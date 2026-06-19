        const canvas = document.getElementById('gameCanvas');
        const ctx = canvas.getContext('2d');
        let width, height;

        // --- CONFIGURATION ---
        const CONFIG = {
	
            shapeTypes: ['circle', 'triangle', 'square'],
            colors: {
                metro: ['#2563EB', '#DC2626', '#4F46E5', '#9333EA', '#0891B2', '#000000'], 
                bus: ['#F59E0B', '#10B981', '#8B5CF6', '#EC4899', '#64748B', '#84CC16', '#14B8A6', '#F43F5E']
            },
            costs: {
                bus: 10,
                vehicle: 15,
                metro: 25,
                interchange: 20,
                bridge: 12,
                tunnel: 12
            },
            metroSpeed: 1.5,
            busSpeed: 0.7,
            metroCapacity: 6,
            busCapacity: 3,
            passengerSpawnRate: 150,
            stationRadius: 10,
            maxBusSegmentLength: 400,
            unconnectedGracePeriod: 3600 // 60 seconds grace period before showing the radial alarm
        };

        // --- STATE VARIABLES ---
        let state = {
            stations: [], lines: [], vehicles: [], particles: [], river: null,
            score: 0, coins: 0, frames: 0,
            isPlaying: false,
            buildMode: 'metro', // 'metro', 'bus', 'vehicle', 'interchange', or a specific Line object
            dragStartStation: null,
            extendData: null,
            hoveredLineData: null,
            draggingSegment: null,
            hoveredTargetStation: null,
            mouseX: 0, mouseY: 0,
            inventory: { metro: 1, bus: 2, vehicle: 0, interchange: 0, bridge: 3, tunnel: 3 },
            nextStationScoreTarget: 5,
            zoom: 1.0, // Dynamic map camera zoom factor
            camX: 0,   // Camera position X
            camY: 0,   // Camera position Y
            
            // Drag and drop vehicle transferring state
            isDraggingExistingVehicle: false,
            draggedVehicle: null,
            draggedVehicleType: null,
            hoveredMetroVehicle: null
        };

        // Enforce a strict overcrowding limit of exactly 6 passengers (normal) or 18 passengers (interchange)
        function getMaxCapacity(station) {
            return station && station.isInterchange ? 18 : 6; 
        }

        let audioContext = null;

        function enableAudio() {
            const AudioCtor = window.AudioContext || window.webkitAudioContext;
            if (!AudioCtor) return;
            if (!audioContext) audioContext = new AudioCtor();
            if (audioContext.state === 'suspended') audioContext.resume();
        }

        function playDing() {
            if (!audioContext || audioContext.state !== 'running') return;
            const now = audioContext.currentTime;
            const oscillator = audioContext.createOscillator();
            const gain = audioContext.createGain();
            oscillator.type = 'sine';
            oscillator.frequency.setValueAtTime(740, now);
            oscillator.frequency.exponentialRampToValueAtTime(1040, now + 0.08);
            gain.gain.setValueAtTime(0.0001, now);
            gain.gain.exponentialRampToValueAtTime(0.12, now + 0.015);
            gain.gain.exponentialRampToValueAtTime(0.0001, now + 0.2);
            oscillator.connect(gain);
            gain.connect(audioContext.destination);
            oscillator.start(now);
            oscillator.stop(now + 0.21);
        }

        function haptic(kind) {
            if (!navigator.vibrate) return;
            const patterns = {
                connect: 35,
                disconnect: [35, 45, 35],
                error: [80, 45, 80]
            };
            navigator.vibrate(patterns[kind]);
        }

        function addScoreParticle(x, y) {
            state.particles.push({ x, y, age: 0, lifetime: 70 });
        }

        function generateRiver() {
            const points = [];
            const phase = Math.random() * Math.PI * 2;
            const amplitude = Math.max(40, width * 0.08);
            const baseX = width * (0.43 + Math.random() * 0.14);
            const startY = -height * 0.5;
            const span = height * 2;
            for (let i = 0; i <= 16; i++) {
                const progress = i / 16;
                points.push({
                    x: baseX + Math.sin(progress * Math.PI * 2.2 + phase) * amplitude + (Math.random() - 0.5) * 12,
                    y: startY + span * progress
                });
            }
            state.river = { points, width: 56 };
        }

        function segmentIntersection(a, b, c, d) {
            const r = { x: b.x - a.x, y: b.y - a.y };
            const s = { x: d.x - c.x, y: d.y - c.y };
            const cross = r.x * s.y - r.y * s.x;
            if (Math.abs(cross) < 0.0001) return null;
            const q = { x: c.x - a.x, y: c.y - a.y };
            const t = (q.x * s.y - q.y * s.x) / cross;
            const u = (q.x * r.y - q.y * r.x) / cross;
            if (t <= 0.015 || t >= 0.985 || u < 0 || u > 1) return null;
            return { x: a.x + t * r.x, y: a.y + t * r.y, angle: Math.atan2(r.y, r.x) };
        }

        function getRiverCrossings(stations) {
            if (!state.river || stations.length < 2) return [];
            const crossings = [];
            for (let i = 0; i < stations.length - 1; i++) {
                const found = [];
                for (let j = 0; j < state.river.points.length - 1; j++) {
                    const hit = segmentIntersection(stations[i], stations[i + 1], state.river.points[j], state.river.points[j + 1]);
                    if (hit && !found.some(p => getDist(p, hit) < 8)) found.push(hit);
                }
                crossings.push(...found);
            }
            return crossings;
        }

        function commitLineStations(line, newStations, isNewLine = false) {
            const oldStations = isNewLine ? [] : [...line.stations];
            const crossingCost = Math.max(0, getRiverCrossings(newStations).length - getRiverCrossings(oldStations).length);
            const crossingResource = line.type === 'metro' ? 'tunnel' : 'bridge';
            if (crossingCost > state.inventory[crossingResource]) {
                haptic('error');
                return false;
            }
            state.inventory[crossingResource] -= crossingCost;
            line.stations = newStations;
            if (!isNewLine) reconcileVehicles(line, oldStations);
            playDing();
            haptic('connect');
            return true;
        }

        // --- STREAMING_CHUNK: Coordinate scale mapping and parallel route segment offsets... ---
        // Maps physical viewport client coordinates into scaled world coordinates
        function screenToWorld(sx, sy) {
            const cx = width / 2;
            const cy = height / 2;
            const z = state.zoom || 1.0;
            return {
                x: (sx - cx) / z + state.camX,
                y: (sy - cy) / z + state.camY
            };
        }

        // Computes the perpendicular offset to draw overlapping parallel lines beautifully side-by-side
        function getSegmentOffset(s1, s2, line, spacing = 9) {
            if (!s1 || !s2) return { x: 0, y: 0 };
            const key = s1.id < s2.id ? s1.id + '_' + s2.id : s2.id + '_' + s1.id;
            
            // Gather all active lines using this segment
            const linesSharing = [];
            state.lines.forEach(l => {
                for (let i = 0; i < l.stations.length - 1; i++) {
                    const st1 = l.stations[i];
                    const st2 = l.stations[i+1];
                    const k = st1.id < st2.id ? st1.id + '_' + st2.id : st2.id + '_' + st1.id;
                    if (k === key) {
                        if (!linesSharing.includes(l)) linesSharing.push(l);
                        break;
                    }
                }
            });

            if (linesSharing.length <= 1) return { x: 0, y: 0 };
            
            // Sort shared lines consistently by color reference
            linesSharing.sort((a, b) => a.color.localeCompare(b.color));
            
            const idx = linesSharing.indexOf(line);
            if (idx === -1) return { x: 0, y: 0 };

            const N = linesSharing.length;
            const offsetDistance = (idx - (N - 1) / 2) * spacing;

            const dx = s2.x - s1.x;
            const dy = s2.y - s1.y;
            const len = Math.sqrt(dx*dx + dy*dy) || 1;
            
            // Calculate perpendicular vector unit components
            const ux = -dy / len;
            const uy = dx / len;

            return {
                x: ux * offsetDistance,
                y: uy * offsetDistance
            };
        }

        // --- STREAMING_CHUNK: Defining Station and Line models... ---
        class Station {
            constructor(x, y, type) {
                this.x = x; this.y = y; this.type = type;
                this.passengers = [];
                this.overcrowdTimer = 0;
                this.id = Math.random().toString(36).substr(2, 9);
                this.unconnectedTime = 0; // Tracks consecutive frames spent unconnected
                this.isInterchange = false; // Tripled capacity upgrade
            }

            draw(ctx, highlightColor = null) {
                const maxCap = getMaxCapacity(this);
                
                // If the passengers meet or exceed the capacity threshold, overcrowding starts
                if (this.passengers.length >= maxCap) {
                    this.overcrowdTimer += 1;
                    ctx.beginPath();
                    // Draw a Mini Metro style circular countdown ring
                    ctx.arc(this.x, this.y, (this.isInterchange ? CONFIG.stationRadius * 1.8 : CONFIG.stationRadius) + 8, -Math.PI / 2, (-Math.PI / 2) + (Math.PI * 2 * (this.overcrowdTimer / 600)));
                    ctx.strokeStyle = 'red';
                    ctx.lineWidth = 4;
                    ctx.stroke();
                    if (this.overcrowdTimer > 600) gameOver();
                } else {
                    // Gradual cooling down when passenger queues drop below overcrowding threshold
                    this.overcrowdTimer = Math.max(0, this.overcrowdTimer - 2);
                }

                // If upgraded to Interchange, draw a bold outer double ring
                if (this.isInterchange) {
                    ctx.beginPath();
                    ctx.arc(this.x, this.y, CONFIG.stationRadius * 1.8, 0, Math.PI * 2);
                    ctx.strokeStyle = '#475569';
                    ctx.lineWidth = 3.5;
                    ctx.stroke();

                    ctx.beginPath();
                    ctx.arc(this.x, this.y, CONFIG.stationRadius * 1.5, 0, Math.PI * 2);
                    ctx.fillStyle = '#f1f5f9';
                    ctx.fill();
                }

                ctx.fillStyle = '#ffffff';
                ctx.strokeStyle = highlightColor ? highlightColor : '#1e293b';
                ctx.lineWidth = highlightColor ? 6 : 4;
                drawShape(ctx, this.x, this.y, this.type, CONFIG.stationRadius);

                ctx.fillStyle = '#1e293b';
                const pSize = 4;
                this.passengers.forEach((p, i) => {
                    const offsetScale = this.isInterchange ? 28 : 20;
                    const px = this.x + offsetScale + (i % 3) * 12;
                    const py = this.y - 10 + Math.floor(i / 3) * 12;
                    drawShape(ctx, px, py, p.target, pSize, true);
                });
            }
        }

        class Line {
            constructor(type, colorIndex) {
                this.type = type;
                this.color = CONFIG.colors[type][colorIndex % CONFIG.colors[type].length];
                this.stations = [];
            }

            draw(ctx, isHovered, dragData = null) {
                if (this.stations.length < 2) return;

                let pts = [];
                pts.push({x: this.stations[0].x, y: this.stations[0].y});
                for (let i = 1; i < this.stations.length; i++) {
                    if (dragData && dragData.line === this && dragData.index === i - 1) {
                        pts.push({x: state.mouseX, y: state.mouseY});
                    }
                    pts.push({x: this.stations[i].x, y: this.stations[i].y});
                }

                const extLen = 22; 
                const lw = this.type === 'metro' ? (isHovered ? 12 : 8) : (isHovered ? 9 : 5);

                if (isHovered && (state.buildMode === 'vehicle' || state.buildMode === 'interchange')) {
                    ctx.strokeStyle = '#4ade80'; 
                    ctx.fillStyle = '#4ade80';
                } else {
                    ctx.strokeStyle = this.color;
                    ctx.fillStyle = this.color;
                }
                
                ctx.lineWidth = lw;
                ctx.lineJoin = 'round';
                ctx.lineCap = 'round';

                if (this.type === 'bus') ctx.setLineDash([10, 10]);
                else ctx.setLineDash([]);

                // Draw each segment individually with its perpendicular side-by-side offset
                for (let i = 0; i < pts.length - 1; i++) {
                    const p1 = pts[i];
                    const p2 = pts[i+1];
                    const s1 = state.stations.find(s => s.x === p1.x && s.y === p1.y);
                    const s2 = state.stations.find(s => s.x === p2.x && s.y === p2.y);
                    
                    const offset = getSegmentOffset(s1, s2, this);

                    let drawStart = { x: p1.x + offset.x, y: p1.y + offset.y };
                    let drawEnd = { x: p2.x + offset.x, y: p2.y + offset.y };

                    if (i === 0) {
                        let dx = p2.x - p1.x;
                        let dy = p2.y - p1.y;
                        let dist = Math.sqrt(dx*dx + dy*dy) || 1;
                        drawStart.x -= (dx/dist) * extLen;
                        drawStart.y -= (dy/dist) * extLen;
                    }
                    if (i === pts.length - 2) {
                        let dx = p2.x - p1.x;
                        let dy = p2.y - p1.y;
                        let dist = Math.sqrt(dx*dx + dy*dy) || 1;
                        drawEnd.x += (dx/dist) * extLen;
                        drawEnd.y += (dy/dist) * extLen;
                    }

                    ctx.beginPath();
                    ctx.moveTo(drawStart.x, drawStart.y);
                    ctx.lineTo(drawEnd.x, drawEnd.y);
                    ctx.stroke();
                }

                ctx.setLineDash([]); // Reset dash for terminals

                // Find terminal offset calculations for end-caps
                const pFirst = pts[0];
                const pSecond = pts[1];
                const sFirst = state.stations.find(s => s.x === pFirst.x && s.y === pFirst.y);
                const sSecond = state.stations.find(s => s.x === pSecond.x && s.y === pSecond.y);
                const firstOffset = getSegmentOffset(sFirst, sSecond, this);
                
                let dxStart = pSecond.x - pFirst.x;
                let dyStart = pSecond.y - pFirst.y;
                let distStart = Math.sqrt(dxStart*dxStart + dyStart*dyStart) || 1;
                let pStartCap = { 
                    x: pFirst.x + firstOffset.x - (dxStart/distStart) * extLen, 
                    y: pFirst.y + firstOffset.y - (dyStart/distStart) * extLen 
                };

                const pLast = pts[pts.length - 1];
                const pPenultimate = pts[pts.length - 2];
                const sLast = state.stations.find(s => s.x === pLast.x && s.y === pLast.y);
                const sPenultimate = state.stations.find(s => s.x === pPenultimate.x && s.y === pPenultimate.y);
                const lastOffset = getSegmentOffset(sPenultimate, sLast, this);

                let dxEnd = pLast.x - pPenultimate.x;
                let dyEnd = pLast.y - pPenultimate.y;
                let distEnd = Math.sqrt(dxEnd*dxEnd + dyEnd*dyEnd) || 1;
                let uxEnd = dxEnd / distEnd;
                let uyEnd = dyEnd / distEnd;
                let pEndCap = { 
                    x: pLast.x + lastOffset.x + uxEnd * extLen, 
                    y: pLast.y + lastOffset.y + uyEnd * extLen 
                };

                // Draw Start Point Cap (Circle)
                ctx.beginPath();
                ctx.arc(pStartCap.x, pStartCap.y, lw * 0.8, 0, Math.PI * 2);
                ctx.fill();

                // Draw End Point Cap (Perpendicular T-Bar)
                let capWidth = lw * 1.3;
                ctx.beginPath();
                ctx.moveTo(pEndCap.x - uyEnd * capWidth, pEndCap.y + uxEnd * capWidth);
                ctx.lineTo(pEndCap.x + uyEnd * capWidth, pEndCap.y - uxEnd * capWidth);
                ctx.stroke();

                if (this.type === 'bus') {
                    let displayCount = this.stations.length;
                    let isExtending = state.dragStartStation && state.buildMode === 'bus' && this.stations[this.stations.length - 1] === state.dragStartStation && state.hoveredTargetStation && !this.stations.includes(state.hoveredTargetStation);
                    let isInserting = dragData && dragData.line === this && state.hoveredTargetStation && !this.stations.includes(state.hoveredTargetStation);
                    
                    if (isExtending || isInserting) displayCount++;
                    if (displayCount > 7) displayCount = 7; 

                    let startX = pEndCap.x + 12;
                    let startY = pEndCap.y + 12;
                    ctx.lineWidth = 1;
                    
                    for (let i = 0; i < 7; i++) {
                        let bx = startX + (i % 4) * 6; 
                        let by = startY + Math.floor(i / 4) * 6; 
                        if (i < displayCount) {
                            ctx.fillStyle = this.color;
                            ctx.fillRect(bx, by, 4, 4); 
                        } else {
                            ctx.strokeStyle = this.color;
                            ctx.strokeRect(bx + 0.5, by + 0.5, 3, 3); 
                        }
                    }
                }
            }
            
            getShapesServed() { return [...new Set(this.stations.map(s => s.type))]; }
        }

        // --- STREAMING_CHUNK: Modeling vehicle and trailing coaches with dynamic station stops... ---
        class Vehicle {
            constructor(line, startIdx = 0) {
                this.line = line;
                this.currentStationIdx = startIdx;
                this.targetStationIdx = startIdx + 1;
                if(this.targetStationIdx >= line.stations.length) this.targetStationIdx = Math.max(0, startIdx - 1);
                
                this.progress = 0;
                this.direction = this.targetStationIdx > this.currentStationIdx ? 1 : -1;
                this.passengers = [];
                this.speed = line.type === 'metro' ? CONFIG.metroSpeed : CONFIG.busSpeed;
                this.capacity = line.type === 'metro' ? CONFIG.metroCapacity : CONFIG.busCapacity;
                this.ghostTrip = null;
                this.boogies = 0; 
                this.posHistory = []; 
                this.stopTimer = 0; // Number of frames to stay stopped at a station for boarding/deboarding
            }

            update() {
                // If currently paused at a station for transfers, tick down timer and remain in place
                if (this.stopTimer > 0) {
                    this.stopTimer--;
                    let s = this.line.stations[this.currentStationIdx];
                    if (s) {
                        const offset = (this.currentStationIdx < this.line.stations.length - 1) 
                            ? getSegmentOffset(s, this.line.stations[this.currentStationIdx+1], this.line) 
                            : {x:0, y:0};
                        this.x = s.x + offset.x;
                        this.y = s.y + offset.y;
                        let nextS = this.line.stations[this.targetStationIdx];
                        if (nextS) {
                            this.angle = Math.atan2(nextS.y - s.y, nextS.x - s.x);
                        }
                        this.posHistory.unshift({ x: this.x, y: this.y, angle: this.angle });
                        if (this.posHistory.length > 200) this.posHistory.pop();
                    }
                    return;
                }

                let start, end;
                if (this.ghostTrip) {
                    start = this.ghostTrip.start;
                    end = this.ghostTrip.end;
                    const dist = Math.sqrt(Math.pow(end.x - start.x, 2) + Math.pow(end.y - start.y, 2)) || 1;
                    this.progress += (this.speed / dist);

                    if (this.progress >= 1) {
                        const transferOccurred = this.arriveAtStation(end);
                        this.progress = 0;
                        this.ghostTrip = null;

                        let idx = this.line.stations.indexOf(end);
                        if (idx !== -1) {
                            this.currentStationIdx = idx;
                            this.targetStationIdx = idx + this.direction;
                            if (this.targetStationIdx < 0 || this.targetStationIdx >= this.line.stations.length) {
                                this.direction *= -1;
                                this.targetStationIdx = this.currentStationIdx + this.direction;
                                if(this.targetStationIdx < 0) {
                                    this.targetStationIdx = 0; this.currentStationIdx = 0; this.direction = 1;
                                    if(this.line.stations.length > 1) this.targetStationIdx = 1;
                                }
                            }
                        } else {
                            let closestIdx = 0;
                            let minDist = Infinity;
                            for (let i = 0; i < this.line.stations.length; i++) {
                                let d = getDist(end, this.line.stations[i]);
                                if (d < minDist) {
                                    minDist = d;
                                    closestIdx = i;
                                }
                            }
                            this.currentStationIdx = closestIdx;
                            this.targetStationIdx = closestIdx + this.direction;
                            if (this.targetStationIdx < 0 || this.targetStationIdx >= this.line.stations.length) {
                                this.direction *= -1;
                                this.targetStationIdx = this.currentStationIdx + this.direction;
                                if(this.targetStationIdx < 0) {
                                     this.targetStationIdx = 0; this.currentStationIdx = 0; this.direction = 1;
                                     if(this.line.stations.length > 1) this.targetStationIdx = 1;
                                }
                            }
                        }

                        // Stop at station if boarding/deboarding occurred
                        if (transferOccurred) {
                            this.stopTimer = 45;
                        }
                    }
                    
                    if (start && end) {
                        const offset = getSegmentOffset(start, end, this.line);
                        this.x = start.x + offset.x + (end.x - start.x) * this.progress;
                        this.y = start.y + offset.y + (end.y - start.y) * this.progress;
                        this.angle = Math.atan2(end.y - start.y, end.x - start.x);
                        this.posHistory.unshift({ x: this.x, y: this.y, angle: this.angle });
                        if (this.posHistory.length > 200) this.posHistory.pop();
                    }
                    return;
                }

                if (this.line.stations.length < 2) return;

                start = this.line.stations[this.currentStationIdx];
                end = this.line.stations[this.targetStationIdx];
                if (!start || !end) {
                    this.currentStationIdx = 0;
                    this.targetStationIdx = 1;
                    return;
                }

                const dist = Math.sqrt(Math.pow(end.x - start.x, 2) + Math.pow(end.y - start.y, 2));
                this.progress += (this.speed / dist);

                if (start && end) {
                    const offset = getSegmentOffset(start, end, this.line);
                    this.x = start.x + offset.x + (end.x - start.x) * this.progress;
                    this.y = start.y + offset.y + (end.y - start.y) * this.progress;
                    this.angle = Math.atan2(end.y - start.y, end.x - start.x);
                    this.posHistory.unshift({ x: this.x, y: this.y, angle: this.angle });
                    if (this.posHistory.length > 200) this.posHistory.pop();
                }

                if (this.progress >= 1) {
                    const transferOccurred = this.arriveAtStation(end);
                    this.progress = 0;
                    this.currentStationIdx = this.targetStationIdx;
                    this.targetStationIdx += this.direction;

                    if (this.targetStationIdx >= this.line.stations.length || this.targetStationIdx < 0) {
                        this.direction *= -1;
                        this.targetStationIdx = this.currentStationIdx + this.direction;
                        if(this.targetStationIdx < 0 || this.targetStationIdx >= this.line.stations.length) {
                             this.targetStationIdx = 0; this.currentStationIdx = 0; this.direction = 1;
                             if(this.line.stations.length > 1) this.targetStationIdx = 1;
                        }
                    }

                    // Pause at station if transfer transaction took place
                    if (transferOccurred) {
                        this.stopTimer = 45;
                    }
                }
            }

            arriveAtStation(station) {
                let transferOccurred = false;

                // 1. Deboard passengers who have reached destination or transfer hub
                for (let i = this.passengers.length - 1; i >= 0; i--) {
                    const p = this.passengers[i];
                    if (station.type === p.target) {
                        this.passengers.splice(i, 1);
                        state.score++;
                        state.coins++;
                        addScoreParticle(station.x, station.y - 18);
                        checkMilestones(); 
                        updateUI();
                        transferOccurred = true;
                        continue;
                    }
                    
                    const lineStations = this.line.stations;
                    const transferStillOnLine = lineStations.some(s => s.id === p.transferStationId);
                    
                    if (station.id === p.transferStationId || !transferStillOnLine) {
                        p.transferStationId = null; 
                        station.passengers.push(this.passengers.splice(i, 1)[0]);
                        transferOccurred = true;
                    }
                }

                // 2. Board passengers waiting at the station who need this line
                for (let i = station.passengers.length - 1; i >= 0; i--) {
                    if (this.passengers.length >= this.capacity) break;
                    
                    const p = station.passengers[i];
                    const path = findShortestPathToType(station, p.target);
                    if (!path || path.length < 2) continue; 
                    
                    const nextStation = path[1];
                    const lineStations = this.line.stations;
                    const idxCurrent = lineStations.indexOf(station);
                    const idxNext = lineStations.indexOf(nextStation);
                    
                    if (idxCurrent !== -1 && idxNext !== -1 && Math.abs(idxCurrent - idxNext) === 1) {
                        let transferIdx = 1;
                        for (let j = 2; j < path.length; j++) {
                            const prev = path[j - 1];
                            const curr = path[j];
                            const pIdx = lineStations.indexOf(prev);
                            const cIdx = lineStations.indexOf(curr);
                            if (pIdx !== -1 && cIdx !== -1 && Math.abs(pIdx - cIdx) === 1) {
                                transferIdx = j; 
                            } else {
                                break; 
                            }
                        }
                        p.transferStationId = path[transferIdx].id;
                        this.passengers.push(station.passengers.splice(i, 1)[0]);
                        transferOccurred = true;
                    }
                }

                return transferOccurred;
            }

            drawBody(ctx, x, y, angle) {
                ctx.save();
                ctx.translate(x, y);
                ctx.rotate(angle); 

                ctx.strokeStyle = '#f8fafc'; 
                ctx.lineWidth = 2.5;

                if (this.line.type === 'metro') {
                    ctx.fillStyle = this.line.color;
                    ctx.beginPath();
                    ctx.roundRect(-20, -7, 40, 14, 7);
                    ctx.fill();
                    ctx.stroke();

                    ctx.fillStyle = '#1e293b'; 
                    ctx.beginPath();
                    ctx.arc(14, 0, 4.5, -Math.PI/2, Math.PI/2);
                    ctx.fill();

                    ctx.fillStyle = '#ffffff';
                    const mainPassengers = this.passengers.slice(0, 6);
                    mainPassengers.forEach((p, i) => {
                        let px = -14 + (i * 5); 
                        let py = 0;
                        ctx.save();
                        ctx.translate(px, py);
                        ctx.rotate(-angle); 
                        drawShape(ctx, 0, 0, p.target, 2, true);
                        ctx.restore();
                    });

                } else {
                    ctx.fillStyle = this.line.color;
                    ctx.beginPath();
                    ctx.roundRect(-12, -8, 24, 16, [3, 8, 8, 3]);
                    ctx.fill();
                    ctx.stroke();

                    ctx.fillStyle = '#1e293b';
                    ctx.beginPath();
                    ctx.roundRect(7, -6, 3, 12, 1);
                    ctx.fill();

                    ctx.fillStyle = '#ffffff';
                    this.passengers.forEach((p, i) => {
                        let px = -6 + (i * 5.5);
                        let py = 0; 
                        ctx.save();
                        ctx.translate(px, py);
                        ctx.rotate(-angle); 
                        drawShape(ctx, 0, 0, p.target, 2, true);
                        ctx.restore();
                    });
                }
                
                ctx.restore();
            }

            draw(ctx) {
                let start, end;
                if (this.ghostTrip) {
                    start = this.ghostTrip.start;
                    end = this.ghostTrip.end;
                    
                    ctx.beginPath();
                    ctx.moveTo(start.x, start.y);
                    ctx.lineTo(end.x, end.y);
                    ctx.strokeStyle = this.line.color + '66'; 
                    ctx.lineWidth = this.line.type === 'metro' ? 8 : 5;
                    ctx.lineJoin = 'round';
                    ctx.lineCap = 'round';
                    if (this.line.type === 'bus') ctx.setLineDash([10, 10]);
                    ctx.stroke();
                    ctx.setLineDash([]);
                } else {
                    if (this.line.stations.length < 2) return;
                    start = this.line.stations[this.currentStationIdx];
                    end = this.line.stations[this.targetStationIdx];
                    if(!start || !end) return;
                }

                // If currently stopped, render directly at station coords (offset handled in update)
                if (this.stopTimer > 0) {
                    this.drawBody(ctx, this.x, this.y, this.angle);
                } else {
                    const offset = getSegmentOffset(start, end, this.line);
                    const x = start.x + offset.x + (end.x - start.x) * this.progress;
                    const y = start.y + offset.y + (end.y - start.y) * this.progress;
                    const angle = Math.atan2(end.y - start.y, end.x - start.x);
                    this.drawBody(ctx, x, y, angle);
                }

                // Render trailing boogies
                const numBoogies = this.boogies || 0;
                const spacing = 26;
                for (let b = 1; b <= numBoogies; b++) {
                    const historyIndex = b * 17; 
                    let p = this.posHistory ? this.posHistory[historyIndex] : null;
                    if (!p) {
                        const startOffset = getSegmentOffset(start, end, this.line);
                        const curX = start.x + startOffset.x + (end.x - start.x) * this.progress;
                        const curY = start.y + startOffset.y + (end.y - start.y) * this.progress;
                        const curAngle = Math.atan2(end.y - start.y, end.x - start.x);
                        p = {
                            x: curX - Math.cos(curAngle) * spacing * b,
                            y: curY - Math.sin(curAngle) * spacing * b,
                            angle: curAngle
                        };
                    }
                    
                    let prevP = b === 1 ? { x: this.x, y: this.y } : (this.posHistory ? this.posHistory[(b-1)*17] : null);
                    if (!prevP) {
                        const startOffset = getSegmentOffset(start, end, this.line);
                        const curX = start.x + startOffset.x + (end.x - start.x) * this.progress;
                        const curY = start.y + startOffset.y + (end.y - start.y) * this.progress;
                        const curAngle = Math.atan2(end.y - start.y, end.x - start.x);
                        prevP = {
                            x: curX - Math.cos(curAngle) * spacing * (b - 1),
                            y: curY - Math.sin(curAngle) * spacing * (b - 1)
                        };
                    }
                    ctx.strokeStyle = '#475569';
                    ctx.lineWidth = 3;
                    ctx.beginPath();
                    ctx.moveTo(prevP.x, prevP.y);
                    ctx.lineTo(p.x, p.y);
                    ctx.stroke();

                    ctx.save();
                    ctx.translate(p.x, p.y);
                    ctx.rotate(p.angle);
                    
                    ctx.strokeStyle = '#f8fafc';
                    ctx.lineWidth = 2.5;
                    ctx.fillStyle = this.line.color;
                    ctx.beginPath();
                    ctx.roundRect(-15, -7, 30, 14, 5);
                    ctx.fill();
                    ctx.stroke();

                    ctx.fillStyle = '#475569';
                    ctx.fillRect(-10, -4, 4, 1.5);
                    ctx.fillRect(-2, -4, 4, 1.5);
                    ctx.fillRect(6, -4, 4, 1.5);
                    ctx.fillRect(-10, 2.5, 4, 1.5);
                    ctx.fillRect(-2, 2.5, 4, 1.5);
                    ctx.fillRect(6, 2.5, 4, 1.5);

                    const passengersInThisCar = this.passengers.slice(6 + (b - 1) * 4, 6 + b * 4);
                    ctx.fillStyle = '#ffffff';
                    passengersInThisCar.forEach((pObj, idx) => {
                        let px = -9 + (idx * 6);
                        let py = 0;
                        ctx.save();
                        ctx.translate(px, py);
                        ctx.rotate(-p.angle);
                        drawShape(ctx, 0, 0, pObj.target, 2, true);
                        ctx.restore();
                    });

                    ctx.restore();
                }
            }
        }

        // --- STREAMING_CHUNK: Shape builders and procedurally spawning logic... ---
        function drawShape(ctx, x, y, type, size, fill = false) {
            ctx.beginPath();
            if (type === 'circle') ctx.arc(x, y, size, 0, Math.PI * 2);
            else if (type === 'square') ctx.rect(x - size, y - size, size * 2, size * 2);
            else if (type === 'triangle') {
                ctx.moveTo(x, y - size); ctx.lineTo(x + size, y + size); ctx.lineTo(x - size, y + size); ctx.closePath();
            }
            if (fill) ctx.fill(); else { ctx.fill(); ctx.stroke(); }
        }

        function resize() {
            const pixelRatio = window.devicePixelRatio || 1;
            width = window.innerWidth; 
            height = window.innerHeight;
            canvas.width = width * pixelRatio; 
            canvas.height = height * pixelRatio;
            
            ctx.setTransform(1, 0, 0, 1, 0, 0);
            ctx.scale(pixelRatio, pixelRatio);
        }

        function checkMilestones() {
            if (state.score >= state.nextStationScoreTarget) {
                spawnStation();
                state.nextStationScoreTarget += 5 + Math.floor(state.stations.length * 1.5);
                
                popInventory('metro');
                popInventory('bus');
            }
        }

        function spawnStation() {
            const padding = 60;
            let r = Math.random();
            let type = 'circle';
            if (state.stations.length === 0) type = 'square';
            else if (r > 0.8) type = 'triangle';
            else if (r > 0.95 && state.stations.filter(s=>s.type==='square').length < 2) type = 'square';

            let x, y, valid = false;
            let attempts = 0;
            while (!valid && attempts < 100) {
                x = padding + Math.random() * (width - padding * 2);
                y = padding + Math.random() * (height - padding * 2);
                if (y < 120 || y > height - 100) continue; 
                
                const clearOfStations = state.stations.every(s => Math.sqrt((s.x-x)**2 + (s.y-y)**2) > 90);
                const clearOfRiver = !state.river || state.river.points.every((point, index, points) => {
                    if (index === points.length - 1) return true;
                    return distToSegmentSquared({ x, y }, point, points[index + 1]) > 2500;
                });
                valid = clearOfStations && clearOfRiver;
                attempts++;
            }
            if(valid) state.stations.push(new Station(x, y, type));
        }

        function spawnPassenger() {
            if (state.stations.length < 2) return;
            const station = state.stations[Math.floor(Math.random() * state.stations.length)];
            let destTypes = [...new Set(state.stations.map(s => s.type))].filter(t => t !== station.type);
            if (destTypes.length === 0) return;
            const dest = destTypes[Math.floor(Math.random() * destTypes.length)];
            station.passengers.push({ target: dest, transferStationId: null });
        }

        // --- BFS GRAPH PATHFINDING ---
        function findShortestPathToType(startStation, targetType) {
            if (startStation.type === targetType) return [startStation];

            let queue = [ [startStation] ];
            let visited = new Set([startStation.id]);

            while (queue.length > 0) {
                let path = queue.shift();
                let curr = path[path.length - 1];

                if (curr.type === targetType) {
                    return path;
                }

                let neighbors = getStationNeighbors(curr);
                for (let nb of neighbors) {
                    if (!visited.has(nb.id)) {
                        visited.add(nb.id);
                        queue.push([...path, nb]);
                    }
                }
            }
            return null;
        }

        function getStationNeighbors(station) {
            let neighbors = new Set();
            state.lines.forEach(line => {
                for (let i = 0; i < line.stations.length; i++) {
                    if (line.stations[i] === station) {
                        if (i > 0) neighbors.add(line.stations[i - 1]);
                        if (i < line.stations.length - 1) neighbors.add(line.stations[i + 1]);
                    }
                }
            });
            return Array.from(neighbors);
        }

        // --- STREAMING_CHUNK: Math, bounds detectors, and grid calculations... ---
        function distToSegmentSquared(p, v, w) {
            let l2 = Math.pow(v.x - w.x, 2) + Math.pow(v.y - w.y, 2);
            if (l2 === 0) return Math.pow(p.x - v.x, 2) + Math.pow(p.y - v.y, 2);
            let t = ((p.x - v.x) * (w.x - v.x) + (p.y - v.y) * (w.y - v.y)) / l2;
            t = Math.max(0, Math.min(1, t));
            return Math.pow(p.x - (v.x + t * (w.x - v.x)), 2) + Math.pow(p.y - (v.y + t * (w.y - v.y)), 2);
        }

        function getHoveredLineSegment(x, y) {
            let closestLine = null;
            let closestIndex = -1;
            let minDistSq = 1200; 
            for (let line of state.lines) {
                if (line.stations.length < 2) continue;
                for (let i = 0; i < line.stations.length - 1; i++) {
                    let dSq = distToSegmentSquared({x, y}, line.stations[i], line.stations[i+1]);
                    if (dSq < minDistSq) {
                        minDistSq = dSq;
                        closestLine = line;
                        closestIndex = i;
                    }
                }
            }
            return { line: closestLine, index: closestIndex };
        }

        function getHoveredStation(x, y) {
            return state.stations.find(s => Math.sqrt((s.x-x)**2 + (s.y-y)**2) < CONFIG.stationRadius * 2.5);
        }

        function getHoveredVehicle(x, y) {
            return state.vehicles.find(v => v.line.type === 'metro' && getDist({ x, y }, v) < 30);
        }

        function getDist(p1, p2) {
            return Math.sqrt(Math.pow(p2.x - p1.x, 2) + Math.pow(p2.y - p1.y, 2));
        }

        function reconcileVehicles(line, oldStations) {
            state.vehicles.forEach(v => {
                if (v.line === line && !v.ghostTrip) {
                    if (v.currentStationIdx >= oldStations.length || v.targetStationIdx >= oldStations.length) return;

                    let s1 = oldStations[v.currentStationIdx];
                    let s2 = oldStations[v.targetStationIdx];

                    let idx1 = line.stations.indexOf(s1);
                    let idx2 = line.stations.indexOf(s2);

                    if (idx1 !== -1 && idx2 !== -1 && Math.abs(idx1 - idx2) === 1) {
                        v.currentStationIdx = idx1;
                        v.targetStationIdx = idx2;
                    } else {
                        v.ghostTrip = { start: s1, end: s2 };
                    }
                }
            });
        }

        // --- STREAMING_CHUNK: Managing side-panel layout, popup badges and inventory UI... ---
        function popInventory(type) {
            if (type === 'bridge' || type === 'tunnel') {
                const el = document.getElementById(type === 'bridge' ? 'bridgeCount' : 'tunnelCount');
                el.classList.add('scale-125');
                setTimeout(() => el.classList.remove('scale-125'), 500);
                return;
            }
            const btnId = type === 'metro' ? 'btnMetro' : type === 'bus' ? 'btnBus' : type === 'interchange' ? 'btnInterchange' : 'btnVehicle';
            const el = document.getElementById(btnId);
            if (el) {
                el.classList.add('scale-110');
                setTimeout(() => {
                    el.classList.remove('scale-110');
                }, 500);

                const pop = document.createElement('div');
                pop.className = 'absolute bg-green-500 text-white font-extrabold text-xs px-2 py-0.5 rounded-full shadow-md float-pop pointer-events-none z-50';
                pop.style.left = `${el.offsetLeft + el.offsetWidth / 2 - 12}px`;
                pop.style.top = `${el.offsetTop - 15}px`;
                pop.innerText = '+1';
                
                const container = document.getElementById('controlsContainer');
                container.appendChild(pop);
                setTimeout(() => pop.remove(), 1000);
            }
        }

        function updateUI() {
            document.getElementById('scoreDisplay').innerText = state.score;
            document.getElementById('coinDisplay').innerText = state.coins;
            document.getElementById('bridgeCount').innerText = state.inventory.bridge;
            document.getElementById('tunnelCount').innerText = state.inventory.tunnel;
            
            const activeMetros = state.lines.filter(l => l.type === 'metro').length;
            const activeBuses = state.lines.filter(l => l.type === 'bus').length;

            document.getElementById('metroCount').innerText = state.inventory.metro;
            document.getElementById('busCount').innerText = state.inventory.bus;
            document.getElementById('vehicleCount').innerText = state.inventory.vehicle;
            document.getElementById('interchangeCount').innerText = state.inventory.interchange;
            
            const btns = { metro: 'btnMetro', vehicle: 'btnVehicle', bus: 'btnBus', interchange: 'btnInterchange' };
            const indicator = document.getElementById('activeIndicatorDot');
            
            for(let key in btns) {
                let el = document.getElementById(btns[key]);
                if (!el) continue;
                if (state.buildMode === key) {
                    el.firstElementChild.className = "w-8 h-8 md:w-10 md:h-10 rounded-full bg-slate-900 text-white flex items-center justify-center shadow-lg border-2 border-slate-700 transform scale-105 transition-all";
                    if (indicator) {
                        indicator.style.top = `${el.offsetTop + (el.offsetHeight / 2)}px`;
                        indicator.style.display = 'block';
                    }
                } else {
                    el.firstElementChild.className = "w-8 h-8 md:w-10 md:h-10 rounded-full bg-slate-100 text-slate-700 flex items-center justify-center shadow-sm hover:bg-slate-200 transition-all";
                }
            }

            const metroLineDots = document.getElementById('metroLineDots');
            const busLineDots = document.getElementById('busLineDots');
            
            if (metroLineDots) {
                metroLineDots.innerHTML = '';
                const activeMetrosList = state.lines.filter(l => l.type === 'metro');
                activeMetrosList.forEach(line => {
                    const dot = document.createElement('div');
                    const isUsed = line.stations.length >= 2;
                    const sizeClass = isUsed ? "w-3.5 h-3.5 md:w-4 md:h-4" : "w-2.5 h-2.5";
                    
                    dot.className = `${sizeClass} rounded-full shadow-md cursor-pointer hover:scale-125 transition-all border border-black/15 select-none touch-none`;
                    dot.style.backgroundColor = line.color;
                    
                    const selectDot = (e) => {
                        e.stopPropagation();
                        e.preventDefault();
                        state.buildMode = line;
                        updateUI();
                    };
                    dot.addEventListener('mousedown', selectDot);
                    dot.addEventListener('touchstart', selectDot, { passive: false });
                    metroLineDots.appendChild(dot);
                });
                for (let i = 0; i < state.inventory.metro; i++) {
                    const dot = document.createElement('div');
                    dot.className = "w-2 h-2 rounded-full bg-slate-300 border border-dashed border-slate-400 opacity-65 select-none";
                    metroLineDots.appendChild(dot);
                }
            }

            if (busLineDots) {
                busLineDots.innerHTML = '';
                const activeBusesList = state.lines.filter(l => l.type === 'bus');
                activeBusesList.forEach(line => {
                    const dot = document.createElement('div');
                    const isUsed = line.stations.length >= 2;
                    const sizeClass = isUsed ? "w-3.5 h-3.5 md:w-4 md:h-4" : "w-2.5 h-2.5";
                    
                    dot.className = `${sizeClass} rounded-full shadow-md cursor-pointer hover:scale-125 transition-all border border-black/15 select-none touch-none`;
                    dot.style.backgroundColor = line.color;
                    
                    const selectDot = (e) => {
                        e.stopPropagation();
                        e.preventDefault();
                        state.buildMode = line;
                        updateUI();
                    };
                    dot.addEventListener('mousedown', selectDot);
                    dot.addEventListener('touchstart', selectDot, { passive: false });
                    busLineDots.appendChild(dot);
                });
                for (let i = 0; i < state.inventory.bus; i++) {
                    const dot = document.createElement('div');
                    dot.className = "w-2 h-2 rounded-full bg-slate-300 border border-dashed border-slate-400 opacity-65 select-none";
                    busLineDots.appendChild(dot);
                }
            }

            const updateShopBtn = (id, cost) => {
                const btn = document.getElementById(id);
                if (state.coins >= cost) {
                    btn.classList.remove('opacity-50', 'cursor-not-allowed');
                } else {
                    btn.classList.add('opacity-50', 'cursor-not-allowed');
                }
            };
            updateShopBtn('buyBusBtn', CONFIG.costs.bus);
            updateShopBtn('buyMetroBtn', CONFIG.costs.metro);
            updateShopBtn('buyVehicleBtn', CONFIG.costs.vehicle);
            updateShopBtn('buyInterchangeBtn', CONFIG.costs.interchange);
            updateShopBtn('buyBridgeBtn', CONFIG.costs.bridge);
            updateShopBtn('buyTunnelBtn', CONFIG.costs.tunnel);

            const shopFloating = document.getElementById('btnShopFloating');
            if (state.coins >= CONFIG.costs.bus) {
                shopFloating.classList.add('pulse-available');
            } else {
                shopFloating.classList.remove('pulse-available');
            }
        }

        window.buy = (item) => {
            if (state.coins >= CONFIG.costs[item]) {
                state.coins -= CONFIG.costs[item];
                state.inventory[item]++;
                popInventory(item);
                updateUI();
            }
        };

        window.toggleShop = () => {
            const modal = document.getElementById('shopModal');
            modal.classList.toggle('hidden');
        };

        window.setBuildMode = (mode) => {
            state.buildMode = mode;
            updateUI();
        };

        // --- STREAMING_CHUNK: Touch interface fallbacks and gesture mappings... ---
        function getCoords(e) {
            if (e.touches && e.touches.length > 0) {
                return { x: e.touches[0].clientX, y: e.touches[0].clientY };
            }
            if (e.changedTouches && e.changedTouches.length > 0) {
                return { x: e.changedTouches[0].clientX, y: e.changedTouches[0].clientY };
            }
            return { x: e.clientX, y: e.clientY };
        }

        function handleDoubleAction(cx, cy) {
            const worldCoords = screenToWorld(cx, cy);
            const hovered = getHoveredLineSegment(worldCoords.x, worldCoords.y);
            if (hovered.line) {
                const line = hovered.line;
                const idx = hovered.index;

                if (idx > 0) { 
                    let oldStations = [...line.stations];
                    line.stations = line.stations.slice(0, idx + 1);
                    reconcileVehicles(line, oldStations);
                    haptic('disconnect');
                }
                
                state.hoveredLineData = null;
                state.draggingSegment = null;
                updateUI();
            }
        }

        canvas.addEventListener('dblclick', (e) => {
            if (!state.isPlaying) return;
            handleDoubleAction(e.clientX, e.clientY);
        });

        let lastTap = 0;

        function handleStart(cx, cy) {
            document.getElementById('shopModal').classList.add('hidden');

            const clickedVehicle = state.vehicles.find(v => !v.ghostTrip && getDist({x: cx, y: cy}, v) < 25);
            if (clickedVehicle) {
                state.draggedVehicle = clickedVehicle;
                state.draggedVehicleType = clickedVehicle.line.type;
                state.isDraggingExistingVehicle = true;
                return;
            }

            const s = getHoveredStation(cx, cy);

            if (state.buildMode === 'vehicle') {
                const hVehicle = getHoveredVehicle(cx, cy);
                if (hVehicle && state.inventory.vehicle > 0) {
                    hVehicle.boogies = (hVehicle.boogies || 0) + 1;
                    hVehicle.capacity += 4; 
                    state.inventory.vehicle--;
                    popInventory('vehicle');
                    updateUI();
                } else if (state.hoveredLineData?.line && state.inventory.vehicle > 0) {
                    state.vehicles.push(new Vehicle(state.hoveredLineData.line, Math.floor(state.hoveredLineData.line.stations.length / 2)));
                    state.inventory.vehicle--;
                    updateUI();
                }
                return;
            }

            if (state.buildMode === 'interchange') {
                if (s && !s.isInterchange && state.inventory.interchange > 0) {
                    s.isInterchange = true;
                    state.inventory.interchange--;
                    popInventory('interchange');
                    updateUI();
                }
                return;
            }

            if (s) {
                let extendLine = null;
                let extendDir = null;

                let targetType = typeof state.buildMode === 'string' ? state.buildMode : state.buildMode.type;

                for (let line of state.lines) {
                    if (line.type === targetType) {
                        if (typeof state.buildMode === 'object' && state.buildMode !== line) continue;

                        if (line.stations[line.stations.length - 1] === s) {
                            extendLine = line; extendDir = 'end'; break;
                        } else if (line.stations[0] === s) {
                            extendLine = line; extendDir = 'start'; break;
                        }
                    }
                }

                if (extendLine) {
                    state.dragStartStation = s;
                    state.extendData = { line: extendLine, dir: extendDir };
                    return;
                }

                let lineToDetach = null;
                let stationIdx = -1;

                for (let line of state.lines) {
                    if (line.type === targetType) {
                        if (typeof state.buildMode === 'object' && state.buildMode !== line) continue;
                        const idx = line.stations.indexOf(s);
                        if (idx > 0 && idx < line.stations.length - 1) {
                            lineToDetach = line;
                            stationIdx = idx;
                            break;
                        }
                    }
                }

                if (lineToDetach) {
                    let oldStations = [...lineToDetach.stations];
                    lineToDetach.stations.splice(stationIdx, 1);
                    state.draggingSegment = { line: lineToDetach, index: stationIdx - 1 };
                    state.dragStartStation = null;
                    state.extendData = null;
                    reconcileVehicles(lineToDetach, oldStations);
                    haptic('disconnect');
                } else {
                    state.dragStartStation = s;
                    state.extendData = null;
                }
            } else {
                const hovered = getHoveredLineSegment(cx, cy);
                if (hovered.line) {
                    state.draggingSegment = hovered;
                    state.extendData = null;
                }
            }
        }

        function handleMove(cx, cy) {
            state.mouseX = cx; 
            state.mouseY = cy;
            state.hoveredLineData = getHoveredLineSegment(state.mouseX, state.mouseY);
            state.hoveredTargetStation = getHoveredStation(state.mouseX, state.mouseY);
            
            if (state.draggedVehicleType === 'boogie') {
                state.hoveredMetroVehicle = getHoveredVehicle(state.mouseX, state.mouseY);
            } else {
                state.hoveredMetroVehicle = null;
            }
        }

        function handleEnd(cx, cy) {
            if (state.isDraggingExistingVehicle) {
                const hoverLine = state.hoveredLineData?.line;
                if (hoverLine && hoverLine.type === state.draggedVehicleType && hoverLine !== state.draggedVehicle.line) {
                    state.draggedVehicle.line = hoverLine;
                    state.draggedVehicle.currentStationIdx = 0;
                    state.draggedVehicle.targetStationIdx = Math.min(1, hoverLine.stations.length - 1);
                    state.draggedVehicle.progress = 0;
                    state.draggedVehicle.direction = 1;
                    state.draggedVehicle.ghostTrip = null;
                    state.draggedVehicle.posHistory = []; 
                }
                state.isDraggingExistingVehicle = false;
                state.draggedVehicle = null;
                state.draggedVehicleType = null;
                updateUI();
                return;
            }

            const endStation = getHoveredStation(cx, cy);

            // Drag-drop support for Interchange
            if (state.draggedVehicleType === 'interchange') {
                if (endStation && !endStation.isInterchange && state.inventory.interchange > 0) {
                    endStation.isInterchange = true;
                    state.inventory.interchange--;
                    popInventory('interchange');
                }
                state.draggedVehicleType = null;
                updateUI();
                return;
            }
            
            if (state.draggingSegment) {
                if (endStation) {
                    const line = state.draggingSegment.line;
                    const idx = state.draggingSegment.index;
                    let oldStations = [...line.stations];
                    const existingIdx = line.stations.indexOf(endStation);
                    
                    if (existingIdx === -1) {
                        let isValidInsert = true;
                        if (line.type === 'bus') {
                            let d1 = getDist(line.stations[idx], endStation);
                            let d2 = getDist(endStation, line.stations[idx+1]);
                            if (line.stations.length >= 7 || d1 > CONFIG.maxBusSegmentLength || d2 > CONFIG.maxBusSegmentLength) {
                                isValidInsert = false;
                            }
                        }
                        if (isValidInsert) {
                            if (line.stations[idx] !== endStation && line.stations[idx+1] !== endStation) {
                                const newStations = [...line.stations];
                                newStations.splice(idx + 1, 0, endStation);
                                commitLineStations(line, newStations);
                            }
                        }
                    } else {
                        if (line.stations.length > 2) {
                            line.stations.splice(existingIdx, 1);
                            reconcileVehicles(line, oldStations);
                            haptic('disconnect');
                        } else {
                            const vehiclesOnLine = state.vehicles.filter(v => v.line === line).length;
                            state.inventory[line.type]++;
                            state.inventory.vehicle += Math.max(0, vehiclesOnLine - 1);
                            state.lines = state.lines.filter(l => l !== line);
                            state.vehicles = state.vehicles.filter(v => v.line !== line);
                            haptic('disconnect');
                            
                            popInventory(line.type);
                        }
                    }
                }
                state.draggingSegment = null;
                updateUI();
                return;
            }

            let buildType = typeof state.buildMode === 'string' ? state.buildMode : state.buildMode.type;

            if (state.dragStartStation && endStation && endStation !== state.dragStartStation && (buildType === 'metro' || buildType === 'bus')) {
                if (state.extendData) {
                    let lineToExtend = state.extendData.line;
                    let extendDir = state.extendData.dir;
                    let oldStations = [...lineToExtend.stations];

                    if (extendDir === 'end') {
                        if (lineToExtend.stations.length >= 2 && lineToExtend.stations[lineToExtend.stations.length - 2] === endStation) {
                            lineToExtend.stations.pop();
                            reconcileVehicles(lineToExtend, oldStations);
                            haptic('disconnect');
                        } else if (!lineToExtend.stations.includes(endStation)) {
                            let dist = getDist(lineToExtend.stations[lineToExtend.stations.length - 1], endStation);
                            if (lineToExtend.type !== 'bus' || (lineToExtend.stations.length < 7 && dist <= CONFIG.maxBusSegmentLength)) {
                                commitLineStations(lineToExtend, [...lineToExtend.stations, endStation]);
                            }
                        }
                    } else if (extendDir === 'start') {
                        if (lineToExtend.stations.length >= 2 && lineToExtend.stations[1] === endStation) {
                            lineToExtend.stations.shift();
                            reconcileVehicles(lineToExtend, oldStations);
                            haptic('disconnect');
                        } else if (!lineToExtend.stations.includes(endStation)) {
                            let dist = getDist(lineToExtend.stations[0], endStation);
                            if (lineToExtend.type !== 'bus' || (lineToExtend.stations.length < 7 && dist <= CONFIG.maxBusSegmentLength)) {
                                commitLineStations(lineToExtend, [endStation, ...lineToExtend.stations]);
                            }
                        }
                    }
                } else if (state.inventory[buildType] > 0) {
                    let dist = getDist(state.dragStartStation, endStation);
                    if (buildType !== 'bus' || dist <= CONFIG.maxBusSegmentLength) {
                        const colorIndex = state.lines.filter(l=>l.type===buildType).length;
                        const newLine = new Line(buildType, colorIndex);
                        if (commitLineStations(newLine, [state.dragStartStation, endStation], true)) {
                            state.lines.push(newLine);
                            state.vehicles.push(new Vehicle(newLine));
                            state.inventory[buildType]--;
                            updateUI();
                        }
                    }
                }
            }
            state.dragStartStation = null;
            state.extendData = null;
            updateUI();
        }

        // --- STREAMING_CHUNK: Binding gesture listeners to the viewport... ---
        canvas.addEventListener('mousedown', (e) => {
            e.preventDefault();
            if (!state.isPlaying) return;
            const worldCoords = screenToWorld(e.clientX, e.clientY);
            handleStart(worldCoords.x, worldCoords.y);
        });

        canvas.addEventListener('mousemove', (e) => {
            e.preventDefault();
            const worldCoords = screenToWorld(e.clientX, e.clientY);
            handleMove(worldCoords.x, worldCoords.y);
        });

        canvas.addEventListener('mouseup', (e) => {
            e.preventDefault();
            if (!state.isPlaying) return;
            const worldCoords = screenToWorld(e.clientX, e.clientY);
            handleEnd(worldCoords.x, worldCoords.y);
        });

        canvas.addEventListener('touchstart', (e) => {
            e.preventDefault();
            if (!state.isPlaying) return;
            const now = Date.now();
            const rawCoords = getCoords(e);
            const worldCoords = screenToWorld(rawCoords.x, rawCoords.y);
            
            state.mouseX = worldCoords.x;
            state.mouseY = worldCoords.y;
            
            if (now - lastTap < 300) {
                handleDoubleAction(rawCoords.x, rawCoords.y);
            } else {
                handleStart(worldCoords.x, worldCoords.y);
            }
            lastTap = now;
        }, { passive: false });

        canvas.addEventListener('touchmove', (e) => {
            e.preventDefault();
            const rawCoords = getCoords(e);
            const worldCoords = screenToWorld(rawCoords.x, rawCoords.y);
            handleMove(worldCoords.x, worldCoords.y);
        }, { passive: false });

        canvas.addEventListener('touchend', (e) => {
            e.preventDefault();
            if (!state.isPlaying) return;
            handleEnd(state.mouseX, state.mouseY);
        }, { passive: false });

        // --- STREAMING_CHUNK: Setting up sidebar dragging upgrades... ---
        function registerSidebarDraggers() {
            const dragVehicle = (e, type) => {
                if (!state.isPlaying) return;
                const rawCoords = getCoords(e);
                const worldCoords = screenToWorld(rawCoords.x, rawCoords.y);
                state.mouseX = worldCoords.x;
                state.mouseY = worldCoords.y;
                state.draggedVehicleType = type;

                if (type === 'metro') setBuildMode('metro');
                else if (type === 'bus') setBuildMode('bus');
                else if (type === 'boogie') setBuildMode('vehicle');
                else if (type === 'interchange') setBuildMode('interchange');
            };

            const handleVehicleDrop = (e) => {
                if (state.draggedVehicleType && !state.isDraggingExistingVehicle) {
                    const cx = state.mouseX;
                    const cy = state.mouseY;
                    
                    if (state.draggedVehicleType === 'boogie') {
                        const hVehicle = getHoveredVehicle(cx, cy);
                        if (hVehicle && state.inventory.vehicle > 0) {
                            hVehicle.boogies = (hVehicle.boogies || 0) + 1;
                            hVehicle.capacity += 4; 
                            state.inventory.vehicle--;
                            popInventory('vehicle');
                        }
                        state.draggedVehicleType = null;
                        updateUI();
                        return;
                    }

                    if (state.draggedVehicleType === 'interchange') {
                        const hoverS = getHoveredStation(cx, cy);
                        if (hoverS && !hoverS.isInterchange && state.inventory.interchange > 0) {
                            hoverS.isInterchange = true;
                            state.inventory.interchange--;
                            popInventory('interchange');
                        }
                        state.draggedVehicleType = null;
                        updateUI();
                        return;
                    }

                    const hovered = getHoveredLineSegment(cx, cy);

                    if (hovered.line && hovered.line.type === state.draggedVehicleType) {
                        let hasInventory = false;
                        if (state.inventory.vehicle > 0) {
                            state.vehicles.push(new Vehicle(hovered.line, Math.floor(hovered.line.stations.length / 2)));
                            state.inventory.vehicle--;
                            popInventory('vehicle');
                            hasInventory = true;
                        } else if (state.draggedVehicleType === 'metro' && state.inventory.metro > 0) {
                            state.vehicles.push(new Vehicle(hovered.line, Math.floor(hovered.line.stations.length / 2)));
                            state.inventory.metro--;
                            hasInventory = true;
                        } else if (state.draggedVehicleType === 'bus' && state.inventory.bus > 0) {
                            state.vehicles.push(new Vehicle(hovered.line, Math.floor(hovered.line.stations.length / 2)));
                            state.inventory.bus--;
                            hasInventory = true;
                        }
                        if (hasInventory) updateUI();
                    }
                    state.draggedVehicleType = null;
                }
            };

            // Custom Carrier Icon Side-Profile (Screenshot 2.42.51) Injection
            const customCarrierIcon = `
                <svg class="w-8 h-8 md:w-10 md:h-10 text-indigo-600" viewBox="0 0 48 24" fill="currentColor">
                    <circle cx="8" cy="18" r="1.8" fill="#1e293b" />
                    <circle cx="14" cy="18" r="1.8" fill="#1e293b" />
                    <circle cx="34" cy="18" r="1.8" fill="#1e293b" />
                    <circle cx="40" cy="18" r="1.8" fill="#1e293b" />
                    <path d="M2 15h12V6H6.5A4.5 4.5 0 0 0 2 10.5V15z" fill="#334155" />
                    <path d="M3.5 12h3V8H6.5a2.5 2.5 0 0 0-2.5 2.5V12z" fill="#f8fafc" />
                    <rect x="8" y="8" width="4" height="4" rx="0.5" fill="#f8fafc" />
                    <rect x="15" y="5" width="4" height="11" rx="0.5" fill="#1e293b" />
                    <rect x="16.5" y="6" width="1" height="9" fill="#f8fafc" />
                    <path d="M20 15h26V6H20v9z" fill="#334155" />
                    <rect x="22" y="8" width="5" height="4" rx="0.5" fill="#f8fafc" />
                    <rect x="29" y="8" width="5" height="4" rx="0.5" fill="#f8fafc" />
                    <rect x="36" y="8" width="5" height="4" rx="0.5" fill="#f8fafc" />
                    <rect x="43" y="8" width="2" height="4" fill="#f8fafc" />
                </svg>
            `;
            document.getElementById('btnVehicle').firstElementChild.innerHTML = customCarrierIcon;

            document.getElementById('btnMetro').addEventListener('mousedown', (e) => dragVehicle(e, 'metro'));
            document.getElementById('btnBus').addEventListener('mousedown', (e) => dragVehicle(e, 'bus'));
            document.getElementById('btnVehicle').addEventListener('mousedown', (e) => dragVehicle(e, 'boogie'));
            document.getElementById('btnInterchange').addEventListener('mousedown', (e) => dragVehicle(e, 'interchange'));
            
            document.getElementById('btnMetro').addEventListener('touchstart', (e) => { e.preventDefault(); dragVehicle(e, 'metro'); }, { passive: false });
            document.getElementById('btnBus').addEventListener('touchstart', (e) => { e.preventDefault(); dragVehicle(e, 'bus'); }, { passive: false });
            document.getElementById('btnVehicle').addEventListener('touchstart', (e) => { e.preventDefault(); dragVehicle(e, 'boogie'); }, { passive: false });
            document.getElementById('btnInterchange').addEventListener('touchstart', (e) => { e.preventDefault(); dragVehicle(e, 'interchange'); }, { passive: false });

            window.addEventListener('mouseup', handleVehicleDrop);
            window.addEventListener('touchend', handleVehicleDrop);

            window.addEventListener('mousemove', (e) => {
                if (state.draggedVehicleType && !state.isDraggingExistingVehicle) {
                    const worldCoords = screenToWorld(e.clientX, e.clientY);
                    state.mouseX = worldCoords.x;
                    state.mouseY = worldCoords.y;
                }
            });
            window.addEventListener('touchmove', (e) => {
                if (state.draggedVehicleType && !state.isDraggingExistingVehicle) {
                    const rawCoords = getCoords(e);
                    const worldCoords = screenToWorld(rawCoords.x, rawCoords.y);
                    state.mouseX = worldCoords.x;
                    state.mouseY = worldCoords.y;
                }
            }, { passive: false });
        }

        window.clearLines = () => {
            let metrosRefund = state.lines.filter(l=>l.type==='metro').length;
            let busesRefund = state.lines.filter(l=>l.type==='bus').length;
            let extraVehiclesRefund = Math.max(0, state.vehicles.length - state.lines.length);

            state.lines = []; 
            state.vehicles = [];
            
            state.inventory.metro += metrosRefund;
            state.inventory.bus += busesRefund;
            state.inventory.vehicle += extraVehiclesRefund;

            if (metrosRefund > 0) popInventory('metro');
            if (busesRefund > 0) popInventory('bus');
            if (extraVehiclesRefund > 0) popInventory('vehicle');

            state.extendData = null;
            if (metrosRefund + busesRefund > 0) haptic('disconnect');
            updateUI();
        };

        // --- STREAMING_CHUNK: Orchestrating the core update and game loops... ---
        window.startGame = () => {
            enableAudio();
            state = {
                stations: [], lines: [], vehicles: [], particles: [], river: null,
                score: 0, coins: 0, frames: 0, isPlaying: true,
                buildMode: 'bus', dragStartStation: null, extendData: null, hoveredLineData: null, draggingSegment: null,
                mouseX: 0, mouseY: 0,
                inventory: { metro: 1, bus: 2, vehicle: 0, interchange: 0, bridge: 3, tunnel: 3 },
                nextStationScoreTarget: 5,
                zoom: 1.0,
                camX: width / 2 || 0,
                camY: height / 2 || 0,
                isDraggingExistingVehicle: false,
                draggedVehicle: null,
                draggedVehicleType: null,
                hoveredMetroVehicle: null
            };
            
            document.getElementById('gameOverScreen').classList.add('hidden');
            document.getElementById('startMenu').classList.add('hidden');
            generateRiver();
            updateUI();
            
            spawnStation(); spawnStation(); spawnStation();
            requestAnimationFrame(gameLoop);
        };

        function gameOver() {
            state.isPlaying = false;
            document.getElementById('finalScore').innerText = state.score;
            document.getElementById('gameOverScreen').classList.remove('hidden');
        }

        function update() {
            state.frames++;
            let currentPassRate = Math.max(30, CONFIG.passengerSpawnRate - (state.stations.length * 6));
            if (state.frames % currentPassRate === 0) spawnPassenger();
            state.vehicles.forEach(v => v.update());
            state.particles.forEach(p => p.age++);
            state.particles = state.particles.filter(p => p.age < p.lifetime);

            // Track how long stations remain unconnected
            state.stations.forEach(s => {
                const isStationConnected = state.lines.some(l => l.stations.includes(s));
                if (!isStationConnected) {
                    s.unconnectedTime++;
                } else {
                    s.unconnectedTime = 0; // Reset as soon as connected
                }
            });

            // True Mini Metro camera zooming & centering:
            if (state.stations.length > 0) {
                let minX = Infinity, maxX = -Infinity;
                let minY = Infinity, maxY = -Infinity;
                
                state.stations.forEach(s => {
                    if (s.x < minX) minX = s.x;
                    if (s.x > maxX) maxX = s.x;
                    if (s.y < minY) minY = s.y;
                    if (s.y > maxY) maxY = s.y;
                });
                
                const padding = 160; 
                const spanX = Math.max(120, maxX - minX);
                const spanY = Math.max(120, maxY - minY);
                
                const targetCamX = (minX + maxX) / 2;
                const targetCamY = (minY + maxY) / 2;
                
                // Lerp camera position coordinates
                state.camX = state.camX || targetCamX;
                state.camY = state.camY || targetCamY;
                state.camX += (targetCamX - state.camX) * 0.05;
                state.camY += (targetCamY - state.camY) * 0.05;
                
                // Determine targeted zoom factor to pack all outer nodes inside safe bounds
                const zoomX = (width - padding) / spanX;
                const zoomY = (height - padding) / spanY;
                let targetZoom = Math.min(zoomX, zoomY);
                
                // Restrict extreme zooms
                targetZoom = Math.min(1.0, Math.max(0.4, targetZoom));
                
                state.zoom = state.zoom || 1.0;
                state.zoom += (targetZoom - state.zoom) * 0.05;
            } else {
                state.camX = width / 2;
                state.camY = height / 2;
                state.zoom = 1.0;
            }
        }

        function drawRiver() {
            if (!state.river) return;
            const points = state.river.points;
            ctx.save();
            ctx.lineJoin = 'round';
            ctx.lineCap = 'round';

            ctx.beginPath();
            ctx.moveTo(points[0].x, points[0].y);
            for (let i = 1; i < points.length; i++) ctx.lineTo(points[i].x, points[i].y);
            ctx.strokeStyle = '#b3def5';
            ctx.lineWidth = state.river.width;
            ctx.stroke();
            ctx.restore();
        }

        function drawCrossingTreatments() {
            if (!state.river) return;
            const crossings = [];
            state.lines.forEach(line => {
                getRiverCrossings(line.stations).forEach(hit => crossings.push({ line, hit }));
            });

            // First erase only the part of each route that passes through the water.
            crossings.forEach(({ line, hit }) => {
                const halfLength = state.river.width / 2 + 5;
                const dx = Math.cos(hit.angle) * halfLength;
                const dy = Math.sin(hit.angle) * halfLength;
                ctx.save();
                ctx.beginPath();
                ctx.moveTo(hit.x - dx, hit.y - dy);
                ctx.lineTo(hit.x + dx, hit.y + dy);
                ctx.strokeStyle = '#b3def5';
                ctx.lineWidth = line.type === 'metro' ? 12 : 9;
                ctx.lineCap = 'butt';
                ctx.stroke();
                ctx.restore();
            });

            crossings.forEach(({ line, hit }) => {
                const halfLength = state.river.width / 2 + 6;
                const dx = Math.cos(hit.angle) * halfLength;
                const dy = Math.sin(hit.angle) * halfLength;
                ctx.save();
                ctx.lineCap = 'butt';

                // Both bridge and tunnel route sections become dotted over the river.
                ctx.beginPath();
                ctx.moveTo(hit.x - dx, hit.y - dy);
                ctx.lineTo(hit.x + dx, hit.y + dy);
                ctx.strokeStyle = line.color;
                ctx.lineWidth = line.type === 'metro' ? 7 : 5;
                ctx.setLineDash([6, 6]);
                ctx.stroke();
                ctx.setLineDash([]);

                // Bus bridges get short rails on both sides of the dotted route gap.
                if (line.type === 'bus') {
                    const nx = -Math.sin(hit.angle) * 7;
                    const ny = Math.cos(hit.angle) * 7;
                    ctx.strokeStyle = line.color;
                    ctx.lineWidth = 2;
                    [-1, 1].forEach(side => {
                        ctx.beginPath();
                        ctx.moveTo(hit.x - dx + nx * side, hit.y - dy + ny * side);
                        ctx.lineTo(hit.x + dx + nx * side, hit.y + dy + ny * side);
                        ctx.stroke();
                    });
                }
                ctx.restore();
            });
        }

        function drawParticles() {
            state.particles.forEach(p => {
                const progress = p.age / p.lifetime;
                ctx.save();
                ctx.globalAlpha = Math.max(0, 1 - progress);
                ctx.translate(p.x, p.y - progress * 42);
                ctx.fillStyle = '#16a34a';
                ctx.strokeStyle = '#ffffff';
                ctx.lineWidth = 4;
                ctx.font = '900 18px Segoe UI, sans-serif';
                ctx.textAlign = 'center';
                ctx.strokeText('+1', 0, 0);
                ctx.fillText('+1', 0, 0);
                ctx.restore();
            });
        }

        // --- STREAMING_CHUNK: Canvas rendering and layer sequencing... ---
        function draw() {
            ctx.clearRect(0, 0, width, height);

            ctx.save();
            
            // Apply Camera Center-Zoom transformation matrix
            ctx.translate(width / 2, height / 2);
            ctx.scale(state.zoom, state.zoom);
            ctx.translate(-state.camX, -state.camY);

            // Draw Background Grid
            ctx.strokeStyle = '#e2e8f0'; ctx.lineWidth = 1;
            for(let i=0; i<width*3; i+=40) { ctx.beginPath(); ctx.moveTo(i - width, -height); ctx.lineTo(i - width, height*2); ctx.stroke(); }
            for(let i=0; i<height*3; i+=40) { ctx.beginPath(); ctx.moveTo(-width, i - height); ctx.lineTo(width*2, i - height); ctx.stroke(); }

            drawRiver();

            // 1. Draw Active Track Lines (First layer)
            state.lines.forEach(l => l.draw(ctx, state.hoveredLineData?.line === l, state.draggingSegment));
            drawCrossingTreatments();

            let activeDragColor = null;

            // 2. Draw dragging/routing preview indicators
            if (state.dragStartStation && state.buildMode !== 'vehicle' && state.buildMode !== 'interchange' && !state.draggingSegment) {
                ctx.beginPath();
                ctx.moveTo(state.dragStartStation.x, state.dragStartStation.y);
                
                let extendLine = state.extendData ? state.extendData.line : null;
                let dragX = state.mouseX;
                let dragY = state.mouseY;

                let buildType = typeof state.buildMode === 'string' ? state.buildMode : state.buildMode.type;

                let isBusLineMaxedOut = false;
                if (buildType === 'bus') {
                    let maxAllowedDist = CONFIG.maxBusSegmentLength;
                    let dx = state.mouseX - state.dragStartStation.x;
                    let dy = state.mouseY - state.dragStartStation.y;
                    let dist = Math.sqrt(dx * dx + dy * dy);
                    
                    if (dist > maxAllowedDist && dist > 0) {
                        dragX = state.dragStartStation.x + (dx / dist) * maxAllowedDist;
                        dragY = state.dragStartStation.y + (dy / dist) * maxAllowedDist;
                        isBusLineMaxedOut = true;
                    }
                }
                
                ctx.lineTo(dragX, dragY);
                
                if (extendLine) {
                    if (extendLine.type === 'bus' && extendLine.stations.length >= 7) {
                        activeDragColor = '#ef4444'; 
                    } else {
                        activeDragColor = extendLine.color;
                    }
                } else {
                    const colorIndex = state.lines.filter(l=>l.type===buildType).length;
                    activeDragColor = CONFIG.colors[buildType][colorIndex % CONFIG.colors[buildType].length];
                }
                
                ctx.strokeStyle = activeDragColor + '88'; 
                ctx.lineWidth = buildType === 'metro' ? 8 : 5;
                if (buildType === 'bus') ctx.setLineDash([10, 10]);
                ctx.stroke(); ctx.setLineDash([]);
                
                if (buildType === 'bus') {
                    let displayCount = extendLine ? extendLine.stations.length : 1;
                    let isExtending = state.dragStartStation && buildType === 'bus' && extendLine && extendLine.stations[extendLine.stations.length - 1] === state.dragStartStation && state.hoveredTargetStation && !extendLine.stations.includes(state.hoveredTargetStation);
                    if (isExtending) displayCount++;
                    if (displayCount > 7) displayCount = 7; 

                    let startX = dragX + 12;
                    let startY = dragY + 12;
                    ctx.lineWidth = 1;
                    for (let i = 0; i < 7; i++) {
                        let bx = startX + (i % 4) * 6; 
                        let by = startY + Math.floor(i / 4) * 6; 
                        if (i < displayCount) {
                            ctx.fillStyle = activeDragColor;
                            ctx.fillRect(bx, by, 4, 4);
                        } else {
                            ctx.strokeStyle = activeDragColor;
                            ctx.strokeRect(bx + 0.5, by + 0.5, 3, 3);
                        }
                    }
                }

                if (isBusLineMaxedOut) {
                    ctx.beginPath();
                    ctx.arc(dragX, dragY, 10, 0, Math.PI * 2);
                    ctx.fillStyle = '#ef4444'; 
                    ctx.fill();
                    
                    ctx.strokeStyle = '#ffffff';
                    ctx.lineWidth = 3;
                    ctx.lineCap = 'round';
                    ctx.beginPath();
                    ctx.moveTo(dragX - 4, dragY - 4);
                    ctx.lineTo(dragX + 4, dragY + 4);
                    ctx.moveTo(dragX + 4, dragY - 4);
                    ctx.lineTo(dragX - 4, dragY + 4);
                    ctx.stroke();
                }

            } else if (state.draggingSegment) {
                const line = state.draggingSegment.line;
                let isInvalid = false;
                if (line.type === 'bus' && state.hoveredTargetStation && !line.stations.includes(state.hoveredTargetStation)) {
                    let d1 = getDist(line.stations[state.draggingSegment.index], state.hoveredTargetStation);
                    let d2 = getDist(state.hoveredTargetStation, line.stations[state.draggingSegment.index + 1]);
                    if (line.stations.length >= 7 || d1 > CONFIG.maxBusSegmentLength || d2 > CONFIG.maxBusSegmentLength) {
                        isInvalid = true;
                    }
                }
                if (isInvalid) {
                    activeDragColor = '#ef4444'; 
                    
                    ctx.beginPath();
                    ctx.arc(state.mouseX, state.mouseY, 10, 0, Math.PI * 2);
                    ctx.fillStyle = '#ef4444'; 
                    ctx.fill();
                    
                    ctx.strokeStyle = '#ffffff';
                    ctx.lineWidth = 3;
                    ctx.lineCap = 'round';
                    ctx.beginPath();
                    ctx.moveTo(state.mouseX - 4, state.mouseY - 4);
                    ctx.lineTo(state.mouseX + 4, state.mouseY + 4);
                    ctx.moveTo(state.mouseX + 4, state.mouseY - 4);
                    ctx.lineTo(state.mouseX - 4, state.mouseY + 4);
                    ctx.stroke();
                } else {
                    activeDragColor = line.color;
                }
            }

            // 3. Highlight transferring vehicles
            let activeDragVehicleType = state.draggedVehicleType;

            if (state.isDraggingExistingVehicle) {
                activeDragVehicleType = state.draggedVehicleType;
                let isDraggingOverValidTrack = state.hoveredLineData?.line && state.hoveredLineData.line.type === activeDragVehicleType;
                if (isDraggingOverValidTrack && state.hoveredLineData.line !== state.draggedVehicle.line) {
                    ctx.lineWidth = 14;
                    ctx.strokeStyle = '#22c55e44'; 
                    ctx.beginPath();
                    let linePoints = state.hoveredLineData.line.stations;
                    ctx.moveTo(linePoints[0].x, linePoints[0].y);
                    for (let p of linePoints) ctx.lineTo(p.x, p.y);
                    ctx.stroke();
                }
                ctx.save();
                ctx.translate(state.mouseX, state.mouseY);
                ctx.fillStyle = activeDragVehicleType === 'metro' ? '#2563EB' : '#F59E0B';
                if (activeDragVehicleType === 'metro') {
                    ctx.beginPath(); ctx.roundRect(-20, -7, 40, 14, 7); ctx.fill();
                } else {
                    ctx.beginPath(); ctx.roundRect(-12, -8, 24, 16, [3, 8, 8, 3]); ctx.fill();
                }
                ctx.restore();
            }

            if (activeDragVehicleType && !state.isDraggingExistingVehicle) {
                if (activeDragVehicleType === 'boogie') {
                    if (state.hoveredMetroVehicle) {
                        ctx.beginPath();
                        ctx.arc(state.hoveredMetroVehicle.x, state.hoveredMetroVehicle.y, 24, 0, Math.PI * 2);
                        ctx.strokeStyle = '#22c55e';
                        ctx.lineWidth = 4;
                        ctx.stroke();
                    }

                    ctx.save();
                    ctx.translate(state.mouseX, state.mouseY);
                    ctx.fillStyle = '#475569';
                    ctx.strokeStyle = '#f8fafc';
                    ctx.lineWidth = 2.5;
                    ctx.beginPath();
                    ctx.roundRect(-15, -7, 30, 14, 5);
                    ctx.fill();
                    ctx.stroke();
                    ctx.restore();
                } else if (activeDragVehicleType === 'interchange') {
                    if (state.hoveredTargetStation) {
                        ctx.beginPath();
                        ctx.arc(state.hoveredTargetStation.x, state.hoveredTargetStation.y, CONFIG.stationRadius * 2.2, 0, Math.PI * 2);
                        ctx.strokeStyle = '#a855f7';
                        ctx.lineWidth = 4;
                        ctx.stroke();
                    }

                    ctx.save();
                    ctx.translate(state.mouseX, state.mouseY);
                    ctx.strokeStyle = '#ffffff';
                    ctx.lineWidth = 2.5;
                    ctx.fillStyle = '#a855f7';
                    ctx.beginPath();
                    ctx.arc(0, 0, 10, 0, Math.PI * 2);
                    ctx.fill();
                    ctx.stroke();
                    ctx.restore();
                } else {
                    let targetType = activeDragVehicleType;
                    let isDraggingOverValidTrack = state.hoveredLineData?.line && state.hoveredLineData.line.type === targetType;
                    
                    if (isDraggingOverValidTrack) {
                        ctx.lineWidth = 14;
                        ctx.strokeStyle = '#22c55e44'; 
                        ctx.beginPath();
                        let linePoints = state.hoveredLineData.line.stations;
                        ctx.moveTo(linePoints[0].x, linePoints[0].y);
                        for (let p of linePoints) ctx.lineTo(p.x, p.y);
                        ctx.stroke();
                    }

                    ctx.save();
                    ctx.translate(state.mouseX, state.mouseY);
                    ctx.fillStyle = targetType === 'metro' ? '#2563EB' : '#F59E0B';
                    if (targetType === 'metro') {
                        ctx.beginPath(); ctx.roundRect(-20, -7, 40, 14, 7); ctx.fill();
                    } else {
                        ctx.beginPath(); ctx.roundRect(-12, -8, 24, 16, [3, 8, 8, 3]); ctx.fill();
                    }
                    ctx.restore();
                }
            }

            // 4. Draw Vehicles SECOND (so they glide underneath stations)
            state.vehicles.forEach(v => {
                if (v !== state.draggedVehicle || !state.isDraggingExistingVehicle) {
                    v.draw(ctx);
                }
            });

            // 5. Draw Stations LAST (topmost layer)
            let buildType = typeof state.buildMode === 'string' ? state.buildMode : state.buildMode.type;

            state.stations.forEach(s => {
                let highlight = null;
                if (activeDragColor && s === state.hoveredTargetStation && s !== state.dragStartStation) {
                    let isReachable = true;
                    if (buildType === 'bus' && state.dragStartStation && !state.draggingSegment) {
                        let dist = getDist(state.dragStartStation, s);
                        if (dist > CONFIG.maxBusSegmentLength) isReachable = false;
                    }
                    if (isReachable) highlight = activeDragColor;
                }

                // If Interchange Upgrade is selected and hovered
                if (state.buildMode === 'interchange' && s === state.hoveredTargetStation && !s.isInterchange) {
                    highlight = '#a855f7';
                }

                // Visual concentric pulsing alert rings only if the station has been unconnected past the grace period
                const isStationConnected = state.lines.some(l => l.stations.includes(s));
                if (!isStationConnected && s.unconnectedTime >= CONFIG.unconnectedGracePeriod) {
                    // Ring 1
                    const pulseProgress = (state.frames % 120) / 120;
                    const r = CONFIG.stationRadius + (pulseProgress * 30);
                    const alpha = 1 - pulseProgress;
                    ctx.strokeStyle = `rgba(239, 68, 68, ${alpha})`; 
                    ctx.lineWidth = 2;
                    ctx.beginPath();
                    ctx.arc(s.x, s.y, r, 0, Math.PI * 2);
                    ctx.stroke();

                    // Ring 2 (Concentric delay offset)
                    const pulseProgress2 = ((state.frames + 60) % 120) / 120;
                    const r2 = CONFIG.stationRadius + (pulseProgress2 * 30);
                    const alpha2 = 1 - pulseProgress2;
                    ctx.strokeStyle = `rgba(239, 68, 68, ${alpha2})`;
                    ctx.lineWidth = 1.5;
                    ctx.beginPath();
                    ctx.arc(s.x, s.y, r2, 0, Math.PI * 2);
                    ctx.stroke();
                }

                s.draw(ctx, highlight);
            });

            drawParticles();

            ctx.restore();
        }

        function gameLoop() {
            if (!state.isPlaying) return;
            update(); draw(); requestAnimationFrame(gameLoop);
        }

        // --- INIT ---
        window.addEventListener('resize', () => {
            resize();
            draw();
        });
        resize();
        draw();
        registerSidebarDraggers();
