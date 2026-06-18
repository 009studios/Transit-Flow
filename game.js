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
            let minDistSq = 400; 
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
