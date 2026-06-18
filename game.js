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
