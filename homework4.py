# NAME: Charles Rawlins, Kyle Whitlatch
# DATE: 4/20/2020
# FILE: Homework 4

from tkinter import *
import math
import copy
from PIL import Image, ImageDraw

global drawingMatrix,drawingUpShift,drawingDownShift,lineMoveList

class indTree:
    def __init__(self,dataIDList):
        self.dataList = dataIDList
        self.leafList = []
        self.numAvg = 1 # TODO: CHANGE LATER?
        # Use Trinary tree for this problem like example
        self.treeDepth = math.ceil(math.log(len(self.dataList)/self.numAvg,3))
        self.maxLeaves = 3 ** self.treeDepth
        print("Tree Depth = " + str(self.treeDepth))
        print("Replication Level = " + str(self.treeDepth - 2))

        self.levelStrings = []
        alpha = 'a'
        for i in range(0,self.treeDepth):
            self.levelStrings.append(alpha)
            alpha = chr(ord(alpha) + 1)

        # indSum = 0
        # for i in range(self.treeDepth):
        #     indSum += 3**i
        # self.indexSize = indSum - 1 # index

        # Create Trinary Tree from data (Leave as Trinary for this problem)

        # Create list of Leaf Nodes
        for i in range(0,self.maxLeaves):
            idString = self.levelStrings[-1]
            if i < len(self.dataList):
                leafNode = indNode(idString + str(i), data=self.dataList[i])
            else:
                leafNode = indNode(idString + str(i)) # Add filler null object to fill out rest of tree
                #TODO: incorpoarate into rest of program
            self.leafList.append(leafNode)

        # Assign Leaf Nodes to intermediate nodes in tree until root
        self.treeMatrix = []
        self.treeMatrix.append(self.leafList)

        for i in range(0,self.treeDepth):
            interIncr = 0
            interList = []
            if(i != (self.treeDepth - 1)):
                for j in range(0,len(self.treeMatrix[i]),3):
                    interNode = indNode(self.levelStrings[-(i+2)] + str(interIncr),isInter=True)
                    interIncr += 1
                    interNode.assignChildren(self.treeMatrix[i][j],self.treeMatrix[i][j+1],self.treeMatrix[i][j+2])
                    interNode.genRange()
                    interList.append(interNode)
            else:
                interNode = indNode("Root", isInter=True,isRoot=True)
                interNode.assignChildren(self.treeMatrix[i][0],self.treeMatrix[i][1],self.treeMatrix[i][2])
                interList.append(interNode)

            self.treeMatrix.append(interList)

        self.treeMatrix = sorted(self.treeMatrix, key=len) # Resort to have root at idx 0
        self.treeMatrix[0][0].genRange()

    # Generated matrix of tree modes!


class indNode:
    def __init__(self,id,data=None, isInter=False,isRoot=False):
        self.id = id
        self.isRoot = isRoot
        self.isInter = isInter
        self.data = data
        self.toRootIdx = 0
        self.toIndexIdx = 0
        self.childIndices = []
        if self.data != None:
            self.dataString = "DATA_" + str(self.data) # Acts as payload

        if isInter:
            self.id = self.id + " (INDEX)"
            self.left = None
            self.middle = None
            self.right = None
            self.dataRange = [0,0]
        else:
            self.id = self.id + " (DATA)"

        if isRoot:
            self.trunkRanges = []

    def assignChildren(self,left, middle, right):
        self.left = left
        self.middle = middle
        self.right = right

    def genRange(self):
        # Check if children are nodes with data or intr nodes
        if self.isRoot:
            self.trunkRanges.append(self.left.dataRange)
            self.trunkRanges.append(self.middle.dataRange)
            self.trunkRanges.append(self.right.dataRange)
            return

        if self.left.data != None:
            rightData = self.left.data
            if self.middle.data != None:
                rightData = self.middle.data
            if self.right.data != None:
                rightData = self.right.data

            self.dataRange = [self.left.data, rightData]
        else:
            # TODO: account for empty objects
            self.trunkRanges = []
            self.trunkRanges.append(self.left.dataRange)
            self.trunkRanges.append(self.middle.dataRange)
            self.trunkRanges.append(self.right.dataRange)
            self.dataRange = [self.trunkRanges[0][0], self.trunkRanges[2][1]]

    def __str__(self):
        return self.id


class indexScheme:

    def __init__(self):
        self.broadcastObjs = []
        self.bCastBeginIdx = []

    def incrBCastIdx(self,bArray,treeIdxs,workingMatrix):

        for i in range(0,len(treeIdxs)):
            bArray.append(workingMatrix[i + 1][treeIdxs[i] - 1])

        treeIdxs[-1] += 1
        bArray.append(workingMatrix[-1][treeIdxs[-1] - 1])
        treeIdxs[-1] += 1
        bArray.append(workingMatrix[-1][treeIdxs[-1] - 1])


        # Check which inter nodes to broadcast next time
        for i in range(len(treeIdxs) - 1):
            if i < len(treeIdxs) - 2:
                if (treeIdxs[i + 1] % 3 == 0) and (treeIdxs[i+2] % 9 == 0):
                    treeIdxs[i] += 1
            else:
                if (treeIdxs[i + 1] % 3 == 0):
                    treeIdxs[i] += 1

        treeIdxs[-1] += 1


    def genBroadcastObjs(self):
        # Generate main broadcast object array
        bArray = []
        numGroups = len(self.probTree.treeMatrix[-2])
        treeIdxs = [1] * (len(self.probTree.treeMatrix) - 1)
        workingMatrix = self.probTree.treeMatrix

        for i in range(numGroups):

            if (i % 3 == 0):
                bArray.append(self.probTree.treeMatrix[0][0]) # Append Root

            self.incrBCastIdx(bArray,treeIdxs,workingMatrix)

        self.broadcastObjs = bArray

    def genPayload(self):

        pointerMatrix = []

        for dataObj in self.broadcastObjs:
            objList = []

            if dataObj.isRoot:
                objList = copy.deepcopy(dataObj.trunkRanges)
                leftIdx = self.broadcastObjs.index(dataObj.left)
                middleIdx = self.broadcastObjs.index(dataObj.middle)
                rightIdx = self.broadcastObjs.index(dataObj.right)
                objList.append(leftIdx)
                objList.append(middleIdx)
                objList.append(rightIdx)
                dataObj.childIndices.append(leftIdx)
                dataObj.childIndices.append(middleIdx)
                dataObj.childIndices.append(rightIdx)

            elif dataObj.isInter:
                if(hasattr(dataObj, "trunkRanges")):
                    objList.append(dataObj.trunkRanges)
                leftIdx = self.broadcastObjs.index(dataObj.left)
                middleIdx = self.broadcastObjs.index(dataObj.middle)
                rightIdx = self.broadcastObjs.index(dataObj.right)
                objList.append(leftIdx)
                objList.append(middleIdx)
                objList.append(rightIdx)
                dataObj.childIndices.append(leftIdx)
                dataObj.childIndices.append(middleIdx)
                dataObj.childIndices.append(rightIdx)
            else:
                objList.append(dataObj.dataString)

            pointerMatrix.append(objList)

        return pointerMatrix

    def genBroadcastArray(self):
        timeIdx = 0
        timeList = []
        bCastList = []
        self.payLoadList = self.genPayload()
        self.payLoadList = self.payLoadList + self.payLoadList # Double for double broadcast

        # Double broadcast for simulation purposes
        for j in range(0,2):
            self.bCastBeginIdx.append(timeIdx)
            for i in range(len(self.broadcastObjs)):
                bCastList.append(self.broadcastObjs[i].id)
                timeList.append(timeIdx)
                timeIdx += 1

        self.broadcastObjs = self.broadcastObjs + self.broadcastObjs
        self.broadcastArray = bCastList
        self.timeArray = timeList

    def printTreeNodes(self):
        print("Tree Matrix:")
        for level in self.probTree.treeMatrix:
            for node in level:
                print("| " + str(node.id) + " |",end=" ")
            print("\n")

    def printBroadcast(self):
        print("Doubled Broadcast:")
        for idx in self.broadcastArray:
            print("|" + idx + "|\t", end=" ")
        print("\n")

    def genSimIndices(self):

        copiedArray = self.broadcastObjs

        # Generate copied Array of unique objects (WILL NO LONGER HAVE TREE RELATIONSHIPS!)
        for i in range(len(copiedArray)):
            copiedArray[i] = copy.deepcopy(copiedArray[i])

        for page,timeIdx in zip(copiedArray,self.timeArray):

            # Generate toRoot and toIndex Indices
            if(page.isRoot):
                page.toRootIdx = 0
                page.toIndexIdx = 0
            else:
                # Get next root idx
                try:
                    nextRootIdx = self.broadcastArray.index("Root (INDEX)", timeIdx + 1)
                    page.toRootIdx = nextRootIdx
                except ValueError as e:
                    # Likely at end of second broadcast, set index to 0
                    page.toRootIdx = -1  # Temp value for simulation purposes
                # Get next index idx
                idxList = []
                for i in range(timeIdx + 1, len(self.broadcastArray)):
                    if ("INDEX" in self.broadcastArray[i]):
                        idxList.append(i)

                if not idxList:
                    page.toIndexIdx = -1
                else:
                    for j in range(len(idxList)):
                        if page.isInter:
                            if ((idxList[j] - timeIdx) > 2):
                                page.toIndexIdx = idxList[j]
                                if page.toIndexIdx > page.toRootIdx and page.toRootIdx != -1:
                                    page.toIndexIdx = page.toRootIdx
                                break
                        else:
                            page.toIndexIdx = min(idxList)
                            if page.toIndexIdx > page.toRootIdx and page.toRootIdx != -1:
                                page.toIndexIdx = page.toRootIdx
                            break

                if(page.toIndexIdx == 0):
                    page.toIndexIdx = -1 # Patchwork

        self.workingCopy = copiedArray

        # Fix some errors in the previous loop and have indices jump to root if client has passed desired item
        for page in self.workingCopy:
            if len(page.childIndices) != 0:
                page.childIndices = list(set(page.childIndices))
                page.childIndices.sort()



        for i in range(len(self.payLoadList)):
            self.payLoadList[i] = copy.deepcopy(self.payLoadList[i])

        nextBCastIdx = self.bCastBeginIdx[1]
        for i in range(nextBCastIdx):
            if len(self.workingCopy[i].childIndices) != 0:
                for j in range(len(self.workingCopy[i].childIndices)):
                    if(self.workingCopy[i].childIndices[j] < i):
                        self.workingCopy[i].childIndices[j] = nextBCastIdx # Have client jump to next BCast
                        if(self.workingCopy[i].isRoot):
                            self.payLoadList[i][j+3] = nextBCastIdx
                        elif(self.workingCopy[i].isInter):
                            self.payLoadList[i][j+1] = nextBCastIdx

        for i in range(nextBCastIdx,len(self.workingCopy)):
            if len(self.workingCopy[i].childIndices) != 0:
                for j in range(len(self.workingCopy[i].childIndices)):
                    if(self.workingCopy[i].childIndices[j] < (i-nextBCastIdx)):
                        self.workingCopy[i].childIndices[j] = -1 # Normally goes to third bcast, make -1 for simulation

        self.nextBCastIdx = nextBCastIdx

    def createScheme(self, inputString):
        self.rawString = inputString
        dataBounds = self.rawString.split(",")
        temp = map(int,dataBounds)
        dataBounds = list(temp)
        dataIDList = []
        for i in range(dataBounds[0], dataBounds[1] + 1):
            dataIDList.append(i)

        self.probTree = indTree(dataIDList)
        print("Generated Tree Matrix!")
        self.printTreeNodes()
        self.genBroadcastObjs()
        self.genBroadcastArray()
        self.printBroadcast()
        self.genSimIndices()
        self.totalBCastTime = len(self.timeArray)
        return self.totalBCastTime


class clientClass:
    def __init__(self,clientStart,clientNeed,mainCanvas,timeWindList):
        self.cliIdx = clientStart
        self.desire = clientNeed
        self.desireString = "DATA_" + str(clientNeed)
        self.nextIdxJump = 0
        self.workingCanvas = mainCanvas
        self.workingDim = timeWindList
        self.textYDist = 50
        self.lineYDist = 20
        self.gotoNextBCast = False
        self.secondBCastIdx = 0

    def setEntry(self):
        global drawingMatrix,lineMoveList
        workX,workY,workWidth = self.workingDim[self.cliIdx+1]
        tempid = self.workingCanvas.create_line(workX,workY - self.textYDist,workX,workY,arrow=LAST)
        lineList = []
        lineList.append(tempid)
        lineList.append([workX,workY - self.textYDist,workX,workY])
        lineList.append(False)
        lineMoveList.append(lineList)
        workLabel = Label(self.workingCanvas, text="Client Entry!")
        workLabel.place(x=workX + workWidth/16, y=workY - 1.5 * self.textYDist)
        drawingMatrix.append(workLabel)

    def parseIdxs(self, workingNode, type):
        global drawingMatrix,lineMoveList

        if(type == "ROOT"):
            assert workingNode.isRoot
            for range in workingNode.trunkRanges:
                if(self.desire >= range[0]) and (self.desire <= range[1]):
                    workingIdx = workingNode.trunkRanges.index(range)
                    break

            self.nextIdxJump = workingNode.childIndices[workingIdx]

            # Second time around in next broadcast
            if self.gotoNextBCast:
                self.nextIdxJump += self.secondBCastIdx
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump - self.secondBCastIdx))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return

            if(self.nextIdxJump == self.secondBCastIdx):
                self.gotoNextBCast = True
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Missed Data! Go to " + str(self.nextIdxJump))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return
            else:
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return

        if(type == "INDEX") and workingNode.left.data == None:
            assert workingNode.isInter
            for range in workingNode.trunkRanges:
                if(self.desire >= range[0]) and (self.desire <= range[1]):
                    workingIdx = workingNode.trunkRanges.index(range)
                    break

            self.nextIdxJump = workingNode.childIndices[workingIdx]

            if(self.gotoNextBCast):
                self.nextIdxJump += self.secondBCastIdx
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump - self.secondBCastIdx))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return

            if (self.nextIdxJump == self.secondBCastIdx):
                    self.gotoNextBCast = True
                    workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                    tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                    lineList = []
                    lineList.append(tempid)
                    lineList.append([workX, workY - self.textYDist, workX, workY])
                    lineList.append(False)
                    lineMoveList.append(lineList)
                    workLabel = Label(self.workingCanvas, text="Missed Data! Go to " + str(self.nextIdxJump))
                    workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                    drawingMatrix.append(workLabel)
                    return
            else:
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return

        if (type == "INDEX") and workingNode.left.data != None:
            self.nextIdxJump = workingNode.childIndices[0]

            if (self.gotoNextBCast):
                self.nextIdxJump += self.secondBCastIdx
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump - self.secondBCastIdx))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return

            if (self.nextIdxJump == self.secondBCastIdx):
                self.gotoNextBCast = True
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Missed Data! Go to " + str(self.nextIdxJump))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return
            else:
                workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.textYDist, workX, workY])
                lineList.append(False)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Wait for " + str(self.nextIdxJump))
                workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                drawingMatrix.append(workLabel)
                return


    def jumpwithIdx(self,type):
        global drawingMatrix,lineMoveList

        if type == "WAIT":
            # Create Lines to symbolize wait time by client until client reaches the correct wait time
            for i in range(self.cliIdx + 1, self.nextIdxJump):
                workX, workY, workWidth = self.workingDim[i + 1]
                tempid = self.workingCanvas.create_line(workX, workY - self.lineYDist, workX + workWidth, workY-self.lineYDist, arrow=LAST,dash=(3,5))
                lineList = []
                lineList.append(tempid)
                lineList.append([workX, workY - self.lineYDist, workX + workWidth, workY-self.lineYDist])
                lineList.append(True)
                lineMoveList.append(lineList)
                workLabel = Label(self.workingCanvas, text="Waiting...")
                labelWidth = 80
                workLabel.place(x=workX + workWidth /2 - labelWidth/2, y=workY - self.textYDist,width=labelWidth)
                drawingMatrix.append(workLabel)
            self.cliIdx = self.nextIdxJump
            self.nextIdxJump = 0
            return

        if type == "CHECK":
            workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
            tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST,dash=(3,5))
            lineList = []
            lineList.append(tempid)
            lineList.append([workX, workY - self.textYDist, workX, workY])
            lineList.append(True)
            lineMoveList.append(lineList)
            workLabel = Label(self.workingCanvas, text="Checking Data...")
            workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
            drawingMatrix.append(workLabel)
            self.cliIdx += 1

    def checkData(self,workingNode):

        if workingNode.data == self.desire:
            return True
        else:
            return False

    def getData(self,workingNode):
        global drawingMatrix,lineMoveList
        assert workingNode.data == self.desire
        workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
        tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
        lineList = []
        lineList.append(tempid)
        lineList.append([workX, workY - self.textYDist, workX, workY])
        lineList.append(False)
        lineMoveList.append(lineList)
        workLabel = Label(self.workingCanvas, text="Got Data Item: " + str(workingNode.data) + "!")
        workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
        drawingMatrix.append(workLabel)

    def jumptoRoot(self,workingNode):
        self.nextIdxJump = workingNode.toRootIdx
        if(self.nextIdxJump == self.secondBCastIdx):
            self.gotoNextBCast = True

    def checkIndex(self,workingNode):
        if workingNode.left.data == None:
            foundData = False
            for range in workingNode.trunkRanges:
                if (self.desire >= range[0]) and (self.desire <= range[1]):
                    foundData = True
                    workingIdx = workingNode.trunkRanges.index(range)
                    break

            if foundData == True:
                if(workingNode.childIndices[workingIdx] == self.secondBCastIdx):
                    self.nextIdxJump = self.secondBCastIdx
                    self.gotoNextBCast = True
                    workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
                    tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
                    lineList = []
                    lineList.append(tempid)
                    lineList.append([workX, workY - self.textYDist, workX, workY])
                    lineList.append(False)
                    lineMoveList.append(lineList)
                    workLabel = Label(self.workingCanvas, text="Missed Data! Go to " + str(self.nextIdxJump))
                    workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
                    drawingMatrix.append(workLabel)

            return foundData

        if workingNode.left.data != None:
            foundData = False

            if(self.desire >= workingNode.dataRange[0]) and (self.desire <= workingNode.dataRange[1]):
                foundData = True

            return foundData

    def jumptoNextIndex(self,workingNode):
        self.nextIdxJump = workingNode.toIndexIdx

    def sayJumptoRoot(self,workingNode):
        global drawingMatrix, lineMoveList
        workX, workY, workWidth = self.workingDim[self.cliIdx + 1]
        tempid = self.workingCanvas.create_line(workX, workY - self.textYDist, workX, workY, arrow=LAST)
        lineList = []
        lineList.append(tempid)
        lineList.append([workX, workY - self.textYDist, workX, workY])
        lineList.append(False)
        lineMoveList.append(lineList)
        workLabel = Label(self.workingCanvas, text="Waiting for Root...")
        workLabel.place(x=workX + workWidth / 16, y=workY - self.textYDist)
        drawingMatrix.append(workLabel)


def createReplication(probScheme, dataEntry,timeLabel):
    totalTime = probScheme.createScheme(dataEntry.get())
    newString = "Indiv. Bcast Time = " + str(int(totalTime/2)) + " units"
    timeLabel.configure(text=newString)
    print("Awaiting Client Input!")

def shiftUpDrawings(mainCanvas):
    global drawingMatrix,drawingUpShift,lineMoveList
    for widget in drawingMatrix:
        currYPos = widget.winfo_y()
        widget.place(y=currYPos+drawingUpShift)

    for lineData in lineMoveList:
        lineId = lineData[0]
        lineCoords = lineData[1]
        isDashed = lineData[2]
        mainCanvas.delete(lineId)
        lineCoords[1] += drawingUpShift
        lineCoords[3] += drawingUpShift
        if(isDashed):
            tempid = mainCanvas.create_line(lineCoords[0], lineCoords[1], lineCoords[2], lineCoords[3], arrow=LAST,dash=(3,5) )
        else:
            tempid = mainCanvas.create_line(lineCoords[0],lineCoords[1],lineCoords[2],lineCoords[3],arrow=LAST)

        lineData[0] = tempid
        lineData[1] = lineCoords


def shiftDownDrawings(mainCanvas):
    global drawingMatrix, drawingDownShift,lineMoveList
    for widget in drawingMatrix:
        currYPos = widget.winfo_y()
        widget.place(y=currYPos + drawingDownShift)

    for lineData in lineMoveList:
        lineId = lineData[0]
        lineCoords = lineData[1]
        isDashed = lineData[2]
        mainCanvas.delete(lineId)
        lineCoords[1] += drawingDownShift
        lineCoords[3] += drawingDownShift
        if (isDashed):
            tempid = mainCanvas.create_line(lineCoords[0], lineCoords[1], lineCoords[2], lineCoords[3], arrow=LAST,dash=(3,5))
        else:
            tempid = mainCanvas.create_line(lineCoords[0], lineCoords[1], lineCoords[2], lineCoords[3], arrow=LAST)

        lineData[0] = tempid
        lineData[1] = lineCoords

# Client jumps to second client and finds desired data if missed in the first broadcast
def secondBCastSim(workingObjs, cli):
    cli.parseIdxs(workingObjs[cli.cliIdx], "ROOT")
    cli.jumpwithIdx("WAIT")
    while (workingObjs[cli.cliIdx].data == None):
        cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
        cli.jumpwithIdx("WAIT")

    while (cli.checkData(workingObjs[cli.cliIdx]) == False):
        cli.jumpwithIdx("CHECK")
        # Got Desired Data!
    cli.getData(workingObjs[cli.cliIdx])

def simClient(probScheme, cliEntry,cliDataEntry,probWindow):

    assert(int(cliEntry.get()) < int(probScheme.totalBCastTime))

    schemeWin = Toplevel(probWindow)
    mainCanvas = Canvas(schemeWin, width=1750,height=400)
    mainCanvas.pack(expand=YES,fill=BOTH)
    schemeWin.title("Client Indexing Simulation")

    bCastY = 50
    ySpacing = 20
    yRow = 180
    bCastXInit = 125
    bCastX = 125
    pageWidth = 250

    cliEntryPoint = cliEntry.get()
    cliDataNeed = cliDataEntry.get()
    numRows = 1

    global drawingMatrix,drawingUpShift,drawingDownShift,drawingMatrix,lineMoveList
    lineMoveList = []
    timeWindList = []
    timeWindList.append([bCastX, bCastY,pageWidth])
    drawingMatrix = []
    drawingDownShift = 100
    drawingUpShift = -100

    # Create Buttons to shift Broadcast Up and Down
    upButton = Button(mainCanvas, text="Shift UP",command= lambda: shiftUpDrawings(mainCanvas))
    downButton = Button(mainCanvas, text="Shift DOWN",command= lambda: shiftDownDrawings(mainCanvas))
    upButton.place(x=0,y=0, width=100)
    downButton.place(x=0,y=40,width=100)

    for pageid,payload,timepage,pageObj in zip(probScheme.broadcastArray,probScheme.payLoadList,probScheme.timeArray,probScheme.broadcastObjs):
        if(timepage == probScheme.nextBCastIdx):
            workingLabel = Label(mainCanvas, text=pageid,borderwidth=4,relief="solid")
            workingLabel.place(x=bCastX, y=bCastY, width=pageWidth)
            drawingMatrix.append(workingLabel)
        else:
            workingLabel = Label(mainCanvas, text=pageid, borderwidth=2, relief="solid")
            workingLabel.place(x=bCastX, y=bCastY, width=pageWidth)
            drawingMatrix.append(workingLabel)

        payloadLabel = Label(mainCanvas, text=str(payload), borderwidth=2,relief="solid")
        payloadLabel.place(x=bCastX, y=bCastY + ySpacing, width=pageWidth)
        drawingMatrix.append(payloadLabel)
        if(timepage > probScheme.nextBCastIdx):
            workingString = "Root: "
            if(pageObj.toRootIdx == 0):
                workingString += str(pageObj.toRootIdx) + " Idx: "
            elif(pageObj.toRootIdx != -1):
                workingString += str(pageObj.toRootIdx - probScheme.nextBCastIdx) + " Idx: "
            else:
                workingString += str(pageObj.toRootIdx) + " Idx: "

            if(pageObj.toIndexIdx == 0):
                workingString += str(pageObj.toIndexIdx)
            elif (pageObj.toIndexIdx != -1):
                workingString += str(pageObj.toIndexIdx - probScheme.nextBCastIdx)
            else:
                workingString += str(pageObj.toIndexIdx)

            indexLabel = Label(mainCanvas, text=workingString,borderwidth=2,relief="solid")
            indexLabel.place(x=bCastX, y=bCastY + 2*ySpacing, width=pageWidth)
            drawingMatrix.append(indexLabel)
        else:
            indexLabel = Label(mainCanvas,text="Root: " + str(pageObj.toRootIdx) + " Idx: " + str(pageObj.toIndexIdx), borderwidth=2, relief="solid")
            indexLabel.place(x=bCastX, y=bCastY + 2 * ySpacing, width=pageWidth)
            drawingMatrix.append(indexLabel)

        timeLabel = Label(mainCanvas, text=str(timepage),borderwidth=2,relief="solid")
        timeLabel.place(x=bCastX, y=bCastY + 3*ySpacing, width=pageWidth)
        drawingMatrix.append(timeLabel)

        # Record index positions for client indexing
        posList = [bCastX, bCastY, pageWidth]
        timeWindList.append(posList)

        if(timepage != 0 and (timepage +1) % 6 == 0):
            bCastY += yRow
            bCastX = bCastXInit
            numRows +=1
        else:
            bCastX += pageWidth

    ################## Do Client Indexing! ####################
    cli = clientClass(int(cliEntry.get()),int(cliDataEntry.get()),mainCanvas,timeWindList)
    workingObjs = probScheme.workingCopy
    cli.setEntry()
    cli.secondBCastIdx = probScheme.nextBCastIdx

    # Check if current page is root or the correct index
    # Get Root or wait for root index page.
    if(workingObjs[cli.cliIdx].isRoot):
        # Started at root, get root info

        ################ MAIN FUNC ################
        cli.parseIdxs(workingObjs[cli.cliIdx], "ROOT")
        cli.jumpwithIdx("WAIT")
        if(cli.gotoNextBCast):
            secondBCastSim(workingObjs, cli)
        else:
            # Easiest Case
            while(workingObjs[cli.cliIdx].data == None):
                cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                cli.jumpwithIdx("WAIT")

            while(cli.checkData(workingObjs[cli.cliIdx]) == False):
                cli.jumpwithIdx("CHECK")

            # Got Desired Data!
            cli.getData(workingObjs[cli.cliIdx])

    elif(workingObjs[cli.cliIdx].isInter):

        if (cli.checkIndex(workingObjs[cli.cliIdx])):

            if(cli.gotoNextBCast):
                cli.jumpwithIdx("WAIT")
                secondBCastSim(workingObjs,cli)
            else:
                if(hasattr(workingObjs[cli.cliIdx], "trunkRanges")):
                    # Working with higher inter node case
                    while (workingObjs[cli.cliIdx].data == None):
                        cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                        cli.jumpwithIdx("WAIT")

                else:
                    # Working with level n-1 node case (should always be before relevant data, so no jump to second bcast)
                    cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                    cli.jumpwithIdx("WAIT")
                    while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                        cli.jumpwithIdx("CHECK")

                cli.getData(workingObjs[cli.cliIdx])

        else:
            cli.jumptoRoot(workingObjs[cli.cliIdx])
            cli.jumpwithIdx("WAIT")
            if (cli.gotoNextBCast):
                secondBCastSim(workingObjs, cli)
            else:
                cli.parseIdxs(workingObjs[cli.cliIdx], "ROOT")
                cli.jumpwithIdx("WAIT")


                while (workingObjs[cli.cliIdx].data == None):
                    cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                    cli.jumpwithIdx("WAIT")

                while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                    cli.jumpwithIdx("CHECK")

                # Got Desired Data!
                cli.getData(workingObjs[cli.cliIdx])

    else:
        # Entered at data object...
        cli.jumptoNextIndex(workingObjs[cli.cliIdx])
        cli.jumpwithIdx("WAIT")

        if(cli.cliIdx == cli.secondBCastIdx):
            cli.gotoNextBCast = True
            secondBCastSim(workingObjs, cli)
        else:
            if(workingObjs[cli.cliIdx].isRoot):
                cli.parseIdxs(workingObjs[cli.cliIdx], "ROOT")
                cli.jumpwithIdx("WAIT")
                if(cli.gotoNextBCast):
                    secondBCastSim(workingObjs, cli)
                else:
                    # Easiest Case
                    while (workingObjs[cli.cliIdx].data == None):
                        cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                        cli.jumpwithIdx("WAIT")

                    while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                        cli.jumpwithIdx("CHECK")

                    # Got Desired Data!
                    cli.getData(workingObjs[cli.cliIdx])
            else:
                if (cli.checkIndex(workingObjs[cli.cliIdx])):
                    # Index has relevant Data
                    if (cli.gotoNextBCast):
                        cli.jumpwithIdx("WAIT")
                        secondBCastSim(workingObjs, cli)
                    else:
                        if (hasattr(workingObjs[cli.cliIdx], "trunkRanges")):
                            # Working with higher inter node case
                            while (workingObjs[cli.cliIdx].data == None):
                                cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                                cli.jumpwithIdx("WAIT")

                            while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                                cli.jumpwithIdx("CHECK")

                        else:
                            # Working with level n-1 node case (should always be before relevant data, so no jump to second bcast)
                            cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                            cli.jumpwithIdx("WAIT")
                            while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                                cli.jumpwithIdx("CHECK")

                        cli.getData(workingObjs[cli.cliIdx])

                else:
                    # Index has no relevant data, go to next root
                    cli.sayJumptoRoot(workingObjs[cli.cliIdx])
                    cli.jumptoRoot(workingObjs[cli.cliIdx])
                    cli.jumpwithIdx("WAIT")

                    ################ MAIN FUNC ################
                    cli.parseIdxs(workingObjs[cli.cliIdx], "ROOT")
                    cli.jumpwithIdx("WAIT")
                    if (cli.gotoNextBCast):
                        secondBCastSim(workingObjs,cli)
                    else:
                        while (workingObjs[cli.cliIdx].data == None):
                            cli.parseIdxs(workingObjs[cli.cliIdx], "INDEX")
                            cli.jumpwithIdx("WAIT")

                        while (cli.checkData(workingObjs[cli.cliIdx]) == False):
                            cli.jumpwithIdx("CHECK")

                        # Got Desired Data!
                        cli.getData(workingObjs[cli.cliIdx])

# Handles entry window geometry for problem 1
def problem1Func(mainWindow):
    probX = 200
    probY = 100
    probWindow = Toplevel(mainWindow)
    probWindow.geometry(str(probX) + "x" + str(probY))
    probWindow.title("Partial Replication with Indexing")
    probScheme = indexScheme()

    # Setup User input GUI
    commandX = 0
    commandY = 0
    probWidgetWidth = 250
    widgetYSpace = 20
    enterLabel = Label(probWindow, text="Enter an Indexing Scheme:",font="Helvetica 10 bold")
    enterLabel.place(x=commandX,y=commandY, width=probWidgetWidth)
    dataLabel = Label(probWindow, text="Enter Data ID Range (0,3^X-1; x >= 2)", font="Helvetica 10")
    dataLabel.place(x=commandX, y=commandY + widgetYSpace, width=probWidgetWidth)
    dataEntry = Entry(probWindow)
    dataEntry.place(x=commandX, y=commandY + 2*widgetYSpace, width=probWidgetWidth)
    timeLabel = Label(probWindow, text="Total Broadcast Time: 0 units", font="Helvetica 10")
    timeLabel.place(x=commandX, y=commandY + 3*widgetYSpace, width=probWidgetWidth + 15)

    genButton = Button(probWindow, text="Generate Structure!", command=lambda: createReplication(probScheme, dataEntry,timeLabel))
    genButton.place(x=commandX, y=commandY + 4 * widgetYSpace, width=probWidgetWidth)

    cliLabel = Label(probWindow, text="Enter Client Entry Time:", font="Helvetica 10")
    cliLabel.place(x=commandX, y=commandY + 6*widgetYSpace, width=probWidgetWidth)
    cliEntry = Entry(probWindow)
    cliEntry.place(x=commandX, y=commandY + 7 * widgetYSpace, width=probWidgetWidth)

    cliDataLabel = Label(probWindow, text="Enter Client Data Item:", font="Helvetica 10")
    cliDataLabel.place(x=commandX, y=commandY + 8 * widgetYSpace, width=probWidgetWidth)
    cliDataEntry = Entry(probWindow)
    cliDataEntry.place(x=commandX, y=commandY + 9 * widgetYSpace, width=probWidgetWidth)

    simButton = Button(probWindow, text="Simulate Indexing!",
                       command=lambda: simClient(probScheme, cliEntry,cliDataEntry,probWindow))
    simButton.place(x=commandX, y=commandY + 10 * widgetYSpace, width=probWidgetWidth)

    probWindow.geometry(str(probWidgetWidth + 15) + "x" + str(12*widgetYSpace))


# Main function, has setup for problem selection window.
if __name__ == "__main__":

    mainWindow = Tk()
    mainWindow.title("Homework 4")
    globalX = 200
    globalY = 150
    mainWindow.geometry([str(globalX) + "x" + str(globalY)])
    startY = 5
    widgetYSpace = 20
    widgetWidth = 150
    widgetX = globalX/2 - widgetWidth/2

    selectLabel = Label(mainWindow, text="Select a Problem:")
    selectLabel.place(x=widgetX, y=startY, width=widgetWidth)
    problem1But = Button(mainWindow, text="Partial Replication",command=lambda: problem1Func(mainWindow))
    problem1But.place(x=widgetX, y=startY + widgetYSpace, width=widgetWidth)

    mainWindow.mainloop()

