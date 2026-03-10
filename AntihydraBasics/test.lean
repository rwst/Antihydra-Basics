import AntihydraBasics.Antihydra
open Antihydra

def isHalt (c : Config) : Bool := c.state.isNone
def getL (c : Config) : Nat := countOnes c.left
def getR (c : Config) : Nat := countOnes c.right

#eval isHalt (run (P_Config_Pad 0 0 4 2) 2)
#eval isHalt (run (P_Config_Pad 0 1 4 2) 2)
