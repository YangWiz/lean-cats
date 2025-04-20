import LeanCats.AST

open CatsAST

def testExpr : Expr := .id 1
def testTerm : Term := .keyword "test"
def testBinOp : BinOp := .union testTerm testExpr
def testStmt : Stmt := .comment "This is a comment"
def testBinding : Binding := .varbinding testExpr testExpr
def testAcyclic : Acyclic := .expr testExpr
def testAcyclicAs : AcyclicAs := .expr testExpr testExpr
def testInstruction : Instruction := .check "test" testExpr
def testModel : Model := .instructions [testInstruction, .expr testExpr, .acyclic testAcyclic]

#eval toString testExpr
#eval toString testTerm
#eval toString testBinOp
#eval toString testStmt
#eval toString testBinding
#eval toString testAcyclic
#eval toString testAcyclicAs
#eval toString testInstruction
#eval toString testModel
