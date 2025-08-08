import LeanCats.CatParser

open Lean.Meta Lean Lean.Expr Elab

elab "defcat" name:ident " := " "<" filename:str ">" : command => do
  Command.withNamespace name.getId do
    let modelExprCoreM : CoreM Expr := Lean.Meta.MetaM.run' <| parseModel filename.getString
    let modelExpr : Expr ← Lean.Elab.Command.liftCoreM modelExprCoreM
    let modelTypeCoreM : CoreM Expr := Lean.Meta.MetaM.run' <| inferType modelExpr
    let modelType : Expr ← Lean.Elab.Command.liftCoreM modelTypeCoreM
      let defnInfo : DefinitionVal := {
      name := name.getId
      value := modelExpr
      levelParams := []
      type := modelType
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe
    }
    -- Add the declaration to the environment
    Lean.Elab.Command.liftCoreM <| addDecl (Declaration.defnDecl defnInfo)

defcat TSO := <"Cats/tso.cat">

#check TSO
