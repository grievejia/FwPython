import FwPython.Common.Identifier
import FwPython.Gradual.Types

/-! # Source obligations

Source obligations describe the source-language meaning reported by checked
runtime blame. They name source expression positions and method boundaries
without depending on checked syntax, runtime contracts, or type-system proofs.
-/

/-- An immediate source-expression child selected from a parent expression. -/
inductive SourceExpressionChild where
  /-- The receiver subexpression of a source attribute access. -/
  | attributeReceiver
  /-- The callee subexpression of a source call. -/
  | callCallee
  /-- The argument subexpression of a source call. -/
  | callArgument
  /-- The test subexpression of a source conditional. -/
  | conditionTest
  /-- The then-branch subexpression of a source conditional. -/
  | conditionThen
  /-- The else-branch subexpression of a source conditional. -/
  | conditionElse
  deriving DecidableEq, Repr

/-- A root-to-descendant list of source-expression child steps in outer-to-inner order. -/
abbrev SourceExpressionPath := List SourceExpressionChild

/-- A source expression position inside the program main expression or a method body. -/
inductive SourceExpressionSite where
  /-- The source expression reached by `path` from the program main expression. -/
  | main : SourceExpressionPath -> SourceExpressionSite
  /-- The source expression reached by `path` from method `methodName` in class `className`. -/
  | methodBody : (className : Identifier) -> (methodName : Identifier) ->
      SourceExpressionPath -> SourceExpressionSite
  deriving DecidableEq, Repr

namespace SourceExpressionSite

/-- Append one child step to the end of a source expression path, preserving the root. -/
def child : SourceExpressionSite -> SourceExpressionChild -> SourceExpressionSite
  | .main path, child => .main (path ++ [child])
  | .methodBody className methodName path, child =>
      .methodBody className methodName (path ++ [child])

end SourceExpressionSite

/-- A source program position that can supply the reported meaning of checked blame. -/
inductive SourceSite where
  /-- A source expression position in the program main expression or a method body. -/
  | expression : SourceExpressionSite -> SourceSite
  /-- The explicit-argument boundary for a source method. -/
  | methodParameter : (className : Identifier) -> (methodName : Identifier) -> SourceSite
  /-- The declared return boundary for a source method. -/
  | methodReturn : (className : Identifier) -> (methodName : Identifier) -> SourceSite
  deriving DecidableEq, Repr

/-- The source-language obligation reported by a blame-capable checked operation. -/
inductive SourceObligation where
  /-- `hasType site G` means a value crossing `site` is expected to satisfy
  gradual type `G`; checked execution enforces the corresponding checked target
  where runtime structure is needed. -/
  | hasType : SourceSite -> GTy -> SourceObligation
  /-- `hasAttribute site attrName` means dynamic attribute resolution at source
  expression site `site` is expected to find `attrName`. -/
  | hasAttribute : SourceExpressionSite -> Identifier -> SourceObligation
  deriving DecidableEq, Repr
