module

public import Theory.SpecificGroups.ONan.Presentation.Marking
public import Theory.SpecificGroups.ONan.Presentation.CoverApplication

/-!
# A concrete involutory marking toward an O'Nan presentation

Four explicit conjugates of the original matrix generator A have order two
and generate `ONan.Model`. The original A and B are explicit words in that
family. In the actual perfect odd-primary central-cover problem, the unique
involutory lifts generate the cover and preserve all pairwise Coxeter relations.

This establishes the marking and its cover application only. A finite set of
relators whose normal closure is the word-evaluation kernel, and hence a marked
isomorphism from a finitely presented group, remain unproved. No completeness
assertion is made for Soicher's thesis candidates or the ATLAS semi-presentation.
See `Presentation/source/README.md` for the checked source boundary and proof idea.
-/
