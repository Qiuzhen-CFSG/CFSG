module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.FastDot

/-!
# Assemble packed certificates without reducing their numerical goals

The list identities are proved here with variable data. Concrete certificates
then apply these lemmas directly, avoiding simplification of closed Boolean
propositions during the assembly of the degree-896 HS checks.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed

theorem checkRows_drop_split (a b c : Mat) (i n : ℕ)
    (h₁ : checkRows ((a.drop i).take n) b ((c.drop i).take n) = true)
    (h₂ : checkRows (a.drop (i + n)) b (c.drop (i + n)) = true) :
    checkRows (a.drop i) b (c.drop i) = true :=
  checkRows_split _ _ _ n h₁ (by simpa only [List.drop_drop] using h₂)

theorem checkDots_drop_split (k d : ℕ) (b : Row) (a : Mat) (i n : ℕ)
    (h₁ : checkDots k d b ((a.drop i).take n) = true)
    (h₂ : checkDots k d b (a.drop (i + n)) = true) :
    checkDots k d b (a.drop i) = true :=
  checkDots_split _ _ _ _ n h₁ (by simpa only [List.drop_drop] using h₂)

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
