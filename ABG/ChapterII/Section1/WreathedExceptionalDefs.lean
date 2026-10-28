module
public import ABG.ChapterII.Section1.WreathedPresentation

/-!
# A chosen quaternion central product in a wreathed group

The exceptional nonabelian subgroup in ABG Chapter II §1 Lemma 3 (article
p.10) is a central product of a quaternion group and the ambient center.
The chosen quaternion generators are the quarter-power of r and d from the
presentation preceding Lemma 2. Their central join gives the fixed model V
used to state the classification, normalizer and conjugacy calculations.
These are actual subgroups of the original group; their quaternion and
central-product properties are proved in the model-identification module.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- The chosen quaternion core of the exceptional central product. -/
@[expose] public def quaternionCore : Subgroup S :=
  Subgroup.closure ({P.r ^ (2 ^ (n - 2)), P.d} : Set S)

/-- The chosen quaternion central product from Lemma 3. -/
@[expose] public def V : Subgroup S := P.quaternionCore ⊔ Subgroup.center S

end ABG.Wreathed.Presentation
