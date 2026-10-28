module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases

/-!
# The ordinary HS component case of A.3.6

The proved odd-primary multiplier calculation makes the center of a finite
perfect group with the literal degree-100 HS central quotient a two-group.
For the source ordinary component with O₂(L)=1, its center is therefore
trivial. The original central-quotient map becomes an isomorphism and supplies
the simple HS alternative. The shared quasisimple result supplies every
common Fitting, radical and quotient clause of A.3.6.

The model is precisely the carrier in the source's sporadic list. Simplicity
is inherited from the component's central quotient; neither a comparison
with another HS model nor an exact two-primary multiplier bound is needed.
The earlier A.2.19 odd-center exclusion is already proved in `HSUpperBound`.

Source: Aschbacher–Smith A.3.6, printed pp.43–46, and I.1.1–I.1.3,
printed pp.407–408.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.HSOddCoverCase
open Chapter1.Section02 Chapter1.Section02.LocalModels
open Sporadic.LeechRelated.HS

/-- The complete A.3.6 conclusion for an ordinary component with trivial
two-core and the specified actual HS central quotient. -/
theorem a36_hs {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Carrier) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Carrier := e.symm.isSimpleGroup
  have hz2 : IsPGroup 2 (center L) :=
    Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e
  have hz : center L = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance, hz2⟩
  let f : L →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hk : f.ker = ⊥ := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk', hz]
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  let j : L ≃* Carrier := MulEquiv.ofBijective f ⟨f.ker_eq_bot_iff.mp hk, hf⟩
  have heven : 2 ∣ Nat.card L := (Nat.card_congr j.toEquiv).symm ▸
    (show 2 ∣ Nat.card Carrier by rw [NormalizerIndex.card_carrier]; norm_num)
  exact ⟨.simple hL j.isSimpleGroup (.sporadic .hs (by intro h; cases h) ⟨j⟩),
    ReadyCoverCases.common_of_quasisimple heven (Or.inl (by rw [hz]; simp))⟩

end CFSG.Quasithin.ChapterA.SQTKStructure.HSOddCoverCase
