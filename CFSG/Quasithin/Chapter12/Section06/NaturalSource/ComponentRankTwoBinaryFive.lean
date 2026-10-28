module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoSmallBinary
public import Theory.SpecificGroups.BinaryLinear.FiveSylowFixerCentralizer

/-!
# The binary linear-five exclusion in the original rank-two branch

Transport the same selected component, original involution and full Sylow
subgroup through the supplied PSL5 field model and its actual binary
linear equivalence. The faithful original E9 then lies in the full
centralizer of a pointwise Sylow fixer. The flag calculation proves that
centralizer has order indivisible by nine, excluding PSL5(2).

The resulting original-source endpoint retains only PSp4, G2, genuine
triality and ReeF4 at their original characteristic-two parameters. It
retains the literal three-core obstruction and every earlier geometry
hypothesis; it does not complete rank two or universal NaturalReduction.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- The actual binary linear-five component contradicts the original faithful E9. -/
theorem SourceHypothesis.original_rank_two_not_binaryLinearFive
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 5 2 := by
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let f := (e.trans (Atlas.fieldEquivPSL 5 eF)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 5) := Finite.of_equiv _ f.toEquiv
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer
    D hZ z hz hTV hTz hbound hH hn c a hTI hns hr f
  exact BinaryLinear.OuterCyclic.not_nine_dvd_sylow_fixer_centralizer_five P α hα hP h9

include hz hTV hTz hbound hH hn a in
/-- Four nonlinear characteristic-two families remain on the literal original component. -/
theorem SourceHypothesis.original_rank_two_nonlinear_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ((∃ f, 2 ≤ f ∧ ClassicalGroup.IsPSp B 2 (2^f)) ∨
        (∃ f, 2 ≤ f ∧ ClassificationModels.IsG2At B (2^f)) ∨
        (∃ f, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f) B) ∨
        (∃ m, 1 ≤ m ∧ Nonempty (B ≃* ReeF4.Model m))) := by
  obtain ⟨hcore,hmodels⟩ := S.original_rank_two_large_even_models D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  refine ⟨hcore,?_⟩
  rcases hmodels with h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (S.original_rank_two_not_binaryLinearFive D hZ z hz hTV hTz hbound hH hn c a hTI hns hr h).elim
end CFSG.Quasithin.Chapter12.Section06
