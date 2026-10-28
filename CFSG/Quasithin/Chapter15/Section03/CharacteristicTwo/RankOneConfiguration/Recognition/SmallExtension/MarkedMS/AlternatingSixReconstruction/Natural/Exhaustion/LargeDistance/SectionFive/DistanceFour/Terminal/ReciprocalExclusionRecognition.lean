module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSixMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Alternating-six recognition for the reciprocal FF section

The complete B.5.1 FF classification is irreducible at simple component
order 360. The B.4.2 catalogue then leaves the alternating-six natural case
and the derived binary symplectic case, identified by the explicit polar
model. The canonical moved-section transport retains the original ambient
actor and yields natural coordinates on its actual moved quotient.

This is the representation-theoretic recognition needed after the reciprocal
factorization argument of MS93 (5.12)(2), printed p.926; the source results
are Aschbacher--Smith B.4.2 and B.5.1.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource

private theorem triple_mono (a b c : ℕ) {q r : ℕ} (h : q ≤ r) :
    q ^ a * (q ^ b - 1) * (q ^ c - 1) ≤
      r ^ a * (r ^ b - 1) * (r ^ c - 1) := by
  gcongr

private theorem card_sl_two_ne_360 (F : Type*) [Field F] [Finite F] :
    Nat.card SL(2,F) ≠ 360 := by
  rw [Atlas.card_sl_two]
  intro hc
  by_cases hq : Nat.card F ≤ 7
  · have hb : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 7 * (7 ^ 2 - 1) := by
      gcongr
    norm_num at hb
    omega
  · have hb : 8 * (8 ^ 2 - 1) ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
      gcongr <;> omega
    norm_num at hb
    omega

private theorem card_sl_three_ne_360 (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) ≠ 360 := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  intro hc
  by_cases hq : Nat.card F ≤ 2
  · have hb := triple_mono 3 3 2 hq
    norm_num at hb
    omega
  · have hb := triple_mono 3 3 2 (show 3 ≤ Nat.card F by omega)
    norm_num at hb
    omega

private theorem card_sp_ne_360 (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.symplecticGroup (Fin 2) F) ≠ 360 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp]
  intro hc
  have hb := triple_mono 4 2 4 (show 2 ≤ Nat.card F from Finite.one_lt_card)
  norm_num at hb
  omega

private theorem card_g2_ne_360 (F : Type*) [Field F] [Finite F] :
    Nat.card (Atlas.G2.Model F) ≠ 360 := by
  rw [Atlas.G2.card_Model]
  intro hc
  have hb := triple_mono 6 6 2 (show 2 ≤ Nat.card F from Finite.one_lt_card)
  norm_num at hb
  omega

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem binary_higher_card_ne {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 360 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

private theorem alternating_card_ne {d : ℕ} (hd : d = 5 ∨ d = 7 ∨ d = 8) :
    Nat.card (alternatingGroup (Fin d)) ≠ 360 := by
  rcases hd with rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- At order 360 the source-correct B.4.2 list has precisely the natural
alternating-six natural action. -/
theorem irreducible_card360_natural
    (ρ : Representation (ZMod 2) G V) (L H : Subgroup G)
    (hc : Nat.card L = 360)
    (hs : CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    Nonempty (ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6)) := by
  cases hs with
  | linearTwo F _ e _ _ =>
    exact (card_sl_two_ne_360 F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | linearThree F _ e _ =>
    exact (card_sl_three_ne_360 F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | symplectic F _ _ e _ =>
    exact (card_sp_ne_360 F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | symplecticTwo e _ =>
    exact ExtensionConsequences.SymplecticTwo.marked_isAlternatingNatural e
  | g2 F _ _ e _ _ =>
    exact (card_g2_ne_360 F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | g2Two e _ _ =>
    have he := (Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
    omega
  | symmetric d hd e _ _ =>
    exact (alternating_card_ne (by rcases hd with h|h <;> simp [h])
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc)).elim
  | alternatingSix _ e _ _ => exact ⟨e⟩
  | alternatingSeven _ _ e _ _ _ =>
    exact (alternating_card_ne (by simp)
      ((Nat.card_congr e.toEquiv).symm.trans hc)).elim
  | tripleSix _ a _ =>
    have hq := Nat.card_congr a.quotientEquiv.toEquiv
    have hz := Nat.card_congr a.centerEquiv.toEquiv
    have hh := card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hq,hz,hc,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  | binaryLinear d hd _ e _ =>
    exact (binary_higher_card_ne hd
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | orthogonalSix _ _ e _ _ =>
    exact (alternating_card_ne (by simp)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | symmetricEight _ e _ =>
    exact (alternating_card_ne (by simp)
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc)).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (binary_higher_card_ne (by simp)
      ((Nat.card_congr e.toEquiv).symm.trans hc)).elim

variable [Module.Finite (ZMod 2) V]

/-- The full FF classification recognizes the actual moved space modulo its
fixed part, allowing an ambient actor larger than the simple component. -/
theorem ff_card360_moved_natural
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hc : Nat.card L = 360) (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) ∧
      Nonempty (ActionEquiv ((MovedSection.ofNormal ρ L).action.comp L.subtype)
        (alternatingNatural 6)) := by
  obtain ⟨hLJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc' : Nat.card (L.subgroupOf (offenderSubgroup ρ)) = 360 :=
    (Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv).trans hc
  cases c.clause_one with
  | irreducible hi _ _ hs _ =>
    have hi' := hi
    rw [c.sectionData.space_eq] at hi'
    change IsIrrPlus _ _ (moved (ρ.comp (offenderSubgroup ρ).subtype)
      (L.subgroupOf (offenderSubgroup ρ))) at hi'
    rw [moved_comp_map,map_subgroupOf_eq_of_le hLJ] at hi'
    have hi'' := (IsIrrPlus.subgroupOf_iff ρ L (offenderSubgroup ρ) hLJ _).mp hi'
    obtain ⟨E⟩ := irreducible_card360_natural _ _ _ hc' hs
    let D := L.subgroupOf (offenderSubgroup ρ)
    let φ : L ≃* D := (subgroupOfEquivOfLe hLJ).symm
    have hm : (moved ρ L).map (LinearMap.id : V →ₗ[ZMod 2] V) =
        moved (ρ.comp (offenderSubgroup ρ).subtype) D := by
      rw [Submodule.map_id,moved_comp_map,map_subgroupOf_eq_of_le hLJ]
    let T := c.sectionData.componentEmbeddingEquiv (MovedSection.ofNormal ρ L) φ
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ h => h) (fun _ _ => rfl) hm
    refine ⟨hi'',⟨?_⟩⟩
    exact ⟨T.groupEquiv.trans E.groupEquiv,T.linearEquiv.trans E.linearEquiv,
      fun g v => by
        change E.linearEquiv (T.linearEquiv (_)) = _
        rw [T.intertwines,E.intertwines]
        rfl⟩
  | doubleThree F _ e _ _ =>
    exact (card_sl_three_ne_360 F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne hd
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne hd
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalRecognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
