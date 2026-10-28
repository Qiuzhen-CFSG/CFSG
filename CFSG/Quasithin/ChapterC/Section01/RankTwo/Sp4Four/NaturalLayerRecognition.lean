module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerOrders
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Natural recognition of the initial Sp4(4) layer

A faithful binary FF module with a self-centralizing simple normal component
of order 979200 has natural symplectic moved quotient over a field of order
four. The complete proved B.5.1 classification first excludes its reducible
rows by group order. The complete B.4.2 list then leaves only Sp4. Transport
through the offender-generated subgroup identifies that action with the
canonical section [V,L]/C_[V,L](L) for the original ambient group.

The fixed central layer is retained; no splitting or restriction on ambient
outer automorphisms is imposed.

Source: Aschbacher--Smith B.4.2 and B.5.1; Meierfrankenfeld--Stellmacher
(1993), (1.4), (1.5), and the initial module in (3.2)(vi).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem binary_higher_card_ne {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 979200 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

private theorem alternating_card_ne {d : ℕ} (hd : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8) :
    Nat.card (alternatingGroup (Fin d)) ≠ 979200 := by
  rcases hd with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- At the order of Sp₄(4), B.4.2 leaves precisely the natural symplectic row. -/
theorem irreducible_card_sp4_four_natural
    (ρ : Representation (ZMod 2) G V) (L H : Subgroup G)
    (hc : Nat.card L = 979200)
    (hs : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ∃ F : BinaryField, F.degree = 2 ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (binarySymplectic F)) := by
  cases hs with
  | linearTwo F _ e _ _ =>
    exact (card_sl_two_ne_sp4_four F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | linearThree F _ e _ =>
    exact (card_sl_three_ne_sp4_four F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | symplectic F _ _ e _ =>
    exact ⟨F,degree_eq_two_of_card_sp F
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc),⟨e⟩⟩
  | symplecticTwo e _ =>
    have hh := (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv, hc,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hh
    norm_num at hh
  | g2 F _ _ e _ _ =>
    exact (card_g2_ne_sp4_four F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | g2Two e _ _ =>
    have hh := (commutator (Atlas.G2.Model (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv, hc,Atlas.G2.card_Model] at hh
    norm_num at hh
  | symmetric d hd e _ _ =>
    exact (alternating_card_ne (by rcases hd with h|h <;> simp [h])
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc)).elim
  | alternatingSix _ e _ _ =>
    exact (alternating_card_ne (by simp)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
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

/-- The full FF classification recognizes the actual moved layer modulo its
fixed part, allowing an ambient group larger than the simple component. -/
theorem ff_card_sp4_four_moved_natural
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hc : Nat.card L = 979200) (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) ∧
      ∃ F : BinaryField, F.degree = 2 ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ L).action.comp L.subtype)
          (binarySymplectic F)) := by
  obtain ⟨hLJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc' : Nat.card (L.subgroupOf (offenderSubgroup ρ)) = 979200 :=
    (Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv).trans hc
  cases c.clause_one with
  | irreducible hi _ _ hs _ =>
    have hi' := hi
    rw [c.sectionData.space_eq] at hi'
    change IsIrrPlus _ _ (subspaceCommutator (ρ.comp (offenderSubgroup ρ).subtype) ⊤
      (L.subgroupOf (offenderSubgroup ρ))) at hi'
    change IsIrrPlus _ _ (moved (ρ.comp (offenderSubgroup ρ).subtype)
      (L.subgroupOf (offenderSubgroup ρ))) at hi'
    rw [moved_comp_map,map_subgroupOf_eq_of_le hLJ] at hi'
    have hi'' := (IsIrrPlus.subgroupOf_iff ρ L (offenderSubgroup ρ) hLJ _).mp hi'
    obtain ⟨F,hF,⟨E⟩⟩ := irreducible_card_sp4_four_natural _ _ _ hc' hs
    let D := L.subgroupOf (offenderSubgroup ρ)
    let φ : L ≃* D := (subgroupOfEquivOfLe hLJ).symm
    have hm : (moved ρ L).map (LinearMap.id : V →ₗ[ZMod 2] V) =
        moved (ρ.comp (offenderSubgroup ρ).subtype) D := by
      rw [Submodule.map_id,moved_comp_map,map_subgroupOf_eq_of_le hLJ]
    let T := c.sectionData.componentEmbeddingEquiv (MovedSection.ofNormal ρ L) φ
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ h => h) (fun _ _ => rfl) hm
    refine ⟨hi'',F,hF,⟨?_⟩⟩
    exact ⟨T.groupEquiv.trans E.groupEquiv,T.linearEquiv.trans E.linearEquiv,
      fun g v => by
        change E.linearEquiv (T.linearEquiv (_)) = _
        rw [T.intertwines,E.intertwines]
        rfl⟩
  | doubleThree F _ e _ _ =>
    exact (card_sl_three_ne_sp4_four F.Carrier
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne hd
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne hd
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc')).elim

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
