module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.Coordinates
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The classifier action on the actual seed span

The faithful plus action on W_K is linearized over F₂. Its component moved
space is exactly U_K = [W_K,K], with an explicit group equivalence. Under
this equivalence the classifier's central submodule is precisely C_UK(K).
Thus the quotient in a natural-module alternative remains a genuine quotient;
no identification of that quotient with U_K is made.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the paragraph
preceding 13.6.14 and the proof of 13.6.20, printed pp.929 and 931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

noncomputable def wkRepresentation :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive (WK K L T z v)) where
  toFun g := (plusAction K L T z v hL hz g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (plusAction K L T z v hL hz 1 w.toMul) = w
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (plusAction K L T z v hL hz (g * h) w.toMul) = _
    rw [map_mul]
    rfl

theorem wkRepresentation_faithful : Function.Injective (wkRepresentation K L T z v hL hz) := by
  intro g h he
  apply plusAction_injective K L T z v hL hz
  apply MulEquiv.ext
  intro w
  exact congrArg Additive.toMul (LinearMap.congr_fun he (Additive.ofMul w))

theorem wkRepresentation_apply (g : plusActor K L T v) (w : Additive (WK K L T z v)) :
    ((wkRepresentation K L T z v hL hz (plusMk K L T z v hL hz g) w).toMul : G) =
      (g : G) * (w.toMul : G) * (g : G)⁻¹ := rfl

include hL hz in
omit [IsElementaryAbelian 2 (WK K L T z v)] in
theorem UK_le_WK : UK K L T z v ≤ WK K L T z v := by
  rw [UK, commutator_comm]
  exact (le_normalizer_iff_commutator_le_right).mp
    ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))

noncomputable def ukSubspace : Submodule (ZMod 2) (Additive (WK K L T z v)) :=
  AddSubgroup.toZModSubmodule 2 ((UK K L T z v).subgroupOf (WK K L T z v)).toAddSubgroup

theorem moved_eq_ukSubspace :
    moved (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K) =
      ukSubspace K L T z v := by
  let ρ := wkRepresentation K L T z v hL hz
  let I := moved ρ (plusImage K L T z v hL hz K)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨k, hk, rfl⟩, w, _, rfl⟩
    change (((ρ (plusMk K L T z v hL hz k) w).toMul : G) / (w.toMul : G)) ∈ UK K L T z v
    rw [wkRepresentation_apply, div_eq_mul_inv]
    rw [UK, commutator_comm]
    exact commutator_mem_commutator hk w.toMul.property
  · have hle : UK K L T z v ≤ I.toAddSubgroup.toSubgroup'.map (WK K L T z v).subtype := by
      rw [UK, commutator_comm]
      apply commutator_le.mpr
      intro k hk w hw
      let k' : plusActor K L T v := ⟨k, K_le_plusActor K L T v hk⟩
      let w' : Additive (WK K L T z v) := Additive.ofMul ⟨w, hw⟩
      refine ⟨(ρ (plusMk K L T z v hL hz k') w' - w').toMul, ?_, ?_⟩
      · change ρ (plusMk K L T z v hL hz k') w' - w' ∈ I
        exact Submodule.subset_span ⟨_, mem_map_of_mem _ hk, w', Submodule.mem_top, rfl⟩
      · change ((ρ (plusMk K L T z v hL hz k') w').toMul : G) / w = _
        rw [wkRepresentation_apply, div_eq_mul_inv]
        rfl
    intro w hw
    obtain ⟨u, hu, he⟩ := hle hw
    have he' : Additive.ofMul u = w := congrArg Additive.ofMul (Subtype.ext he)
    exact he' ▸ hu

noncomputable def movedEquivUK (s : MovedSection (wkRepresentation K L T z v hL hz)
    (plusImage K L T z v hL hz K)) :
    Multiplicative s.space.toSubmodule ≃* UK K L T z v where
  toFun w := ⟨w.toAdd.val.toMul,
    by exact (moved_eq_ukSubspace K L T z v hL hz).le (s.space_eq.le w.toAdd.property)⟩
  invFun u := Multiplicative.ofAdd ⟨Additive.ofMul ⟨u, UK_le_WK K L T z v hL hz u.property⟩,
    by rw [s.space_eq, moved_eq_ukSubspace]; exact u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The classifier's central submodule is exactly C_UK(K), under the
underlying identification of its moved space with U_K. -/
theorem mem_sectionCentral_iff (hK : K ≤ Gv v)
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) (w : s.space.toSubmodule) :
    w ∈ s.central.toSubmodule ↔ (w.val.toMul : G) ∈ centralizer (K : Set G) := by
  rw [s.central_eq]
  constructor
  · intro hw
    apply mem_centralizer_iff.mpr
    intro k hk
    have he := congrArg (fun x : s.space.toSubmodule => (x.val.toMul : G))
      (hw (componentPlus K L T z v hK hL hz ⟨k, hk⟩))
    change ((wkRepresentation K L T z v hL hz
      (componentPlus K L T z v hK hL hz ⟨k, hk⟩) w.val).toMul : G) = _ at he
    rw [componentPlus_apply, wkRepresentation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hw c
    obtain ⟨k, rfl⟩ := componentPlus_surjective K L T z v hK hL hz c
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((wkRepresentation K L T z v hL hz
      (componentPlus K L T z v hK hL hz k) w.val).toMul : G) = _
    rw [componentPlus_apply, wkRepresentation_apply]
    change (k : G) * (w.val.toMul : G) * (k : G)⁻¹ = (w.val.toMul : G)
    rw [mem_centralizer_iff.mp hw k k.property, mul_inv_cancel_right]


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
