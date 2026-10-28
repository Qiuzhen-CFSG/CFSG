module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.Reductions

/-!
# The mutually normalizing case of orthogonal weak-closure centralization

If an actor preserves each of the two definite planes and every displacement
is singular, each displacement supported on a single plane must vanish.
The actor is therefore trivial. The finite calculation below checks this in
the literal matrix-and-coordinate-permutation action.

Compatibility transports singular ambient commutators to that calculation.
Consequently the induced action embeds in the plane-swap group of order two,
so `C_A(V)` has index at most two in `A`. For a noncentralizing whole conjugate,
its order would be at least eight. The inverse-conjugation displacement
argument in `Reductions` bounds its order by four, giving the contradiction.
This is the rank-one automizer/transvection contradiction of the first
source case, expressed through the two incompatible fixed-subgroup orders.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first case
in the proof of 15.3.46(4), printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
open Subgroup
attribute [local instance] orthogonalAction
private instance : DecidableEq OrthogonalActor :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- A plane-preserving actor whose displacements are all singular is trivial. -/
theorem eq_one_of_singular_displacements_of_shift_one :
    ∀ a : OrthogonalActor, a.right = 1 →
      (∀ v : OrthogonalVector, orthogonalCoordinateValue ((a • v) / v) = 0) → a = 1 := by
  decide +kernel

variable {G : Type*} [Group G] {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- Singular commutators are singular displacements in the compatible coordinates. -/
theorem coordinate_displacements_singular
    (d : NaturalOrthogonalAction M V) (k : OrthogonalCoordinateModel d P)
    {A : Subgroup G} (hAM : A ≤ M) (hs : IsTotallySingular d.form ⁅V, A⁆) (a : A) :
    ∀ w : OrthogonalVector,
      orthogonalCoordinateValue ((k.action.actor ⟨a, hAM a.property⟩ • w) / w) = 0 := by
  intro w
  obtain ⟨v, rfl⟩ := k.action.coordinates.surjective w
  rw [← k.action.compatible, ← map_div, ← k.form_eq]
  apply hs.2
  simp only [div_eq_mul_inv]
  change (a : G) * (v : G) * (a : G)⁻¹ * (v : G)⁻¹ ∈ ⁅V, A⁆
  rw [commutator_comm]
  exact commutator_mem_commutator a.property v.property

/-- The actual action of such a subgroup factors faithfully through the plane swap. -/
theorem fixed_relIndex_le_two_of_singular_commutator [Finite G]
    (d : NaturalOrthogonalAction M V) (k : OrthogonalCoordinateModel d P)
    {A : Subgroup G} (hAM : A ≤ M) (hs : IsTotallySingular d.form ⁅V, A⁆) :
    (A ⊓ centralizer (V : Set G)).relIndex A ≤ 2 := by
  let f : A →* OrthogonalPlaneIndex :=
    RegularWreathProduct.rightHom.comp (k.action.actor.comp (Subgroup.inclusion hAM))
  have he : f.ker = (A ⊓ centralizer (V : Set G)).subgroupOf A := by
    ext a
    change f a = 1 ↔ (a : G) ∈ A ⊓ centralizer (V : Set G)
    constructor
    · intro ha
      have hid := eq_one_of_singular_displacements_of_shift_one _ ha
        (coordinate_displacements_singular d k hAM hs a)
      have hm : (⟨a, hAM a.property⟩ : M) ∈ k.action.actor.ker := hid
      rw [k.action.ker_actor] at hm
      exact ⟨a.property, hm⟩
    · intro ha
      have hm : (⟨a, hAM a.property⟩ : M) ∈ k.action.actor.ker := by
        rw [k.action.ker_actor]
        exact ha.2
      change RegularWreathProduct.rightHom (k.action.actor ⟨a, hAM a.property⟩) = 1
      rw [show k.action.actor ⟨a, hAM a.property⟩ = 1 from hm, map_one]
  change ((A ⊓ centralizer (V : Set G)).subgroupOf A).index ≤ 2
  rw [← he, index_ker]
  have hc := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  exact hc.trans_eq (by norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card])

/-- The mutually normalizing case of 15.3.46(4). The singular-displacement
bound gives a fixed subgroup of index at most two, whereas symmetry and
nondegeneracy give order at most four. -/
theorem conjugate_le_centralizer_of_normalizes [Finite G]
    {T : Sylow 2 G} (d : NaturalOrthogonalAction M V)
    (h : EarlierFusionInputs T M V P) (k : OrthogonalCoordinateModel d P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  by_contra hne
  have hgM : g ∉ M := by
    intro hg
    have he : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (h.normalizer_eq.le hg)
    apply hne
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hAM := hgT.trans h.sylow_le
  have hs := commutator_totallySingular_of_normalizes d h c g hgM hAM hn
  have hi := fixed_relIndex_le_two_of_singular_commutator d k hAM hs
  have hc := card_fixed_le_four d h c g hgT hne
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := A ⊓ centralizer (V : Set G)
  have hB : B ≤ A := inf_le_left
  have hmul := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at hmul
  change Nat.card B * B.relIndex A = Nat.card A at hmul
  have hA : Nat.card A = 16 := by
    rw [show A = V.map (MulAut.conj g).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj g).injective]
    exact k.action.card_vector
  rw [hA] at hmul
  change B.relIndex A ≤ 2 at hi
  change Nat.card B ≤ 4 at hc
  nlinarith

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
