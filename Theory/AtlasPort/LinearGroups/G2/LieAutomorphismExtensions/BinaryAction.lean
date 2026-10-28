module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the actual binary derived group

The binary carrier here is literally the commutator subgroup of the full
split-octonion group. The checked long-root/sign calculation identifies it
and gives its order 6048; the full group has order 12096.

Conjugation defines an actual homomorphism from the full group to the
automorphisms of this derived subgroup. The sign character factors every
full-group element as a derived-group element times a Borel element. Hence
its conjugation action preserves both parabolic types of the derived group,
with one common inner conjugation for the whole marked pair. This is the
inherited G₂ point/line convention used for the Dynkin action in the source.

Bijectivity of this conjugation homomorphism is a separate, still required
binary automorphism theorem. The constructions and type-preservation result
here do not assert that automorphism identification or extension exclusion.

Source: Aschbacher--Smith, F.1.12 printed pp.263--264 and Definition F.4.3
printed p.274. The binary sign and derived-group calculations are imported
from the licensed ATLAS model and its checked extensions.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open LieParabolicSetup

abbrev BinaryDerived := commutator (Model (ZMod 2))

def binaryConjugation : Model (ZMod 2) →* MulAut BinaryDerived := MulAut.conjNormal

@[simp] theorem binaryConjugation_apply (g : Model (ZMod 2)) (x : BinaryDerived) :
    (binaryConjugation g x).val = g * x.val * g⁻¹ := rfl

theorem binaryDerived_eq : BinaryDerived = BinaryException.H :=
  BinaryParabolicPair.commutator_eq_longRootClosure

theorem card_binaryDerived : Nat.card BinaryDerived = 6048 := by
  rw [binaryDerived_eq]
  exact BinaryException.card_H

theorem card_binaryFull : Nat.card (Model (ZMod 2)) = 12096 := by
  rw [card_Model, Nat.card_eq_fintype_card, ZMod.card]
  norm_num

/-- The two labeled full parabolics, restricted to the actual derived subgroup. -/
def binaryMarkedParabolic (i : Fin 2) : Subgroup BinaryDerived :=
  (if i = 0 then parabolic₁ else parabolic₂).subgroupOf BinaryDerived

theorem binaryConjugation_map_subgroupOf (g : Model (ZMod 2))
    (P : Subgroup (Model (ZMod 2))) :
    (P.subgroupOf BinaryDerived).map (binaryConjugation g).toMonoidHom =
      (P.map (MulAut.conj g).toMonoidHom).subgroupOf BinaryDerived := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    change g * y * g⁻¹ = x.val at he
    have hyD : y ∈ BinaryDerived := by
      have hxD := (inferInstance : BinaryDerived.Normal).conj_mem x.val x.property g⁻¹
      have he' : g⁻¹ * x.val * g = y := by
        rw [← he]
        simp [mul_assoc]
      simpa only [inv_inv, he'] using hxD
    refine ⟨⟨y, hyD⟩, hy, ?_⟩
    apply Subtype.ext
    exact he

/-- Conjugation transports each labeled parabolic family without exchanging its label. -/
theorem binaryConjugation_marked (g : Model (ZMod 2)) (i : Fin 2) :
    (binaryMarkedParabolic i).map (binaryConjugation g).toMonoidHom =
      ((if i = 0 then parabolic₁ else parabolic₂).map
        (MulAut.conj g).toMonoidHom).subgroupOf BinaryDerived :=
  binaryConjugation_map_subgroupOf g _

@[simp] theorem binaryConjugation_inner (h : BinaryDerived) :
    binaryConjugation h.val = MulAut.conj h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

theorem binary_borel_supplement (g : Model (ZMod 2)) :
    ∃ (h : BinaryDerived) (b : borel (K := ZMod 2)), g = h.val * b.val := by
  have hmem (x : Model (ZMod 2)) (hx : Binary.lineSign x = 1) : x ∈ BinaryDerived := by
    rw [binaryDerived_eq, ← BinaryException.lineSign_kernel]
    exact hx
  rcases Int.units_eq_one_or (Binary.lineSign g) with h | h
  · exact ⟨⟨g, hmem g h⟩, 1, (mul_one g).symm⟩
  · have hb : rootF (1 : ZMod 2) ∈ borel :=
      Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    refine ⟨⟨g * (rootF 1)⁻¹, hmem _ ?_⟩, ⟨rootF 1, hb⟩, ?_⟩
    · rw [map_mul, map_inv, h, Binary.lineSign_rootF_one]
      exact mul_inv_cancel _
    · exact (inv_mul_cancel_right g (rootF 1)).symm

theorem binaryConjugation_borel_fixes (b : borel (K := ZMod 2)) (i : Fin 2) :
    (binaryMarkedParabolic i).map (binaryConjugation b.val).toMonoidHom =
      binaryMarkedParabolic i := by
  let P : Subgroup (Model (ZMod 2)) := if i = 0 then parabolic₁ else parabolic₂
  have hBP : borel (K := ZMod 2) ≤ P := by
    dsimp [P]
    split
    · exact borel_le_parabolic₁
    · exact borel_le_parabolic₂
  change (P.subgroupOf BinaryDerived).map _ = P.subgroupOf BinaryDerived
  rw [binaryConjugation_map_subgroupOf]
  have hn := P.le_normalizer (hBP b.property)
  have he : P.map (MulAut.conj b.val).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  exact congrArg (fun Q : Subgroup (Model (ZMod 2)) => Q.subgroupOf BinaryDerived) he

/-- Every ambient conjugation preserves the two parabolic types of the derived group,
with one common derived-group conjugation for the whole marked pair. -/
theorem binaryConjugation_preserves_marked_types (g : Model (ZMod 2)) :
    ∃ h : BinaryDerived, ∀ i : Fin 2,
      (binaryMarkedParabolic i).map (binaryConjugation g).toMonoidHom =
        (binaryMarkedParabolic i).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h, b, rfl⟩ := binary_borel_supplement g
  refine ⟨h, fun i => ?_⟩
  rw [map_mul]
  change (binaryMarkedParabolic i).map
    ((binaryConjugation h.val).toMonoidHom.comp (binaryConjugation b.val).toMonoidHom) = _
  rw [← Subgroup.map_map, binaryConjugation_borel_fixes, binaryConjugation_inner]

end Atlas.G2.LieAutomorphismExtensions
