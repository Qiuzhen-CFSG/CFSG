module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.ModelCalculations

/-!
The fixed plane in the orthogonal Sylow actor.

For the literal action of SL₂(2) wr C₂ on the sum of two definite planes,
every nontrivial normal subgroup of a Sylow 2-subgroup contains its central
involution. Its fixed space therefore lies in the base subgroup's fixed plane,
and the pointwise stabilizer of that plane inside the Sylow group is the base
subgroup itself. We check these assertions in the standard dihedral Sylow group
and transport them by Sylow conjugacy. These are the model facts used in
Aschbacher–Smith, The Classification of Quasithin Groups, original 15.3.51(2).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.OrthogonalGeometry.Source50Model
open Subgroup
open scoped IsMulCommutative Pointwise
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction
private instance : DecidableEq OrthogonalActor := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm

abbrev planePart (P : Subgroup OrthogonalActor) : Subgroup OrthogonalActor :=
  P ⊓ (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex).ker

/-- Every nontrivial subgroup normalized by the standard Sylow contains its central involution. -/
theorem standard_center_mem (R : Subgroup OrthogonalActor)
    (hle : R ≤ wreathTwoDihedralHom.range)
    (hn : wreathTwoDihedralHom.range ≤ normalizer (R : Set OrthogonalActor))
    (hne : R ≠ ⊥) : wreathTwoDihedralHom (DihedralGroup.r 2) ∈ R := by
  have hc : ∀ x : DihedralGroup 4, x ≠ 1 →
      x = DihedralGroup.r 2 ∨ x ^ 2 = DihedralGroup.r 2 ∨
        ∃ y : DihedralGroup 4, y*x*y⁻¹*x⁻¹ = DihedralGroup.r 2 := by decide +kernel
  obtain ⟨x, hx, hx1⟩ := R.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨a, rfl⟩ := hle hx
  have ha : a ≠ 1 := fun he => hx1 (by rw [he, map_one])
  rcases hc a ha with he | he | ⟨b, he⟩
  · rwa [← he]
  · rw [← he, map_pow]; exact R.pow_mem hx 2
  · rw [← he, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact R.mul_mem ((hn ⟨b, rfl⟩ _).mp hx) (R.inv_mem hx)

private theorem standard_fixed_bound (R : Subgroup OrthogonalActor)
    (hle : R ≤ wreathTwoDihedralHom.range)
    (hn : wreathTwoDihedralHom.range ≤ normalizer (R : Set OrthogonalActor))
    (hne : R ≠ ⊥) : fixedVectors R ≤ fixedVectors (planePart wreathTwoDihedralHom.range) := by
  have hc : ∀ v : OrthogonalVector,
      wreathTwoDihedralHom (DihedralGroup.r 2) • v = v →
      ∀ x : DihedralGroup 4, (wreathTwoDihedralHom x).right = 1 →
        wreathTwoDihedralHom x • v = v := by decide +kernel
  intro v hv x hx
  obtain ⟨⟨a, rfl⟩, ha⟩ := hx
  exact hc v (hv _ (standard_center_mem R hle hn hne)) a ha

/-- Conjugation preserves the base-kernel part of an actor subgroup. -/
theorem planePart_conj (P : Subgroup OrthogonalActor) (g : OrthogonalActor) :
    planePart (P.map (MulAut.conj g).toMonoidHom) =
      (planePart P).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    change (g*y*g⁻¹).right = 1 at hx
    change y.right = 1
    simpa [mul_comm] using hx
  · rintro ⟨y, ⟨hy, hr⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    change y.right = 1 at hr
    change (g*y*g⁻¹).right = 1
    simp [hr]

/-- Literal actor conjugation transports fixed vectors through its vector action. -/
theorem fixed_conj (P : Subgroup OrthogonalActor) (g : OrthogonalActor)
    (v : OrthogonalVector) :
    g • v ∈ fixedVectors (P.map (MulAut.conj g).toMonoidHom) ↔ v ∈ fixedVectors P := by
  constructor
  · intro hv x hx
    apply MulAction.injective g
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, mul_smul, inv_smul_smul]
      using hv _ ⟨x, hx, rfl⟩
  · rintro hv _ ⟨x, hx, rfl⟩
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, mul_smul, inv_smul_smul]
      using congrArg (fun w : OrthogonalVector => g • w) (hv x hx)

/-- A nontrivial normal subgroup of the Sylow actor fixes vectors only in the
plane fixed by its base subgroup. -/
theorem fixedVectors_le_plane_fixed (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) (hle : R ≤ P)
    (hn : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor))
    (hne : R ≠ ⊥) : fixedVectors R ≤ fixedVectors (planePart P) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor P wreathTwoSylow
  let e := (MulAut.conj g).toMonoidHom
  have hP : (P : Subgroup OrthogonalActor).map e = wreathTwoDihedralHom.range := by
    have he := congrArg (fun Q : Sylow 2 OrthogonalActor => (Q : Subgroup OrthogonalActor)) hg
    rw [Sylow.coe_subgroup_smul, wreathTwoSylow_coe] at he
    exact he
  have hR : R.map e ≠ ⊥ := fun h => hne (by
    apply Subgroup.map_injective (f := e) (MulAut.conj g).injective
    simpa only [Subgroup.map_bot] using h)
  have hf := standard_fixed_bound (R.map e) (hP ▸ map_mono hle)
    (hP ▸ (map_mono hn).trans (le_normalizer_map _)) hR
  intro v hv
  have hv' := hf ((fixed_conj R g v).mpr hv)
  rw [← hP, planePart_conj] at hv'
  exact (fixed_conj (planePart P) g v).mp hv'

private theorem standard_pointwise :
    wreathTwoDihedralHom.range ⊓ pointwise (fixedVectors (planePart wreathTwoDihedralHom.range)) =
      planePart wreathTwoDihedralHom.range := by
  apply le_antisymm
  · rintro x ⟨⟨a, rfl⟩, ha⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    have hc : ∀ a : DihedralGroup 4,
        (∀ v : OrthogonalVector, (∀ b : DihedralGroup 4,
          (wreathTwoDihedralHom b).right = 1 → wreathTwoDihedralHom b • v = v) →
          wreathTwoDihedralHom a • v = v) → (wreathTwoDihedralHom a).right = 1 := by
      decide +kernel
    exact hc a (fun v hv => ha v (by rintro _ ⟨⟨b, rfl⟩, hb⟩; exact hv b hb))
  · intro x hx
    exact ⟨hx.1, fun v hv => hv x hx⟩

/-- The pointwise stabilizer of the fixed plane inside the Sylow actor is its
plane-preserving subgroup. -/
theorem pointwise_plane_fixed (P : Sylow 2 OrthogonalActor) :
    (P : Subgroup OrthogonalActor) ⊓ pointwise (fixedVectors (planePart P)) = planePart P := by
  apply le_antisymm
  · rintro x ⟨hx, hfix⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq OrthogonalActor P wreathTwoSylow
    let e := (MulAut.conj g).toMonoidHom
    have hP : (P : Subgroup OrthogonalActor).map e = wreathTwoDihedralHom.range := by
      have he := congrArg (fun Q : Sylow 2 OrthogonalActor => (Q : Subgroup OrthogonalActor)) hg
      rw [Sylow.coe_subgroup_smul, wreathTwoSylow_coe] at he
      exact he
    have hx' : e x ∈ planePart wreathTwoDihedralHom.range := by
      rw [← standard_pointwise]
      refine ⟨hP ▸ mem_map_of_mem e hx, ?_⟩
      intro v hv
      have hv' : g⁻¹ • v ∈ fixedVectors (planePart P) := by
        apply (fixed_conj (planePart P) g (g⁻¹ • v)).mp
        rw [← planePart_conj, hP, smul_inv_smul]
        exact hv
      have he := congrArg (fun w : OrthogonalVector => g • w) (hfix _ hv')
      simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul,
        smul_inv_smul] using he
    rw [← hP, planePart_conj] at hx'
    exact (mem_map_iff_mem (MulAut.conj g).injective).mp hx'
  · intro x hx
    exact ⟨hx.1, fun v hv => hv x hx⟩

end CFSG.Quasithin.Chapter15.Section03.OrthogonalGeometry.Source50Model
