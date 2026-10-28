module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.BorelCubic.Standard
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.Placement
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# Cubic unitary Borel actions are inner

For q = 2^n congruent to −1 modulo three, a cubic unitary conjugation
preserving a PSU₃(q) Borel of order divisible by three is inner.
The standard matrix calculation is proved in `BorelCubic.Standard`.
Here an actual Hermitian basis change and a special-unitary lift of a
Sylow conjugator transport the given Borel to that standard Borel.
The same matrix conjugates the actor, so its cubic relation, Borel
invariance and innerness transport along the specified PSU equivalence.

This proves exactly `UnitaryLocal.CubicBorelAction`, including arbitrary
nondegenerate Hermitian forms. The order condition concerns the induced
automorphism; no order-three hypothesis is imposed on its matrix lift.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the final
paragraph of 15.3.37, printed p.1135. The Borel geometry is F.1.3(1),
with actual matrices from Huppert II.10.12.
-/

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Subgroup
open BenderSuzuki.MatrixGroups.HermitianForm
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal
namespace BorelCubic
variable {F : Type*} [Field F]

private theorem unitary_basis_change (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (FormTransport.standardForm J).form)
    (u : J.unitarySubgroup) : C⁻¹ * u.val * C ∈ (FormTransport.standardForm J).unitarySubgroup := by
  have adj_mul (A B : Matrix (Fin 3) (Fin 3) F) :
      J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
    change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
    rw [map_mul, transpose_mul]
    rfl
  have adj_one : J.conjTranspose 1 = 1 := by
    change ((J.conj : F →+* F).mapMatrix 1).transpose = _
    rw [map_one, transpose_one]
  have hcancel : J.conjTranspose (C⁻¹).val * J.conjTranspose C.val = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change J.conjTranspose (C⁻¹ * u.val * C).val * (FormTransport.standardForm J).form *
    (C⁻¹ * u.val * C).val = (FormTransport.standardForm J).form
  rw [← hC]
  simp only [Units.val_mul, adj_mul]
  calc
    _ = J.conjTranspose C.val * J.conjTranspose u.val.val *
        (J.conjTranspose (C⁻¹).val * J.conjTranspose C.val) * J.form *
        (C.val * (C⁻¹).val) * u.val.val * C.val := by simp only [mul_assoc]
    _ = J.conjTranspose C.val * (J.conjTranspose u.val.val * J.form * u.val.val) *
        C.val := by rw [hcancel, Units.mul_inv]; simp only [mul_one, mul_assoc]
    _ = _ := by rw [(J.mem_unitarySubgroup_iff _).mp u.property]

private theorem conjugation_transport (J K : HermitianForm 3 F)
    (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup K)
    (C : GL (Fin 3) F)
    (he : ∀ x, (e x).val = (ProjGenLinGroup.mk C)⁻¹ * x.val * ProjGenLinGroup.mk C)
    (u : J.unitarySubgroup) (v : K.unitarySubgroup)
    (hv : v.val = C⁻¹ * u.val * C) :
    MulAut.congr e (J.unitaryConjHom u) = K.unitaryConjHom v := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [J.unitaryConjHom_apply, K.unitaryConjHom_apply]
  change e (J.unitaryConj u (e.symm (e x))) = K.unitaryConj v (e x)
  rw [e.symm_apply_apply]
  apply Subtype.ext
  rw [he, J.unitaryConj_apply_val, K.unitaryConj_apply_val, he, hv]
  simp only [map_mul, map_inv]
  group

private theorem invariant_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (α : MulAut G)
    (hA : A.map α.toMonoidHom = A) :
    (A.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = A.map e.toMonoidHom := by
  have he : (MulAut.congr e α).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp α.toMonoidHom := by
    ext x
    exact congrArg e (congrArg α (e.symm_apply_apply x))
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hA]

end BorelCubic

/-- Cubic unitary conjugations preserving a Borel whose order is divisible by
three are inner, for every Hermitian form and every Sylow two-subgroup. -/
public theorem cubicBorelAction (n : ℕ) (hn : 0 < n) (hq : 2 ^ n % 3 = 2) :
    CubicBorelAction n := by
  intro F _ _ J hcard hconj
  dsimp only
  intro T d h3 hd hB
  classical
  let J0 := FormTransport.standardForm J
  let B := normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  let B0 := BorelTorus.projectiveBorel J0 rfl
  obtain ⟨C, hC, g, hBmatrix⟩ := psu_sylow_normalizer_eq_matrix_borel J n hn hcard hconj T
  let e0 := FormTransport.projectiveEquiv J C hC
  let e := e0.trans (MulAut.conj g).symm
  have hBe : B.map e.toMonoidHom = B0 := by
    rw [show B = (B0.map (MulAut.conj g).toMonoidHom).comap e0.toMonoidHom from hBmatrix]
    change ((B0.map (MulAut.conj g).toMonoidHom).comap e0.toMonoidHom).map
      ((MulAut.conj g).symm.toMonoidHom.comp e0.toMonoidHom) = B0
    rw [← Subgroup.map_map, map_comap_eq_self_of_surjective e0.surjective, Subgroup.map_map]
    have heq : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact (MulAut.conj g).symm_apply_apply x
    rw [heq, Subgroup.map_id]
  let d0 : J0.unitarySubgroup := ⟨C⁻¹ * d.val * C,
    BorelCubic.unitary_basis_change J C hC d⟩
  obtain ⟨a, ha⟩ := J0.specialToProjective_surjective g
  let au : J0.unitarySubgroup := ⟨a.val, a.property.1⟩
  let v := au⁻¹ * d0 * au
  have heformula (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      (e x).val = (ProjGenLinGroup.mk (C * a.val))⁻¹ * x.val *
        ProjGenLinGroup.mk (C * a.val) := by
    change (g⁻¹ * e0 x * g).val = _
    change g.val⁻¹ * (e0 x).val * g.val = _
    rw [← ha, J0.specialToProjective_apply_val, FormTransport.projectiveEquiv_apply]
    simp [map_mul, mul_assoc]
  have hv : v.val = (C * a.val)⁻¹ * d.val * (C * a.val) := by
    change a.val⁻¹ * (C⁻¹ * d.val * C) * a.val = _
    group
  have heact : MulAut.congr e (J.unitaryConjHom d) = J0.unitaryConjHom v :=
    BorelCubic.conjugation_transport J J0 e (C * a.val) heformula d v hv
  have hv3 : (J0.unitaryConjHom v) ^ 3 = 1 := by
    rw [← heact, ← map_pow, hd, map_one]
  have hBv : B0.map (J0.unitaryConjHom v).toMonoidHom = B0 := by
    rw [← heact, ← hBe]
    exact BorelCubic.invariant_map e B (J.unitaryConjHom d) hB
  have hB3 : 3 ∣ Nat.card B0 := by
    rw [← hBe, card_map_of_injective e.injective]
    exact h3
  have hinner := BorelCubic.standard_cubic_borel_action J0 n hn hq hcard hconj rfl v
    hB3 hv3 hBv
  rw [← heact, ← MulAut.map_innerSubgroup_congr e] at hinner
  obtain ⟨α, hα, hαe⟩ := hinner
  exact (MulAut.congr e).injective hαe ▸ hα

end CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal
