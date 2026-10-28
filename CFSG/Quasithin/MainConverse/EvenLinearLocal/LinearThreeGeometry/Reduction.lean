module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.Centralizers
public import Theory.GroupTheory.QuasithinBasic

/-!
# Reducing all projective two-locals to a matrix fixed-space calculation

Conjugate an arbitrary two-subgroup into the concrete UT₃ Sylow subgroup,
then lift it by intersecting its inverse image with the matrix UT₃ subgroup.
Trace invariance identifies its full projective normalizer with the image
of its matrix normalizer. A matrix normalizer cover consequently gives a
cover of every projective two-local. Maximality among two-locals upgrades
containment to equality with one of the full parabolics.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed pp.4 and 482.
The geometric fixed-space input is an explicit premise in this module.
These conditional reductions do not assert that input or the source theorem.
-/

public section
open scoped MatrixGroups Pointwise
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.RootPlaneGeometry
namespace CFSG.Quasithin.MainConverse.LinearThreeGeometry

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem map_conj_projection (K : Subgroup SL(3,F)) (s : SL(3,F)) :
    (K.map (MulAut.conj s).toMonoidHom).map (projection F) =
      (K.map (projection F)).map (MulAut.conj (projection F s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem map_conj_conj {G : Type*} [Group G] (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b*a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite F] [CharP F 2] in
/-- Restricting the preimage to UT₃ lifts every projective subgroup in UT₃. -/
private theorem unipotent_lift (R : Subgroup PSL(3,F)) (hR : R ≤ unipotent F) :
    ∃ Q : Subgroup SL(3,F), Q ≤ unipotentSL F ∧ Q.map (projection F) = R := by
  refine ⟨R.comap (projection F) ⊓ unipotentSL F, inf_le_right, ?_⟩
  apply le_antisymm
  · rintro x ⟨u,hu,rfl⟩
    exact hu.1
  · intro x hx
    obtain ⟨u,hu,he⟩ := hR hx
    refine ⟨u,⟨?_,hu⟩,he⟩
    change projection F u ∈ R
    rwa [he]

/-- A geometric normalizer cover in SL₃ covers every two-local of PSL₃. -/
theorem twoLocal_conjugate_le_of_normalizer_cover
    (hgeo : ∀ Q : Subgroup SL(3,F), Q ≠ ⊥ → Q ≤ unipotentSL F →
      ∃ (s : SL(3,F)) (point : Bool),
        (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ parabolicSL F point)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (M : Subgroup PSL(3,F)) (hM : IsTwoLocal M) :
    ∃ (g : PSL(3,F)) (point : Bool),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic F point := by
  obtain ⟨R,hR,hRp,rfl⟩ := hM
  obtain ⟨S,hRS⟩ := hRp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) S (unipotentSylow F hf hF)
  have hS : (S : Subgroup PSL(3,F)).map (MulAut.conj g).toMonoidHom = unipotent F := by
    have h := congrArg (fun T : Sylow 2 PSL(3,F) => (T : Subgroup PSL(3,F))) hg
    exact h
  let R' := R.map (MulAut.conj g).toMonoidHom
  have hR'U : R' ≤ unipotent F := hS ▸ Subgroup.map_mono hRS
  obtain ⟨Q,hQU,hQR⟩ := unipotent_lift F R' hR'U
  have hQ : Q ≠ ⊥ := by
    intro hQ
    have he : R' = ⊥ := by rw [← hQR,hQ,Subgroup.map_bot]
    apply hR
    apply (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    simpa only [Subgroup.map_bot] using he
  obtain ⟨s,point,hcover⟩ := hgeo Q hQ hQU
  have hnorm : (Subgroup.normalizer Q).map (projection F) = Subgroup.normalizer R' := by
    rw [← normalizer_map_comap F Q hQU, Subgroup.map_comap_eq_self_of_surjective
      (projection_surjective F), hQR]
  have hcover' := Subgroup.map_mono (f := projection F) hcover
  rw [map_conj_projection F, hnorm, ← parabolic_eq_map] at hcover'
  have hnR : Subgroup.normalizer R' =
      (Subgroup.normalizer R).map (MulAut.conj g).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R (MulAut.conj g)).symm
  rw [hnR,map_conj_conj] at hcover'
  exact ⟨projection F s * g,point,hcover'⟩

/-- Maximality upgrades the geometric containment to an actual ambient conjugacy. -/
theorem maximalTwoLocal_conjugate_of_normalizer_cover
    (hgeo : ∀ Q : Subgroup SL(3,F), Q ≠ ⊥ → Q ≤ unipotentSL F →
      ∃ (s : SL(3,F)) (point : Bool),
        (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ parabolicSL F point)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (M : Subgroup PSL(3,F)) (hM : IsMaximalTwoLocal M) :
    ∃ g : PSL(3,F), M.map (MulAut.conj g).toMonoidHom = pointParabolic F ∨
      M.map (MulAut.conj g).toMonoidHom = lineParabolic F := by
  obtain ⟨g,point,hle⟩ := twoLocal_conjugate_le_of_normalizer_cover F hgeo hf hF M hM.1
  have hM' := Theory.GroupTheory.isMaximalTwoLocal_map (MulAut.conj g) hM
  have heq : M.map (MulAut.conj g).toMonoidHom = parabolic F point :=
    le_antisymm hle (hM'.2 (parabolic_twoLocal F point) hle)
  refine ⟨g, ?_⟩
  cases point
  · exact Or.inr heq
  · exact Or.inl heq

/-- Once coverage is supplied, every maximal two-local has characteristic two. -/
theorem maximalTwoLocal_characteristicTwo_of_normalizer_cover
    (hgeo : ∀ Q : Subgroup SL(3,F), Q ≠ ⊥ → Q ≤ unipotentSL F →
      ∃ (s : SL(3,F)) (point : Bool),
        (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ parabolicSL F point)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (M : Subgroup PSL(3,F)) (hM : IsMaximalTwoLocal M) :
    HasCharacteristicTwo M := by
  obtain ⟨g,point,hle⟩ := twoLocal_conjugate_le_of_normalizer_cover F hgeo hf hF M hM.1
  have hM' := Theory.GroupTheory.isMaximalTwoLocal_map (MulAut.conj g) hM
  have heq : M.map (MulAut.conj g).toMonoidHom = parabolic F point :=
    le_antisymm hle (hM'.2 (parabolic_twoLocal F point) hle)
  have hc : HasCharacteristicTwo (M.map (MulAut.conj g).toMonoidHom) :=
    heq ▸ parabolic_characteristicTwo F point
  exact hc.of_equiv
    (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

/-- The all-local cover in particular supplies the source condition E. -/
theorem evenCharacteristic_of_normalizer_cover
    (hgeo : ∀ Q : Subgroup SL(3,F), Q ≠ ⊥ → Q ≤ unipotentSL F →
      ∃ (s : SL(3,F)) (point : Bool),
        (Subgroup.normalizer Q).map (MulAut.conj s).toMonoidHom ≤ parabolicSL F point)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f) :
    IsEvenCharacteristic PSL(3,F) := by
  intro _ M hM _
  exact maximalTwoLocal_characteristicTwo_of_normalizer_cover F hgeo hf hF M hM

end CFSG.Quasithin.MainConverse.LinearThreeGeometry
