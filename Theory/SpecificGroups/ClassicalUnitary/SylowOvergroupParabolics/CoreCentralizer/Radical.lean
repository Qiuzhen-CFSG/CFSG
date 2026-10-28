module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
public import Theory.PGroupCore
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# The flag kernel of a geometric unitary parabolic

For an arbitrary stored Hermitian form, the special unitary stabilizer of `W`
also preserves its perpendicular. The subgroup acting trivially on the three
sections of `0 ≤ W ≤ Wᗮ ≤ V` is normal in that stabilizer. Its difference from
the identity has cube zero, so in characteristic two its elements have fourth
power one. The literal projective image is consequently a normal two-subgroup
of the intrinsic parabolic and lies in its two-core.

For nonzero `W`, the radical meets the scalar projective kernel trivially.
This lifts projective commutation with the radical to actual commutation.
The remaining matrix calculation is specified by `ScalarShear`; it is not
assumed by the radical definition or proved by this module.

Source: the unitary realization of GLS3 2.6.4--2.6.5(e),
`refs/KGroup/GLS3/chapter2.tex`, used in Aschbacher--Smith B.1.13,
printed p.74 (PDF p.85) of `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups Subgroup

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer
variable {F : Type*} [Field F] {d : ℕ} (J : HermitianForm d F)

/-- The Hermitian pairing with the literal stored Gram matrix. -/
def pairing (v w : Fin d → F) : F :=
  (fun i => J.conj (v i)) ⬝ᵥ (J.form *ᵥ w)

/-- The right perpendicular of a subspace for the stored Hermitian form. -/
def perpendicular (W : Submodule F (Fin d → F)) : Submodule F (Fin d → F) where
  carrier := {v | ∀ w ∈ W, pairing J w v = 0}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro v w hv hw x hx
    simp only [pairing, mulVec_add, dotProduct_add]
    rw [show (fun i => J.conj (x i)) ⬝ᵥ (J.form *ᵥ v) = 0 from hv x hx,
      show (fun i => J.conj (x i)) ⬝ᵥ (J.form *ᵥ w) = 0 from hw x hx, add_zero]
  smul_mem' := by
    intro c v hv w hw
    change (fun i => J.conj (w i)) ⬝ᵥ (J.form *ᵥ (c • v)) = 0
    rw [mulVec_smul, dotProduct_smul,
      show (fun i => J.conj (w i)) ⬝ᵥ (J.form *ᵥ v) = 0 from hv w hw, smul_zero]

/-- The flag inclusion is exactly the original total-isotropy condition. -/
theorem le_perpendicular_iff (W : Submodule F (Fin d → F)) :
    W ≤ perpendicular J W ↔ TotallyIsotropic J W := by
  constructor
  · intro h v hv w hw
    exact h hw v hv
  · intro h w hw v hv
    exact h v hv w hw

/-- The actual special unitary action preserves the Hermitian pairing. -/
theorem pairing_action (g : J.specialSubgroup) (v w : Fin d → F) :
    pairing J (linearAction J g v) (linearAction J g w) = pairing J v w := by
  have hg := (J.mem_specialSubgroup_iff g.val).mp g.property |>.1
  change (fun i => J.conj ((g.val.val *ᵥ v) i)) ⬝ᵥ
    (J.form *ᵥ (g.val.val *ᵥ w)) = _
  rw [show (fun i => J.conj ((g.val.val *ᵥ v) i)) =
    (g.val.val.map J.conj) *ᵥ (fun i => J.conj (v i)) from
      funext (RingHom.map_mulVec J.conj.toRingHom g.val.val v)]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have he : (g.val.val.map J.conj).transpose = J.conjTranspose g.val.val := rfl
  rw [he, hg]
  rfl

/-- A special unitary stabilizer preserves the perpendicular as well. -/
theorem action_mem_perpendicular (W : Submodule F (Fin d → F))
    (g : specialStabilizer J W) {v : Fin d → F} (hv : v ∈ perpendicular J W) :
    linearAction J g.val v ∈ perpendicular J W := by
  intro w hw
  have hi := (mem_specialStabilizer_iff J W (g.val⁻¹)).mp
    ((specialStabilizer J W).inv_mem g.property)
  have hw' := hv _ ((hi w).mpr hw)
  have he := pairing_action J g.val (linearAction J (g.val⁻¹) w) v
  have hew : linearAction J g.val (linearAction J (g.val⁻¹) w) = w := by
    rw [map_inv]
    exact (linearAction J g.val).apply_symm_apply w
  rw [hew] at he
  exact he.trans hw'

/-- The natural action restricted to the full special unitary stabilizer. -/
def stabilizerAction (W : Submodule F (Fin d → F)) :
    specialStabilizer J W →* ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  (linearAction J).comp (specialStabilizer J W).subtype

/-- The restricted action preserves the original subspace. -/
theorem stabilizerAction_mem (W : Submodule F (Fin d → F))
    (g : specialStabilizer J W) {v : Fin d → F} (hv : v ∈ W) :
    stabilizerAction J W g v ∈ W :=
  ((mem_specialStabilizer_iff J W g.val).mp g.property v).mpr hv

/-- The restricted action preserves its perpendicular. -/
theorem stabilizerAction_perpendicular (W : Submodule F (Fin d → F))
    (g : specialStabilizer J W) {v : Fin d → F} (hv : v ∈ perpendicular J W) :
    stabilizerAction J W g v ∈ perpendicular J W := action_mem_perpendicular J W g hv

/-- The action cancels with the action of the inverse group element. -/
@[simp] theorem stabilizerAction_inv_cancel (W : Submodule F (Fin d → F))
    (g : specialStabilizer J W) (v : Fin d → F) :
    stabilizerAction J W g (stabilizerAction J W g⁻¹ v) = v := by
  rw [map_inv]
  exact (stabilizerAction J W g).apply_symm_apply v

/-- The kernel on the three sections of the flag `0 ≤ W ≤ Wᗮ ≤ V`.
Its defining conditions are literal linear-action identities, with no
normality, two-group, or centralizer hypothesis built into the definition. -/
def specialRadical (W : Submodule F (Fin d → F)) : Subgroup (specialStabilizer J W) where
  carrier := {g | (∀ v ∈ W, stabilizerAction J W g v = v) ∧
    (∀ v ∈ perpendicular J W, stabilizerAction J W g v - v ∈ W) ∧
    (∀ v, stabilizerAction J W g v - v ∈ perpendicular J W)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2⟩ ⟨hh0, hh1, hh2⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simpa only [map_mul, LinearEquiv.mul_apply, hh0 v hv] using hg0 v hv
    · intro v hv
      have hv' := stabilizerAction_perpendicular J W h hv
      have ht := W.add_mem (hg1 _ hv') (hh1 v hv)
      simpa only [map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel] using ht
    · intro v
      have ht := (perpendicular J W).add_mem (hg2 (stabilizerAction J W h v)) (hh2 v)
      simpa only [map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel] using ht
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      apply (stabilizerAction J W g).injective
      simpa only [stabilizerAction_inv_cancel] using (hg0 v hv).symm
    · intro v hv
      have ht := W.neg_mem (hg1 _ (stabilizerAction_perpendicular J W g⁻¹ hv))
      simpa only [stabilizerAction_inv_cancel, neg_sub] using ht
    · intro v
      have ht := (perpendicular J W).neg_mem (hg2 (stabilizerAction J W g⁻¹ v))
      simpa only [stabilizerAction_inv_cancel, neg_sub] using ht

/-- The flag kernel is normal in the full special unitary stabilizer. -/
instance specialRadical_normal (W : Submodule F (Fin d → F)) :
    (specialRadical J W).Normal where
  conj_mem := by
    rintro n ⟨hn0, hn1, hn2⟩ g
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have hi := hn0 _ (stabilizerAction_mem J W g⁻¹ hv)
      simp only [map_mul, LinearEquiv.mul_apply, hi, stabilizerAction_inv_cancel]
    · intro v hv
      have hi := hn1 _ (stabilizerAction_perpendicular J W g⁻¹ hv)
      have ht := stabilizerAction_mem J W g hi
      simpa only [map_mul, LinearEquiv.mul_apply, map_sub,
        stabilizerAction_inv_cancel] using ht
    · intro v
      have hi := hn2 (stabilizerAction J W g⁻¹ v)
      have ht := stabilizerAction_perpendicular J W g hi
      simpa only [map_mul, LinearEquiv.mul_apply, map_sub,
        stabilizerAction_inv_cancel] using ht

/-- The linear action of the special unitary stabilizer is faithful. -/
theorem stabilizerAction_injective (W : Submodule F (Fin d → F)) :
    Function.Injective (stabilizerAction J W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F)).injective.comp
    (GeneralLinearGroup.toLin.injective.comp
      (J.specialSubgroup.subtype_injective.comp (specialStabilizer J W).subtype_injective))

/-- Each radical element lowers the three-step flag, so `(u - 1)³ = 0`. -/
theorem specialRadical_cube (W : Submodule F (Fin d → F)) (u : specialRadical J W) :
    ((stabilizerAction J W u.val).toLinearMap - 1) ^ 3 = 0 := by
  let t : Module.End F (Fin d → F) := (stabilizerAction J W u.val).toLinearMap - 1
  have ht (v : Fin d → F) : t v = stabilizerAction J W u.val v - v := rfl
  apply LinearMap.ext
  intro v
  change t (t (t v)) = 0
  rw [ht]
  exact sub_eq_zero.mpr (u.property.1 _ (u.property.2.1 _ (u.property.2.2 v)))

/-- In characteristic two the flag kernel has exponent dividing four. -/
theorem specialRadical_pow_four [CharP F 2] [NeZero d]
    (W : Submodule F (Fin d → F)) (u : specialRadical J W) : u ^ 4 = 1 := by
  let e : Module.End F (Fin d → F) := (stabilizerAction J W u.val).toLinearMap
  let : CharP (Module.End F (Fin d → F)) 2 := charP_of_injective_algebraMap' F 2
  have h3 : (e - 1) ^ 3 = 0 := specialRadical_cube J W u
  have h4 : (e - 1) ^ 4 = 0 := by rw [show 4 = 3 + 1 from rfl, pow_succ, h3, zero_mul]
  have hp := sub_pow_char_pow_of_commute (R := Module.End F (Fin d → F))
    (p := 2) (n := 2) (Commute.one_right e)
  norm_num only [Nat.reducePow, one_pow] at hp
  have he : e ^ 4 = 1 := sub_eq_zero.mp (hp.symm.trans h4)
  apply Subtype.ext
  apply stabilizerAction_injective J W
  apply LinearEquiv.toLinearMap_injective
  change (stabilizerAction J W (u.val ^ 4)).toLinearMap =
    (stabilizerAction J W 1).toLinearMap
  rw [map_pow, map_one]
  exact he

/-- The flag kernel is a two-group, without a field-size restriction. -/
theorem specialRadical_isTwoGroup [CharP F 2] [NeZero d]
    (W : Submodule F (Fin d → F)) : IsPGroup 2 (specialRadical J W) := by
  intro u
  exact ⟨2, specialRadical_pow_four J W u⟩

/-- The literal SU-to-PGL projection restricted to the actual parabolic. -/
def projectParabolic (W : Submodule F (Fin d → F)) :
    specialStabilizer J W →* parabolic J W :=
  ((project J).comp (specialStabilizer J W).subtype).codRestrict _
    (fun g => ⟨g.val, g.property, rfl⟩)

/-- Every element of the projective parabolic has a stabilizer representative. -/
theorem projectParabolic_surjective (W : Submodule F (Fin d → F)) :
    Function.Surjective (projectParabolic J W) := by
  rintro ⟨x, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

/-- The image of the flag kernel inside the intrinsic projective parabolic. -/
def projectiveRadical (W : Submodule F (Fin d → F)) : Subgroup (parabolic J W) :=
  (specialRadical J W).map (projectParabolic J W)

/-- Normality is relative to the full projective parabolic. -/
instance projectiveRadical_normal (W : Submodule F (Fin d → F)) :
    (projectiveRadical J W).Normal :=
  Subgroup.Normal.map inferInstance _ (projectParabolic_surjective J W)

/-- The projected flag kernel is a two-group. -/
theorem projectiveRadical_isTwoGroup [CharP F 2] [NeZero d]
    (W : Submodule F (Fin d → F)) : IsPGroup 2 (projectiveRadical J W) :=
  (specialRadical_isTwoGroup J W).map _

/-- The concrete normal two-subgroup lies in the intrinsic two-core. -/
theorem projectiveRadical_le_twoCore [CharP F 2] [NeZero d] [Finite F]
    (W : Submodule F (Fin d → F)) : projectiveRadical J W ≤ pCore 2 (parabolic J W) :=
  le_sSup ⟨inferInstance, projectiveRadical_isTwoGroup J W⟩

/-- The projection has trivial kernel on the radical: a scalar fixing a
nonzero subspace pointwise must be the identity. -/
theorem specialRadical_eq_one_of_project_eq_one (W : Submodule F (Fin d → F))
    (hW : W ≠ ⊥) (u : specialStabilizer J W) (hu : u ∈ specialRadical J W)
    (hp : projectParabolic J W u = 1) : u = 1 := by
  have h : ProjGenLinGroup.mk u.val.val = 1 :=
    congrArg (fun x : parabolic J W => x.val.val) hp
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hW
  have hfix := hu.1 v hv
  change (u.val.val : Matrix (Fin d) (Fin d) F) *ᵥ v = v at hfix
  rw [← hc] at hfix
  change (Matrix.diagonal (fun _ : Fin d => c.val)) *ᵥ v = v at hfix
  rw [Matrix.diagonal_const_mulVec] at hfix
  have hc1 : c = 1 := Units.ext ((smul_left_injective F hv0)
    (hfix.trans (one_smul F v).symm))
  apply Subtype.ext
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

/-- Normality and the trivial radical kernel lift projective commutation
with a radical element to actual commutation. -/
theorem commute_of_projectParabolic_commute (W : Submodule F (Fin d → F))
    (hW : W ≠ ⊥) (g u : specialStabilizer J W) (hu : u ∈ specialRadical J W)
    (hp : Commute (projectParabolic J W g) (projectParabolic J W u)) : Commute g u := by
  have hu' : g * u * g⁻¹ * u⁻¹ ∈ specialRadical J W :=
    (specialRadical J W).mul_mem
      ((specialRadical_normal J W).conj_mem u hu g) ((specialRadical J W).inv_mem hu)
  have hp' : projectParabolic J W (g * u * g⁻¹ * u⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hp.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have he := specialRadical_eq_one_of_project_eq_one J W hW _ hu' hp'
  have hc : g * u * g⁻¹ = u := mul_inv_eq_one.mp he
  exact mul_inv_eq_iff_eq_mul.mp hc

/-- Every stabilizer representative of a projective radical-centralizer
element centralizes the special unitary radical. -/
theorem centralizes_specialRadical_of_project (W : Submodule F (Fin d → F))
    (hW : W ≠ ⊥) (g : specialStabilizer J W)
    (hg : projectParabolic J W g ∈ centralizer (projectiveRadical J W : Set (parabolic J W))) :
    g ∈ centralizer (specialRadical J W : Set (specialStabilizer J W)) := by
  rw [mem_centralizer_iff]
  intro u hu
  exact (commute_of_projectParabolic_commute J W hW g u hu
    (((mem_centralizer_iff.mp hg) _ ⟨u, hu, rfl⟩).symm)).eq.symm

/-- The matrix normal form needed from the remaining centralizer calculation.
After subtracting one common scalar, the operator kills `Wᗮ` and has image
in `W`. This predicate asserts linear identities, not a core bound. -/
def ScalarShear (W : Submodule F (Fin d → F)) (g : specialStabilizer J W) : Prop :=
  ∃ c : Fˣ, (∀ v ∈ perpendicular J W, stabilizerAction J W g v = (c : F) • v) ∧
    ∀ v, stabilizerAction J W g v - (c : F) • v ∈ W

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.CoreCentralizer
