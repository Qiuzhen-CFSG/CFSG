module

public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import BenderSuzuki.Converse.PSU3

/-!
# Invariant planes in the concrete unitary root group

The root coordinates are pairs (a,b) satisfying b + conjugate(b) + a conjugate(a) = 0.
In characteristic two, squaring an element of exponent two forces a = 0.
These are precisely the central elements. The torus multiplies their second
coordinate by inverse norms, and norm surjectivity makes it transitive on the
nonzero center. Thus a nontrivial invariant subgroup of exponent two is the
whole center, whose order is the fixed-field order.

The projective root homomorphism is injective; transporting along it preserves
this argument and the actual embedded center. This is the concrete model step
in Aschbacher--Smith, proof of 15.3.40, printed p.1138 (combined manuscript,
1 March 2004). The trace, norm and matrix formulas come from the existing
Huppert II.10.4 and II.10.12 developments.
-/

public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryField
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 3 F) (q : ℕ)
variable (hcard : Nat.card F = q ^ 2)
variable (hfixed : Nat.card {x : F // J.conj x = x} = q)

include hcard hfixed in
omit [CharP F 2] in
private theorem first_surjective (a : F) :
    ∃ z : hermitianUnipotentCoord J, z.1.1 = a := by
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a * J.conj a)) (by rw [map_neg, map_mul, J.conj_involutive]; ring)
  exact ⟨⟨(a, b), by dsimp; linear_combination hb⟩, rfl⟩

omit [Finite F] [CharP F 2] in
private theorem commute_iff (z w : hermitianUnipotentCoord J) :
    z * w = w * z ↔ z.1.1 * J.conj w.1.1 = w.1.1 * J.conj z.1.1 := by
  constructor
  · intro h
    have h' := congrArg (fun x : hermitianUnipotentCoord J => x.1.2) h
    change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 =
      w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 at h'
    linear_combination -h'
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · exact add_comm _ _
    · change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 =
        w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1
      rw [h]; ring

include hcard hfixed in
/-- The center is precisely the set of root coordinates with first entry zero. -/
theorem mem_center_iff_first_zero (z : hermitianUnipotentCoord J) :
    z ∈ center (hermitianUnipotentCoord J) ↔ z.1.1 = 0 := by
  constructor
  · intro hz
    have hc (w : hermitianUnipotentCoord J) :=
      (commute_iff J z w).mp ((mem_center_iff.mp hz w).symm)
    obtain ⟨w, hw⟩ := first_surjective J q hcard hfixed 1
    have hf : z.1.1 = J.conj z.1.1 := by simpa [hw] using hc w
    obtain ⟨t, ht⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed 1 (by simp)
    obtain ⟨v, hv⟩ := first_surjective J q hcard hfixed t
    have ht' : J.conj t ≠ t := by
      intro he; rw [he, CharTwo.add_self_eq_zero] at ht; exact zero_ne_one ht
    have he := hc v
    rw [hv, ← hf] at he
    have hh : z.1.1 * (J.conj t - t) = 0 := by linear_combination he
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr ht')
  · intro hz
    exact mem_center_iff.mpr (fun w => ((commute_iff J z w).mpr (by simp [hz])).symm)

omit [Finite F] in
private theorem first_zero_of_sq_one (z : hermitianUnipotentCoord J) (hz : z ^ 2 = 1) :
    z.1.1 = 0 := by
  have he := congrArg (fun x : hermitianUnipotentCoord J => x.1.2) hz
  rw [pow_two] at he
  change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at he
  rw [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero] at he
  rcases mul_eq_zero.mp he with h | h
  · exact h
  · exact (map_eq_zero J.conj).mp h

omit [Finite F] in
private theorem fixed_second (z : hermitianUnipotentCoord J) (hz : z.1.1 = 0) :
    J.conj z.1.2 = z.1.2 := by
  have he := z.2
  rw [hz, zero_mul, add_zero] at he
  exact (eq_neg_of_add_eq_zero_right he).trans (CharTwo.neg_eq _)

include hcard hfixed in
/-- The root center has the order of the fixed field. -/
theorem card_center : Nat.card (center (hermitianUnipotentCoord J)) = q := by
  let e : center (hermitianUnipotentCoord J) ≃ {x : F // J.conj x = x} :=
    { toFun := fun z => ⟨z.1.1.2, fixed_second J z.1
        ((mem_center_iff_first_zero J q hcard hfixed z.1).mp z.2)⟩
      invFun := fun x => ⟨⟨(0, x.1), by simp [x.2, CharTwo.add_self_eq_zero]⟩,
        (mem_center_iff_first_zero J q hcard hfixed _).mpr rfl⟩
      left_inv := by
        intro z
        apply Subtype.ext; apply Subtype.ext
        exact Prod.ext ((mem_center_iff_first_zero J q hcard hfixed z.1).mp z.2).symm rfl
      right_inv := by intro x; rfl }
  exact (Nat.card_congr e).trans hfixed

include hcard hfixed in
/-- Every nontrivial torus-invariant subgroup of exponent two is the full root center. -/
theorem invariant_eq_center (U : Subgroup (hermitianUnipotentCoord J))
    (hU : U ≠ ⊥) (hsq : ∀ z ∈ U, z ^ 2 = 1)
    (hinv : ∀ k : Fˣ, ∀ z ∈ U, hermitianTorusAction J k z ∈ U) :
    U = center (hermitianUnipotentCoord J) := by
  have hfirst (z) (hz : z ∈ U) : z.1.1 = 0 := first_zero_of_sq_one J z (hsq z hz)
  apply le_antisymm
  · intro z hz
    exact (mem_center_iff_first_zero J q hcard hfixed z).mpr (hfirst z hz)
  · obtain ⟨⟨z, hz⟩, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hzne : z ≠ 1 := fun h => hzne (Subtype.ext h)
    have hz0 := hfirst z hz
    have hzb : z.1.2 ≠ 0 := by
      intro he; apply hzne; apply Subtype.ext; exact Prod.ext hz0 he
    intro w hw
    have hw0 := (mem_center_iff_first_zero J q hcard hfixed w).mp hw
    by_cases hwb : w.1.2 = 0
    · have he : w = 1 := Subtype.ext (Prod.ext hw0 hwb)
      rw [he]; exact U.one_mem
    · obtain ⟨k, hk, hkn⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed
        (z.1.2 / w.1.2) (by rw [map_div₀, fixed_second J z hz0, fixed_second J w hw0])
        (div_ne_zero hzb hwb)
      have he : hermitianTorusAction J (Units.mk0 k hk) z = w := by
        apply Subtype.ext; apply Prod.ext
        · simp [hz0, hw0]
        · simp only [hermitianTorusAction_snd, Units.val_mk0]
          calc
            z.1.2 * (J.conj k)⁻¹ * k⁻¹ = z.1.2 / (k * J.conj k) := by
              simp only [div_eq_mul_inv, mul_inv]; ring
            _ = w.1.2 := by rw [hkn]; field_simp
      exact he ▸ hinv (Units.mk0 k hk) z hz

omit [Finite F] [CharP F 2] in
private theorem torus_normalizes_root
    (hs : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Fˣ) :
    hermitianTorusPSU J hs k ∈ normalizer ((hermitianUnipotentPSU J hs).range : Set _) := by
  have hc (l : Fˣ) (z : hermitianUnipotentCoord J) :
      hermitianTorusPSU J hs l * hermitianUnipotentPSU J hs z *
        (hermitianTorusPSU J hs l)⁻¹ =
      hermitianUnipotentPSU J hs (hermitianTorusAction J l z) :=
    mul_inv_eq_iff_eq_mul.mpr (hermitianTorusPSU_mul_unipotent J hs l z)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨hermitianTorusAction J k z, (hc k z).symm⟩
  · rintro ⟨z, hz⟩
    have hh := congrArg (fun a =>
      (hermitianTorusPSU J hs k)⁻¹ * a * hermitianTorusPSU J hs k) hz
    have hi := hc k⁻¹ z
    simp only [map_inv, inv_inv] at hi
    refine ⟨hermitianTorusAction J k⁻¹ z, ?_⟩
    rw [← hi, hh]
    simp [mul_assoc]

/-- An injective homomorphism identifies the center of its domain with the
center of its image, including the embeddings into the ambient group. -/
private theorem map_center_eq_range_center {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) :
    (center A).map f = (center f.range).map f.range.subtype := by
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨e z, (centerCongr e ⟨z, hz⟩).property, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨e.symm z, (centerCongr e.symm ⟨z, hz⟩).property, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply z)

/-- Injective transport preserves the center of an embedded subgroup. -/
theorem map_subgroup_center {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f) (P : Subgroup H) :
    ((center P).map P.subtype).map f =
      (center (P.map f)).map (P.map f).subtype := by
  have hh := map_center_eq_range_center (f.comp P.subtype) (hf.comp P.subtype_injective)
  rwa [MonoidHom.range_comp, Subgroup.range_subtype, ← Subgroup.map_map] at hh

include hcard hfixed in
/-- A four-group in the concrete projective root, invariant under its normalizer,
is the whole root center, and the fixed field has order four. -/
theorem projective_plane_eq_center
    (hs : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hWR : W ≤ (hermitianUnipotentPSU J hs).range)
    (hW : Nat.card W = 4) (hsq : ∀ w ∈ W, w ^ 2 = 1)
    (hnorm : normalizer ((hermitianUnipotentPSU J hs).range : Set _) ≤
      normalizer (W : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    q = 4 ∧ W = (center (hermitianUnipotentPSU J hs).range).map
      (hermitianUnipotentPSU J hs).range.subtype := by
  let f := hermitianUnipotentPSU J hs
  have hf : Function.Injective f := BenderSuzuki.Converse.hUPSU_injective J hs
  let U := W.comap f
  have hUW : U.map f = W := Subgroup.map_comap_eq_self hWR
  have hUc : Nat.card U = 4 := by
    rw [← Subgroup.card_map_of_injective hf, hUW, hW]
  have hU : U ≠ ⊥ := by intro he; rw [he] at hUc; simp at hUc
  have hUsq (z) (hz : z ∈ U) : z ^ 2 = 1 := by
    apply hf
    rw [map_pow, map_one]
    exact hsq (f z) hz
  have hUi (k : Fˣ) (z) (hz : z ∈ U) : hermitianTorusAction J k z ∈ U := by
    change f (hermitianTorusAction J k z) ∈ W
    have hk := hnorm (torus_normalizes_root J hs k)
    have hh := (Subgroup.mem_normalizer_iff.mp hk (f z)).mp hz
    have he := hermitianTorusPSU_mul_unipotent J hs k z
    rwa [← mul_inv_eq_iff_eq_mul.mpr he]
  have he := invariant_eq_center J q hcard hfixed U hU hUsq hUi
  refine ⟨?_, ?_⟩
  · rw [he, card_center J q hcard hfixed] at hUc
    exact hUc
  · rw [← hUW, he]
    exact map_center_eq_range_center f hf

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryField
