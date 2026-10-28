module
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms

/-!
# The coefficient action on a literal Sylow-normalizer quotient

Align the specified Sylow image with the upper root group. Semilinear
coverage expresses an automorphism preserving that image as an inner
Borel twist followed by a field automorphism. The diagonal projection
kills the inner twist. The resulting surjection on the original normalizer
has exactly its original Sylow as kernel and intertwines the given action.
No invariance of a chosen Hall complement is required.

Source: the rank-one torus argument in Aschbacher–Smith 5.1.13, printed
p.638, refs/quasithin.pdf; the semilinear coverage is the existing rank-one
model theorem.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem exists_sylowNormalizer_torus_action
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (α : MulAut G) (β : MulAut SL(2,F))
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = (P : Subgroup G)) :
    ∃ f : normalizer (P : Set G) →* Fˣ, ∃ σ : F ≃+* F,
      Function.Surjective f ∧
      (∀ x, f x = 1 ↔ (x : G) ∈ P) ∧
      ∀ x y : normalizer (P : Set G), α x = y →
        f y = Units.map σ.toMonoidHom (f x) := by
  let R := P.mapSurjective hq
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) R (upperUnipotentSylow F 2)
  let e := MulAut.conj a
  let q' := e.toMonoidHom.comp q
  let β' := MulAut.congr e β
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hPq : (P : Subgroup G).map q' = upperUnipotent F := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    change ((a • R : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have he' (x : G) : q' (α x) = β' (q' x) := by
    change e (q (α x)) = e (β (e.symm (e (q x))))
    rw [he,e.symm_apply_apply]
  have hU : (upperUnipotent F).map β'.toMonoidHom = upperUnipotent F := by
    have heq : β'.toMonoidHom.comp q' = q'.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (he' x).symm
    rw [←hPq,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  obtain ⟨g,σ,hβ⟩ := sl2_semilinear_coverage β'
  have hg : g ∈ rankOneBorel F := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hβ] at hU
    change (upperUnipotent F).map
      ((MulAut.conj g).toMonoidHom.comp (sl2FieldAut σ).toMonoidHom) = _ at hU
    rwa [←Subgroup.map_map,sl2FieldAut_map_upper] at hU
  have hk' : q'.ker ≤ (P : Subgroup G) := by
    intro x hx
    exact hk (e.map_eq_one_iff.mp hx)
  have hroot : (upperUnipotent F).comap q' = P := by
    rw [←hPq,comap_map_eq_self hk']
  have hN : (rankOneBorel F).comap q' = normalizer (P : Set G) := by
    rw [rankOneBorel,comap_normalizer_eq_of_surjective _ hq',hroot,P.coe_coe]
  let f0 : normalizer (P : Set G) →* rankOneBorel F :=
    (q'.comp (normalizer (P : Set G)).subtype).codRestrict _ (by
      intro x
      change (x : G) ∈ (rankOneBorel F).comap q'
      rw [hN]
      exact x.property)
  have hf0 : Function.Surjective f0 := by
    intro y
    obtain ⟨x,hx⟩ := hq' y
    have hm : x ∈ normalizer (P : Set G) := by
      rw [←hN]
      change q' x ∈ rankOneBorel F
      rw [hx]
      exact y.property
    exact ⟨⟨x,hm⟩,Subtype.ext hx⟩
  let π : rankOneBorel F →* Fˣ := {
    toFun b := Units.mk0 (b.val.val 0 0) (by
      have hd : b.val.val 0 0 * b.val.val 1 1 = 1 := by
        simpa only [det_fin_two,(mem_rankOneBorel_iff _).mp b.property,
          mul_zero,sub_zero] using b.val.property
      exact left_ne_zero_of_mul_eq_one hd)
    map_one' := by ext; rfl
    map_mul' b d := by
      apply Units.ext
      simp [mul_apply,Fin.sum_univ_two,(mem_rankOneBorel_iff _).mp d.property] }
  have hπ : Function.Surjective π := by
    intro z
    refine ⟨⟨diag2 z z.ne_zero,diag_mem_rankOneBorel (z:F) z.ne_zero⟩,?_⟩
    apply Units.ext
    simp [π,diag2_coe']
  have hπk (b : rankOneBorel F) : π b = 1 ↔ b.val ∈ upperUnipotent F := by
    constructor
    · intro hb
      have h00 : b.val.val 0 0 = 1 := congrArg Units.val hb
      have h10 := (mem_rankOneBorel_iff _).mp b.property
      have h11 : b.val.val 1 1 = 1 := by
        simpa only [det_fin_two,h00,h10,one_mul,mul_zero,sub_zero] using b.val.property
      refine (mem_upperUnipotent F _).mpr ⟨b.val.val 0 1,?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [transvection_coe,h00,h10,h11]
    · intro hb
      obtain ⟨z,hz⟩ := (mem_upperUnipotent F _).mp hb
      apply Units.ext
      change b.val.val 0 0 = 1
      rw [←hz]
      simp [transvection_coe]
  let f := π.comp f0
  refine ⟨f,σ,hπ.comp hf0,?_,?_⟩
  · intro x
    change π (f0 x) = 1 ↔ _
    rw [hπk]
    exact Iff.of_eq (congrArg (fun H : Subgroup G => (x : G) ∈ H) hroot)
  · intro x y hxy
    let z : rankOneBorel F := ⟨sl2FieldAut σ (q' x),by
      apply (mem_rankOneBorel_iff _).mpr
      change σ ((q' x).val 1 0) = 0
      exact (congrArg σ ((mem_rankOneBorel_iff _).mp (f0 x).property)).trans (map_zero σ)⟩
    have hy : f0 y = (⟨g,hg⟩ : rankOneBorel F) * z * (⟨g,hg⟩ : rankOneBorel F)⁻¹ := by
      apply Subtype.ext
      change q' y = g * sl2FieldAut σ (q' x) * g⁻¹
      rw [←hxy,he',hβ]
      rfl
    change π (f0 y) = _
    rw [hy,map_mul,map_mul,map_inv,mul_comm (π ⟨g,hg⟩),mul_assoc,mul_inv_cancel,mul_one]
    apply Units.ext
    change (sl2FieldAut σ (q' x)).val 0 0 = σ ((q' x).val 0 0)
    rfl
end Matrix.SpecialLinearGroup
