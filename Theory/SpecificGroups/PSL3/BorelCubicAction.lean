module
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.FieldTheory.CubicDisplacement
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
/-!
# Cubic displacement on the full binary projective Borel

The first diagonal axis has no scalar kernel. Cubic displacement by a
field actor therefore fixes all field cubes and kills the field part above
order four. A graph actor would force every field unit to have ninth power
one; this is impossible at binary field order at least eight. The triangular linear
factor disappears on the actual Borel quotient, retaining cubic scalars.
A two-element with an odd inner power is inner. A two-subgroup containing
the original Sylow inner image then makes this actor Sylow inner by maximality.

Source: the automorphism calculation used in Aschbacher--Smith 12.6.31,
printed pp.836--837; GLS3 §2.7 for the standard automorphism factors.
-/
public section
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
open scoped MatrixGroups
namespace Matrix.PSL3.BorelCubicAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem quotient_linear_torus {n : ℕ} (hF : Nat.card F = 2^n)
    (m : GL (Fin 3) F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (d : Fˣ × Fˣ) (hb : linearConj F m (torusMap F d) ∈ borel F) :
    quotientTorusEquiv F hF (QuotientGroup.mk
      (⟨linearConj F m (torusMap F d),hb⟩ : borel F)) = QuotientGroup.mk d := by
  obtain ⟨u,hu,he⟩ := linearConjSL_torus_factor F m hm d
  have he' : (⟨linearConj F m (torusMap F d),hb⟩ : borel F) =
      ⟨projection F u,unipotent_le_borel F (mem_map_of_mem _ hu)⟩ *
        ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩ := by
    apply Subtype.ext
    change projection F (linearConjSL F m (torusSL F d)) = _
    rw [he,map_mul]
    rfl
  have hu' : (QuotientGroup.mk
      (⟨projection F u,unipotent_le_borel F (mem_map_of_mem _ hu)⟩ : borel F) :
      borel F ⧸ pCore 2 (borel F)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [twoCore_eq F hF]
    exact mem_map_of_mem _ hu
  rw [he',QuotientGroup.mk_mul,hu',one_mul]
  exact quotientTorusEquiv_mk_torus F hF d

/-- Full cubic displacement leaves only the linear automorphism factor. -/
theorem linear_of_cubic_displacement_three {n : ℕ} (hn : 3 ≤ n)
    (hF : Nat.card F = 2^n) (a : MulAut PSL(3,F))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (hc : ∀ x ∈ borel F, (a x * x⁻¹)^3 ∈ unipotent F) :
    ∃ m : GL (Fin 3) F, a = linearConj F m := by
  obtain ⟨m,σ,ε,rfl⟩ := ActorCoverage.projectiveCoverage_of_standard_eq_top F
    (standard_eq_top_of_two_power_card F (by omega) hF) a
  have hm := linear_part_unipotent F m σ ε hU
  have hB : (borel F).map (projectiveActor F m σ ε).toMonoidHom = borel F := by
    rw [←normalizer_unipotent F (by omega : 0 < n) hF,
      map_equiv_normalizer_eq,hU]
  let q := (quotientTorusEquiv F hF).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (borel F)))
  have hcq (b : borel F) :
      (q ⟨projectiveActor F m σ ε b,hB.le (mem_map_of_mem _ b.property)⟩ *
        (q b)⁻¹)^3 = 1 := by
    rw [←map_inv,←map_mul,←map_pow]
    apply (quotientTorusEquiv F hF).map_eq_one_iff.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [twoCore_eq F hF]
    exact hc b b.property
  have haxis (u : Fˣ) :
      ((if ε then QuotientGroup.mk (1,(Units.map σ.toMonoidHom u)⁻¹)
        else QuotientGroup.mk (Units.map σ.toMonoidHom u,1)) *
        (QuotientGroup.mk (u,1))⁻¹ : (Fˣ × Fˣ) ⧸ cubicScalars F)^3 = 1 := by
    let b : borel F := ⟨torusMap F (u,1),torus_le_borel F ⟨(u,1),rfl⟩⟩
    have hh := hcq b
    have hqb : q b = QuotientGroup.mk (u,1) := quotientTorusEquiv_mk_torus F hF _
    rw [hqb] at hh
    cases ε
    · have he : projectiveActor F m σ false b =
          linearConj F m (torusMap F (Units.map σ.toMonoidHom u,1)) := by
        simp only [projectiveActor,Bool.false_eq_true,↓reduceIte,mul_one,
          MulAut.mul_apply,b,field_torusMap,map_one]
      have hq : q ⟨projectiveActor F m σ false b,hB.le (mem_map_of_mem _ b.property)⟩ =
          QuotientGroup.mk (Units.map σ.toMonoidHom u,1) := by
        change quotientTorusEquiv F hF (QuotientGroup.mk _) = _
        simp_rw [he]
        exact quotient_linear_torus hF m hm _ _
      simpa only [hq,Bool.false_eq_true,↓reduceIte] using hh
    · have he : projectiveActor F m σ true b =
          linearConj F m (torusMap F (1,(Units.map σ.toMonoidHom u)⁻¹)) := by
        simp only [projectiveActor,↓reduceIte,MulAut.mul_apply,b,
          oppositionGraph_torusMap,field_torusMap,inv_one,map_one,map_inv]
      have hq : q ⟨projectiveActor F m σ true b,hB.le (mem_map_of_mem _ b.property)⟩ =
          QuotientGroup.mk (1,(Units.map σ.toMonoidHom u)⁻¹) := by
        change quotientTorusEquiv F hF (QuotientGroup.mk _) = _
        simp_rw [he]
        exact quotient_linear_torus hF m hm _ _
      simpa only [hq,↓reduceIte] using hh
  have hlarge : 8 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  cases ε
  · have hσ : σ = 1 := by
      apply (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ ?_).resolve_right
      · omega
      · intro u
        have h := haxis u
        simp only [Bool.false_eq_true,↓reduceIte,←QuotientGroup.mk_inv,
          ←QuotientGroup.mk_mul,←QuotientGroup.mk_pow] at h
        have hs := (QuotientGroup.eq_one_iff _).mp h
        change ((Units.map σ.toMonoidHom u,1) * (u,1)⁻¹)^3 ∈ cubicScalars F at hs
        have hh : (Units.map σ.toMonoidHom u * u⁻¹)^3 = (1 * (1:Fˣ)⁻¹)^3 := hs.1
        simpa only [inv_one,mul_one,one_pow] using hh
    exact ⟨m,by simp [projectiveActor,hσ]⟩
  · have hall (u : Fˣ) : u^9 = 1 := by
      have h := haxis u
      simp only [↓reduceIte,←QuotientGroup.mk_inv,←QuotientGroup.mk_mul,
        ←QuotientGroup.mk_pow] at h
      have hs := (QuotientGroup.eq_one_iff _).mp h
      change ((1,(Units.map σ.toMonoidHom u)⁻¹) * (u,1)⁻¹)^3 ∈ cubicScalars F at hs
      have hh : ((1 * u⁻¹)^3)^3 = 1 := hs.2
      simpa only [one_mul,←pow_mul,inv_pow,inv_eq_one] using hh
    have hdiv : Nat.card Fˣ ∣ 9 := by
      rw [←IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall
    rw [Nat.card_units,hF] at hdiv
    by_cases hn3 : n = 3
    · subst n
      norm_num at hdiv
    · have hlarge' : 16 ≤ 2^n :=
        Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 4 ≤ n)
      have hsmall := Nat.le_of_dvd (by decide : 0 < 9) hdiv
      omega

/-- The original large-field API, retained with its original hypothesis. -/
theorem linear_of_cubic_displacement {n : ℕ} (hn : 4 ≤ n)
    (hF : Nat.card F = 2^n) (a : MulAut PSL(3,F))
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (hc : ∀ x ∈ borel F, (a x * x⁻¹)^3 ∈ unipotent F) :
    ∃ m : GL (Fin 3) F, a = linearConj F m :=
  linear_of_cubic_displacement_three (by omega) hF a hU hc

/-- A two-element with full cubic Borel displacement is inner. -/
theorem inner_of_cubic_displacement_three {n : ℕ} (hn : 3 ≤ n)
    (hF : Nat.card F = 2^n) (a : MulAut PSL(3,F))
    (ha : ∃ k : ℕ, a ^ (2^k) = 1)
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (hc : ∀ x ∈ borel F, (a x * x⁻¹)^3 ∈ unipotent F) :
    a ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨m,rfl⟩ := linear_of_cubic_displacement_three hn hF a hU hc
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  have hi : q (linearConj F m) ^ Nat.card Fˣ = 1 := by
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (linearConj_pow_inner F m)
  obtain ⟨k,hk⟩ := ha
  have hk' : q (linearConj F m) ^ (2^k) = 1 := by rw [←map_pow,hk,map_one]
  have he : orderOf (q (linearConj F m)) = 1 := Nat.eq_one_of_dvd_coprimes
    ((units_odd F hF).coprime_two_right.pow_right k)
    (orderOf_dvd_of_pow_eq_one hi) (orderOf_dvd_of_pow_eq_one hk')
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp he)

/-- The original large-field innerness API. -/
theorem inner_of_cubic_displacement {n : ℕ} (hn : 4 ≤ n)
    (hF : Nat.card F = 2^n) (a : MulAut PSL(3,F))
    (ha : ∃ k : ℕ, a ^ (2^k) = 1)
    (hU : (unipotent F).map a.toMonoidHom = unipotent F)
    (hc : ∀ x ∈ borel F, (a x * x⁻¹)^3 ∈ unipotent F) :
    a ∈ MulAut.innerSubgroup PSL(3,F) :=
  inner_of_cubic_displacement_three (by omega) hF a ha hU hc

/-- Cubic Borel displacement detects an original two-subgroup actor, through
its actual Sylow subgroup and the full inner map. -/
theorem actor_mem_sylow_inner {n : ℕ} (hn : 4 ≤ n)
    (hF : Nat.card F = 2^n) (P : Sylow 2 PSL(3,F))
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hPA : (P : Subgroup PSL(3,F)).map MulAut.conj ≤ A)
    (a : MulAut PSL(3,F)) (ha : a ∈ A)
    (hP : (P : Subgroup PSL(3,F)).map a.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set PSL(3,F)), (a x * x⁻¹)^3 ∈ (P : Subgroup PSL(3,F))) :
    a ∈ (P : Subgroup PSL(3,F)).map MulAut.conj := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P
    (unipotentSylow F (by omega : 0 < n) hF)
  let e := MulAut.conj g
  have hPe : (P : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    change ((g • P : Sylow 2 PSL(3,F)) : Subgroup PSL(3,F)) = _
    rw [hg]
    rfl
  let b := MulAut.congr e a
  have hact (x : PSL(3,F)) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  have hU : (unipotent F).map b.toMonoidHom = unipotent F := by
    have heq : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom :=
      MonoidHom.ext hact
    rw [←hPe,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  have hN : (normalizer (P : Set PSL(3,F))).map e.toMonoidHom = borel F := by
    change (normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F))).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hPe,normalizer_unipotent F (by omega) hF]
  have hbc : ∀ x ∈ borel F, (b x * x⁻¹)^3 ∈ unipotent F := by
    intro x hx
    rw [←hN] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem e.toMonoidHom (hc y hy)
    rw [hPe] at hh
    simpa only [map_pow,map_mul,map_inv,MulEquiv.coe_toMonoidHom,hact] using hh
  have hap : ∃ k : ℕ, a ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := hA ⟨a,ha⟩
    exact ⟨k,congrArg Subtype.val hk⟩
  have hbp : ∃ k : ℕ, b ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := hap
    exact ⟨k,by rw [show b = MulAut.congr e a from rfl,←map_pow,hk,map_one]⟩
  obtain ⟨x,hx⟩ := inner_of_cubic_displacement hn hF b hbp hU hbc
  have hi : MulAut.conj (e.symm x) = a := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hx
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hinj : Function.Injective (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) :=
    MulAut.conj_injective_of_center_eq_bot (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
  have hp : IsPGroup 2 (A.comap MulAut.conj) := hA.comap_of_injective _ hinj
  have hle : (P : Subgroup PSL(3,F)) ≤ A.comap MulAut.conj :=
    map_le_iff_le_comap.mp hPA
  have he := P.is_maximal' hp hle
  refine ⟨e.symm x,?_,hi⟩
  rw [←he]
  change MulAut.conj (e.symm x) ∈ A
  rwa [hi]
/-- Transport the calculation through a supplied surjection and the exact
image Sylow; the original normalizer is mapped onto the full normalizer. -/
theorem normalizer_actor_mem_sylow_inner {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2^n)
    (q : X →* PSL(3,F)) (hq : Function.Surjective q) (P : Sylow 2 X)
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hPA : ((P : Subgroup X).map q).map MulAut.conj ≤ A)
    (α : MulAut X) (β : MulAut PSL(3,F)) (hβ : β ∈ A)
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup X).map α.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set X), (α x * x⁻¹)^3 ∈ (P : Subgroup X)) :
    β ∈ ((P : Subgroup X).map q).map MulAut.conj := by
  let R := P.mapSurjective hq
  apply actor_mem_sylow_inner hn hF R A hA hPA β hβ
  · have heq : β.toMonoidHom.comp q = q.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he x).symm)
    change ((P : Subgroup X).map q).map β.toMonoidHom = (P : Subgroup X).map q
    rw [Subgroup.map_map,heq,←Subgroup.map_map,hP]
  · intro x hx
    have hN := P.normalizer_map_surjective q hq
    change (normalizer (P : Set X)).map q = normalizer (R : Set PSL(3,F)) at hN
    rw [←hN] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem q (hc y hy)
    change (β (q y) * (q y)⁻¹)^3 ∈ (P : Subgroup X).map q
    simpa only [map_pow,map_mul,map_inv,he] using hh
end Matrix.PSL3.BorelCubicAction
