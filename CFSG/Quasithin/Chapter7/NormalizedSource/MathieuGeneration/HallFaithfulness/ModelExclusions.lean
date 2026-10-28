module
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.Mathieu.M22.Properties.OrderEight
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import Theory.SpecificGroups.SU3.HomocyclicSlice
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.Mathieu.TwoRankLower

/-!
# Rank-one exclusions for a full Mathieu cover

An injective full M₂₂ cover gives a literal M₂₂ section. Its element of
order eight excludes binary PSL₂ and PSU₃ through the Sylow exponent bound;
the Suzuki row is excluded by three-divisibility. For odd PSL₂ we lift the
same section to SL₂ and apply the rank-three bound to its Sylow image.
These exclusions feed the involution fixed-component comparison without
replacing the covering group by its central quotient.

Source: the model inspection in Aschbacher--Smith 4.2.13, printed p.612,
using the actual Theorem B models from A.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterA.Section02 ClassificationModels
open BenderSuzuki.MatrixGroups BenderSuzuki.External

private theorem exponent_four_of_section {X S : Type*} [Group X] [Finite X] [Group S]
    (hX : ∀ P : Subgroup X, IsPGroup 2 P → ∀ x : P, x ^ 4 = 1)
    (U : Subgroup X) (f : U →* S) (hf : Function.Surjective f) :
    ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 4 = 1 := by
  intro P hp x
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hf 2 Q
  have hx : (x : S) ∈ (R : Subgroup U).map f := by
    change (x : S) ∈ (R.mapSurjective hf : Subgroup S)
    rw [hR]
    exact hQ x.property
  obtain ⟨a,ha,he⟩ := hx
  have hs : (a : X) ^ 4 = 1 := congrArg Subtype.val
    (hX ((R : Subgroup U).map U.subtype) (R.isPGroup'.map U.subtype)
      ⟨a,mem_map_of_mem U.subtype ha⟩)
  have hs' : a ^ 4 = 1 := Subtype.ext hs
  apply Subtype.ext
  simpa only [map_pow,map_one,he,Subgroup.coe_pow,Subgroup.coe_one] using congrArg f hs'

private theorem no_cover_of_exponent_four {Q B : Type*} [Group Q] [Finite Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    (hQ : ∀ P : Subgroup Q, IsPGroup 2 P → ∀ x : P, x ^ 4 = 1) : False := by
  let a := MonoidHom.ofInjective hf
  let g := eB.toMonoidHom.comp ((QuotientGroup.mk' (center B)).comp a.symm.toMonoidHom)
  have hg : Function.Surjective g := eB.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.symm.surjective)
  have hh := exponent_four_of_section hQ f.range g hg
  obtain ⟨x,hx⟩ := m22_exists_order_eight
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 3) (by
    simpa only [Nat.card_zpowers,show (2 : ℕ)^3 = 8 from rfl] using hx)
  have hs : x ^ 4 = 1 := congrArg Subtype.val (hh (zpowers x) hp ⟨x,mem_zpowers x⟩)
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd

private theorem exponent_four_of_sylow {Q : Type*} [Group Q] [Finite Q]
    (P : Sylow 2 Q) (hP : ∀ x : P, x ^ 4 = 1)
    (U : Subgroup Q) (hU : IsPGroup 2 U) (x : U) : x ^ 4 = 1 := by
  obtain ⟨R,hR⟩ := hU.exists_le_sylow
  let e := R.equiv P
  have hs : (⟨x,hR x.property⟩ : R) ^ 4 = 1 := e.injective (by
    simpa only [map_pow,map_one] using hP (e ⟨x,hR x.property⟩))
  exact Subtype.ext (congrArg (fun z : R => (z : Q)) hs)

private theorem unitary_exponent_four {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2 ^ n) ^ 2) (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    ∀ P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsPGroup 2 P →
      ∀ x : P, x ^ 4 = 1 := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  let K := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨d⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hcard hfixed
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card,pow_mul] using hcard)
  let P := HermitianForm.EvenTwoRank.rootSylow K rfl hn hcard hfixed
  let e0 : hermitianUnipotentCoord K ≃*
      HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup K rfl :=
    MulEquiv.ofBijective (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.root K rfl).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.root_injective K rfl),
        (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.root K rfl).rangeRestrict_surjective⟩
  let e : hermitianUnipotentCoord K ≃* P := e0.trans
    (MulEquiv.subgroupCongr (HermitianForm.EvenTwoRank.rootSylow_coe K rfl hn hcard hfixed).symm)
  have hp (z : P) : z ^ 4 = 1 := by
    have hz : ((e.symm z)^2).val.1 = 0 := by
      rw [HermitianForm.EvenInner.square_coordinates]
    have hs := (HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero K ((e.symm z)^2)).mpr hz
    have hs4 : e.symm z ^ 4 = 1 := by simpa only [←pow_mul] using hs
    simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e hs4
  intro U hU x
  have hs := exponent_four_of_sylow P hp (U.map d.toMonoidHom) (hU.map _)
    ⟨d x,mem_map_of_mem _ x.property⟩
  apply Subtype.ext
  apply d.injective
  simpa only [map_pow,map_one,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val hs

/-- No Bender model contains a full M₂₂ cover. Binary linear and unitary
Sylow subgroups have exponent at most four; Suzuki has three-free order. -/
theorem m22_cover_not_bender {Q B : Type*} [Group Q] [Finite Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f) :
    ¬ IsBenderModel Q := by
  intro hm
  cases hm with
  | linear n hn hm =>
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    let d := e.trans (Theory.PSL2.sl2QuotientEquiv E).symm
    apply no_cover_of_exponent_four eB (d.toMonoidHom.comp f) (d.injective.comp hf)
    intro P hP x
    rw [show (4 : ℕ) = 2 * 2 from rfl,pow_mul,Matrix.SpecialLinearGroup.twoSubgroup_pow_two P hP x,one_pow]
  | unitary n hn hm =>
    obtain ⟨E,_,_,J,hE,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Q e.toEquiv
    exact no_cover_of_exponent_four eB (e.toMonoidHom.comp f) (e.injective.comp hf)
      (unitary_exponent_four J (by omega) hE hconj)
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    have hd : Nat.card M22 ∣ Nat.card Q := by
      rw [←Nat.card_congr eB.toEquiv]
      exact (card_quotient_dvd_card _).trans (card_dvd_of_injective f hf)
    have h3 := (by rw [m22_order]; decide : 3 ∣ Nat.card M22).trans hd
    rw [Nat.card_congr e.toEquiv] at h3
    exact suzukiMatrixGroup_three_free m (by omega) h3
private theorem odd_field_prime_power
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  have hc : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨ringChar F,n,hp,?_,n.pos,hc⟩
  apply hp.odd_of_ne_two
  intro heq
  rw [heq] at hc
  have heven : Even (Nat.card F) := by
    rw [hc]
    exact Nat.even_pow.mpr ⟨by decide,n.pos.ne'⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- An M₂₂ cover cannot embed in odd-field PSL₂. Lift the literal section
to SL₂ and apply the rank-three bound to the same Sylow epimorphism. -/
theorem m22_cover_not_odd_linear_two {Q B : Type*} [Group Q] [Group B]
    (eB : (B ⧸ center B) ≃* M22) (f : B →* Q) (hf : Function.Injective f)
    {q : ℕ} (hq : Odd q) : ¬ ClassicalGroup.IsPSL Q 2 q := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let j := e.toMonoidHom.comp f
  have hj : Function.Injective j := e.injective.comp hf
  let a := MonoidHom.ofInjective hj
  let π := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F))
  let U := j.range.comap π
  let r : U →* j.range := π.subgroupComap j.range
  have hr : Function.Surjective r := π.subgroupComap_surjective_of_surjective
    j.range (QuotientGroup.mk'_surjective _)
  let g := eB.toMonoidHom.comp ((QuotientGroup.mk' (center B)).comp
    (a.symm.toMonoidHom.comp r))
  have hg : Function.Surjective g := eB.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (a.symm.surjective.comp hr))
  let P : Sylow 2 U := Classical.choice inferInstance
  let S := P.mapSurjective hg
  let k := Matrix.SpecialLinearGroup.toGL.comp (U.subtype.comp (P : Subgroup U).subtype)
  have hk : Function.Injective k := Matrix.SpecialLinearGroup.toGL_injective.comp
    (U.subtype_injective.comp (P : Subgroup U).subtype_injective)
  have ho : Odd (Nat.card F) := hF.symm ▸ hq
  have hb := Theory.SpecificGroups.OddThreeSectionRank.gl2_twoGroup_image_twoRank_le_three
    (odd_field_prime_power F ho) (Field.two_ne_zero_of_odd_card F ho)
    P.isPGroup' k hk (g.subgroupMap (P : Subgroup U)) (g.subgroupMap_surjective _)
  change primeRank 2 S ≤ 3 at hb
  rw [←S.primeRank_eq] at hb
  have hl := m22_four_le_twoRank
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
