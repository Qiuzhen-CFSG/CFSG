module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.PointStabilizerCentralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.GeneratorInvariance
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.Mathieu.M22.Properties.OrderEight
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import Theory.SpecificGroups.SU3.HomocyclicSlice
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.Mathieu.TwoRankLower
public import Theory.SpecificGroups.SymplecticFour.TwoPower
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.Representation.SpecialLinearNatural
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M23.Properties.Automorphisms

/-!
# The odd-prime fixed-section sieve for the p.623 comparison

A nontrivial odd-prime automorphism fixing a literal M₂₂ section excludes
all odd-characteristic and binary rank-one models by section ranks and
Sylow exponents. The same exponent bound removes binary PSL₃ and PSp₄;
orders exclude the small endpoints and small sporadics. For M₂₃ and M₂₄,
innerness and the native odd-order spectrum forbid the commuting prime
orders forced by the fixed M₂₂ section.

For HS, the fixed M₂₂ section forces index dividing 100. The existing
small-index theorem then puts a conjugate of the concrete point stabilizer
in the fixed subgroup; its checked trivial centralizer excludes the actor.
The remaining list is binary G₂, triality, Ree F₄ and J₄. This is a
partial comparison, not their exclusion. The numerator of the M₂₂ section
need not be quasisimple; its possibly noncentral two-core is retained.
Hall.OddNormalizer.OddLocalAction applies this to the full original residual.
Source: Aschbacher--Smith 4.4.3, p.623; Theorem C, p.33. The copied Sylow
exponent transport and unitary-coordinate calculation are adapted from
MathieuGeneration.HallFaithfulness.ModelExclusions. The imported matrix,
Witt-design and ATLAS calculations retain their original source and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 ClassificationModels Sporadic.Mathieu
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups

/-- A prime-order automorphism fixes an actual Mathieu section pointwise.
This definition carries a subgroup and a surjective quotient map. -/
@[expose] def HasMathieuFixedSection (S : Type*) [Group S] (p : ℕ) : Prop :=
  ∃ a : MulAut S, orderOf a = p ∧ IsSectionOf M22 a.fixedSubgroup

variable {S U : Type*} [Group S] [Group U]

theorem HasMathieuFixedSection.of_mulEquiv {p : ℕ}
    (h : HasMathieuFixedSection S p) (e : S ≃* U) : HasMathieuFixedSection U p := by
  obtain ⟨a,ha,hsec⟩ := h
  let b := MulAut.congr e a
  let f : a.fixedSubgroup →* b.fixedSubgroup :=
    (e.toMonoidHom.comp a.fixedSubgroup.subtype).codRestrict _ (fun x => by
      rw [MulAut.mem_fixedSubgroup]
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply,(MulAut.mem_fixedSubgroup _ _).mp x.property])
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (e.injective (congrArg Subtype.val he))
  exact ⟨b,(MulAut.congr e).orderOf_eq a |>.trans ha,hsec.ambient_injective f hf⟩

private theorem section_card_dvd (h : IsSectionOf M22 S) : 443520 ∣ Nat.card S := by
  obtain ⟨B,f,hf⟩ := h
  rw [←m22_order]
  exact (card_dvd_of_surjective f hf).trans B.card_subgroup_dvd_card

theorem HasMathieuFixedSection.card_dvd {p : ℕ} (h : HasMathieuFixedSection S p) :
    443520 ∣ Nat.card S := by
  obtain ⟨a,ha,hsec⟩ := h
  exact (section_card_dvd hsec).trans a.fixedSubgroup.card_subgroup_dvd_card

theorem HasMathieuFixedSection.section {p : ℕ} (h : HasMathieuFixedSection S p) :
    IsSectionOf M22 S := by
  obtain ⟨a,_,hsec⟩ := h
  exact hsec.ambient_injective a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective

theorem no_mathieu_self_fixed_section {p : ℕ} (hp : 1 < p) :
    ¬ HasMathieuFixedSection M22 p := by
  rintro ⟨a,ha,hsec⟩
  have hproper : a.fixedSubgroup ≠ ⊤ := by
    intro hh
    have he : a = 1 := by
      apply MulEquiv.ext
      intro x
      exact (MulAut.mem_fixedSubgroup _ _).mp (hh ▸ mem_top x)
    rw [he,orderOf_one] at ha
    omega
  have hlt : Nat.card a.fixedSubgroup < Nat.card M22 :=
    Set.ncard_lt_card (show (a.fixedSubgroup : Set M22) ≠ Set.univ from
      fun hh => hproper (SetLike.coe_injective hh))
  exact (not_le_of_gt hlt) hsec.card_le

private theorem not_alternating_section (h : IsSectionOf M22 S)
    {n : ℕ} (hn : n ≤ 9) (e : S ≃* alternatingGroup (Fin n)) : False := by
  have hd : 11 ∣ Nat.card S := (by decide : 11 ∣ 443520).trans (section_card_dvd h)
  rw [Nat.card_congr e.toEquiv] at hd
  have hh := (alternatingGroup (Fin n)).card_subgroup_dvd_card
  rw [Nat.card_perm,Nat.card_fin] at hh
  have hbad := hd.trans (hh.trans (Nat.factorial_dvd_factorial hn))
  norm_num [Nat.factorial] at hbad

private theorem not_binary_linear_section (h : IsSectionOf M22 S)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL S n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := e.trans (Atlas.fieldEquivPSL n ef)
  have hd : 11 ∣ Nat.card S := (by decide : 11 ∣ 443520).trans (section_card_dvd h)
  rw [Nat.card_congr a.toEquiv] at hd
  have hs := hd.trans (card_quotient_dvd_card (center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))
  have hgl := hs.trans (card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective)
  rcases hn with rfl | rfl
  all_goals
    rw [Matrix.card_GL_field,ZMod.card] at hgl
    norm_num [Fin.prod_univ_succ] at hgl

private theorem not_odd_linear_three_section (h : IsSectionOf M22 S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL S 3 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨B,f,hf⟩ := h.ambient_injective e.toMonoidHom e.injective
  have hr := Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
    (hF.symm ▸ ho) B f.ker
  rw [primeRank_equiv 2 (QuotientGroup.quotientKerEquivOfSurjective f hf)] at hr
  have hl := m22_four_le_twoRank
  omega

private theorem not_odd_unitary_three_section (h : IsSectionOf M22 S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU S 3 q) : False := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  obtain ⟨B,f,hf⟩ := h.ambient_injective e.toMonoidHom e.injective
  have hr := Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
    J (hF.symm ▸ ho.pow) B f.ker
  rw [primeRank_equiv 2 (QuotientGroup.quotientKerEquivOfSurjective f hf)] at hr
  have hl := m22_four_le_twoRank
  omega

private theorem not_odd_linear_two_section (h : IsSectionOf M22 S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL S 2 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := hF.symm ▸ ho
  have hfield : GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
    have hc : Nat.card F = ringChar F ^ (n : ℕ) := by
      simpa only [Nat.card_eq_fintype_card] using hn
    refine ⟨ringChar F,n,hp,?_,n.pos,hc⟩
    apply hp.odd_of_ne_two
    intro he
    have heven : Even (Nat.card F) := by
      rw [hc,he]
      exact Nat.even_pow.mpr ⟨by decide,n.pos.ne'⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨B,g,hg⟩ := h.ambient_injective e.toMonoidHom e.injective
  let π := Theory.PSL2.quotientMap F
  let U := B.comap π
  let f := g.comp (π.subgroupComap B)
  have hf : Function.Surjective f := hg.comp
    (π.subgroupComap_surjective_of_surjective B (Theory.PSL2.quotientMap_surjective F))
  let P : Sylow 2 U := Sylow.nonempty.some
  let j := Matrix.SpecialLinearGroup.toGL.comp (U.subtype.comp (P : Subgroup U).subtype)
  have hj : Function.Injective j := Matrix.SpecialLinearGroup.toGL_injective.comp
    (U.subtype_injective.comp (P : Subgroup U).subtype_injective)
  let Q := P.mapSurjective hf
  have hr := Theory.SpecificGroups.OddThreeSectionRank.gl2_twoGroup_image_twoRank_le_three
    hfield (Field.two_ne_zero_of_odd_card F hodd) P.isPGroup' j hj
    (f.subgroupMap (P : Subgroup U)) (f.subgroupMap_surjective _)
  change primeRank 2 Q ≤ 3 at hr
  rw [←Q.primeRank_eq] at hr
  have hl := m22_four_le_twoRank
  omega

/-- All odd-characteristic Theorem C families are excluded using the actual
Mathieu section, without assuming that its numerator is quasisimple. -/
theorem HasMathieuFixedSection.not_odd {p : ℕ} (h : HasMathieuFixedSection S p)
    (hm : IsTheoremCOddModel S) : False := by
  cases hm with
  | linear_two q n hq ho hn he => exact not_odd_linear_two_section h.section ho.pow he
  | linear_three q hq ho he => exact not_odd_linear_three_section h.section ho he
  | unitary_three q hq ho he => exact not_odd_unitary_three_section h.section ho he

end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 ClassificationModels Sporadic.Mathieu
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped MatrixGroups
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

private theorem not_section_of_exponent_four {S : Type*} [Group S] [Finite S]
    (h : IsSectionOf M22 S)
    (hS : ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 4 = 1) : False := by
  obtain ⟨U,f,hf⟩ := h
  have hh := exponent_four_of_section hS U f hf
  obtain ⟨x,hx⟩ := m22_exists_order_eight
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 3) (by
    simpa only [Nat.card_zpowers,show (2 : ℕ)^3 = 8 from rfl] using hx)
  have hs : x ^ 4 = 1 := congrArg Subtype.val (hh (zpowers x) hp ⟨x,mem_zpowers x⟩)
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd

/-- The binary rank-one rows cannot even have an M₂₂ section: its order-eight
element survives every surjection on Sylow subgroups. Suzuki is three-free. -/
theorem not_bender_section {S : Type*} [Group S] [Finite S]
    (h : IsSectionOf M22 S) (hm : IsBenderModel S) : False := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let d := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
    apply not_section_of_exponent_four (h.ambient_injective d.toMonoidHom d.injective)
    intro P hP x
    rw [show (4 : ℕ) = 2 * 2 from rfl,pow_mul,
      Matrix.SpecialLinearGroup.twoSubgroup_pow_two P hP x,one_pow]
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S e.toEquiv
    exact not_section_of_exponent_four (h.ambient_injective e.toMonoidHom e.injective)
      (unitary_exponent_four J (by omega) hF hconj)
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    have hd : 3 ∣ Nat.card S := (by decide : 3 ∣ 443520).trans (section_card_dvd h)
    rw [Nat.card_congr e.toEquiv] at hd
    exact suzukiMatrixGroup_three_free m (by omega) hd
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 ClassificationModels Sporadic.Mathieu
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups

private theorem not_binary_linear_three_section {S : Type*} [Group S]
    (h : IsSectionOf M22 S) {n : ℕ} (hm : ClassicalGroup.IsPSL S 3 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hsec := h.ambient_injective e.toMonoidHom e.injective
  let π := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F))
  obtain ⟨B,g,hg⟩ := hsec
  let U := B.comap π
  let f := g.comp (π.subgroupComap B)
  have hf : Function.Surjective f := hg.comp
    (π.subgroupComap_surjective_of_surjective B (QuotientGroup.mk'_surjective _))
  have hSL : IsSectionOf M22 (Matrix.SpecialLinearGroup (Fin 3) F) := ⟨U,f,hf⟩
  apply not_section_of_exponent_four hSL
  intro P hP x
  obtain ⟨k,hk⟩ := hP x
  have hj : Function.Injective (Representation.specialLinearNatural (k := F) 3) := by
    intro x y hh
    apply Subtype.ext
    exact Matrix.toLin'.injective hh
  exact Subtype.ext (Representation.BinaryTwoPowerDegree.pow_eq_one_of_finrank_le
    (Representation.specialLinearNatural (k := F) 3) hj (m := 2) (by simp)
    (x : Matrix.SpecialLinearGroup (Fin 3) F) (congrArg Subtype.val hk))

private theorem not_binary_symplectic_section {S : Type*} [Group S]
    (h : IsSectionOf M22 S) {n : ℕ} (hm : ClassicalGroup.IsPSp S 2 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  apply not_section_of_exponent_four (h.ambient_injective d.toMonoidHom d.injective)
  intro P hP x
  obtain ⟨k,hk⟩ := hP x
  exact Subtype.ext (Theory.SpecificGroups.SymplecticFour.TwoPower.pow_four_eq_one_of_pow_two_pow_eq_one
    (x : Theory.SpecificGroups.SymplecticFour.Sp F) k (congrArg Subtype.val hk))

/-- The three remaining binary exceptional families in the odd-local comparison. -/
@[expose] def RemainingOddLocalRankTwoModel (S : Type*) [Group S] : Prop :=
  (∃ n, 2 ≤ n ∧ IsG2At S (2 ^ n)) ∨
  (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (S ≃* ReeF4.Model m))

theorem HasMathieuFixedSection.rank_two_rows {S : Type*} [Group S] {p f : ℕ}
    (h : HasMathieuFixedSection S p) (hm : IsTheoremCRankTwoModel S f) :
    RemainingOddLocalRankTwoModel S := by
  cases hm with
  | linear hn hm => exact (not_binary_linear_three_section h.section hm).elim
  | symplectic hn hm => exact (not_binary_symplectic_section h.section hm).elim
  | g2 hn hm => exact Or.inl ⟨f,hn,hm⟩
  | triality hn hm => exact Or.inr (Or.inl ⟨f,hn,hm⟩)
  | ree_f4 m hm hf iso => exact Or.inr (Or.inr ⟨m,hm,iso⟩)
  | symplectic_derived hf iso =>
    have hd := (h.of_mulEquiv
      (iso.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).card_dvd
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  | g2_derived hf iso =>
    have hd := (h.of_mulEquiv iso.some).card_dvd
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits hf iso =>
    have hd := (h.of_mulEquiv iso.some).card_dvd
    rw [Tits.parrottGroup_card] at hd
    norm_num at hd

private theorem not_fixed_section_of_mathieu_embedding
    {S : Type*} [Group S] [Finite S] (hz : center S = ⊥)
    (hi : Function.Surjective (MulAut.conj : S →* MulAut S))
    (j : S →* M24) (hj : Function.Injective j)
    {p : ℕ} (hp : p.Prime) (hpgt : 3 < p) : ¬ HasMathieuFixedSection S p := by
  rintro ⟨a,ha,hs⟩
  obtain ⟨x,rfl⟩ := hi a
  have hxo : orderOf x = p :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) x).symm.trans ha
  obtain ⟨q,hq,hqd,hneq,hoq,hlarge⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ 443520 ∧
      p ≠ q ∧ Odd q ∧ 21 < p * q := by
    by_cases he : p = 11
    · exact ⟨5,by decide,by decide,by omega,by decide,by omega⟩
    · exact ⟨11,by decide,by decide,he,by decide,by omega⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' q (hqd.trans (section_card_dvd hs))
  have hyc : x * (y : S) = (y : S) * x := by
    have hh := (MulAut.mem_fixedSubgroup _ _).mp y.property
    change x * (y : S) * x⁻¹ = y at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hyord : orderOf (y : S) = q := (orderOf_coe y).trans hy
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hneq (((Nat.dvd_prime hq).mp hd).resolve_left hp.ne_one))
  have hxy : orderOf (j (x * y)) = p * q := by
    rw [orderOf_injective j hj]
    exact (Commute.orderOf_mul_eq_mul_orderOf_of_coprime hyc
      (by rw [hxo,hyord]; exact hcop)).trans (by rw [hxo,hyord])
  have ho : Odd (p*q) := (hp.odd_of_ne_two (by omega)).mul hoq
  rcases M24OddCyclic.oddOrderSpectrum (j (x * y))
    (by rw [hxy]; exact ho.not_two_dvd_nat) with hh | hh | hh | hh
  · omega
  · rw [hxy] at hh
    exact Nat.not_prime_mul hp.ne_one hq.ne_one hh
  · omega
  · omega

/-- Prime-order odd automorphisms of M₂₃ cannot fix an M₂₂ section. -/
theorem no_mathieu_odd_fixed_m23 {p : ℕ} (hp : p.Prime) (hgt : 3 < p) :
    ¬ HasMathieuFixedSection M23 p := by
  let j : M23 →* M24 := (MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp
    m23ToM24PointStabilizer
  exact not_fixed_section_of_mathieu_embedding M23Geometry.m23_center_eq_bot
    m23_conj_surjective j (Subtype.val_injective.comp m23ToM24PointStabilizer_injective) hp hgt

/-- The same native odd-order spectrum excludes M₂₄. -/
theorem no_mathieu_odd_fixed_m24 {p : ℕ} (hp : p.Prime) (hgt : 3 < p) :
    ¬ HasMathieuFixedSection M24 p :=
  not_fixed_section_of_mathieu_embedding M24InvolutionCentralizers.center_eq_bot
    M24OuterRestriction.conj_surjective (MonoidHom.id _) Function.injective_id hp hgt
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 Sporadic.LeechRelated.HS

/-- An odd-prime automorphism of HS fixing an M₂₂ section would centralize
a conjugate of the concrete point stabilizer, whose centralizer is trivial. -/
theorem no_mathieu_odd_fixed_hs {p : ℕ} (hp : p.Prime) (hgt : 3 < p) :
    ¬ HasMathieuFixedSection Carrier p := by
  rintro ⟨a,ha,hsec⟩
  have houter := outer_isPGroup_two_of_pointStabilizer_map pointStabilizer_map
    normalizer_relIndex_dvd_two_pow
  have hin : a ∈ MulAut.innerSubgroup Carrier := by
    apply (QuotientGroup.eq_one_iff a).mp
    let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
    obtain ⟨n,hn⟩ := houter (q a)
    have hq : (q a)^p = 1 := by rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_left.mpr (hp.odd_of_ne_two (by omega))).pow_left n)
      (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hq)
  obtain ⟨x,rfl⟩ := hin
  let C := (MulAut.conj x).fixedSubgroup
  have hdiv : 443520 ∣ Nat.card C := by
    obtain ⟨U,f,hf⟩ := hsec
    rw [←Sporadic.Mathieu.m22_order]
    exact (card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card
  have hi : C.index ∣ 100 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 443520)).mp
    have hh := Nat.mul_dvd_mul_right hdiv C.index
    rw [C.card_mul_index,NormalizerIndex.card_carrier] at hh
    exact hh
  let : MulAction pointStabilizer (Carrier ⧸ C) :=
    MulAction.compHom (Carrier ⧸ C) pointStabilizer.subtype
  obtain ⟨z,hz⟩ := MulAction.exists_fixedPoint_of_smallMaximalIndex_dvd
    (G := pointStabilizer) (X := Carrier ⧸ C) (d := 11)
    (fun U hU hsize => SmallIndex.pointStabilizer_smallMaximalIndex U hU
      (hsize.trans (Nat.le_of_dvd (by decide) hi)))
    (fun hd => (by decide : ¬11 ∣ 100) (hd.trans hi))
  obtain ⟨g,rfl⟩ := Quotient.exists_rep z
  have hcentral : g * x * g⁻¹ ∈ centralizer (pointStabilizer : Set Carrier) := by
    intro y hy
    have hfix := hz ⟨y,hy⟩
    change (QuotientGroup.mk (y*g) : Carrier ⧸ C) = QuotientGroup.mk g at hfix
    have hm : g⁻¹*y*g ∈ C := by
      simpa only [mul_assoc] using (QuotientGroup.eq.mp hfix.symm)
    have hh := (MulAut.mem_fixedSubgroup _ _).mp hm
    change x*(g⁻¹*y*g)*x⁻¹ = g⁻¹*y*g at hh
    have he := mul_inv_eq_iff_eq_mul.mp hh
    have he' := congrArg (fun z : Carrier => g*z*g⁻¹) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using he'.symm
  rw [PointCentralizer.centralizer_pointStabilizer_eq_bot] at hcentral
  have hx : x = 1 := (MulAut.conj g).injective ((mem_bot.mp hcentral).trans (map_one _).symm)
  rw [hx,map_one,orderOf_one] at ha
  omega
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 ClassificationModels Sporadic.Mathieu
variable {S : Type*} [Group S]

/-- The actual model possibilities after the section-rank and finite-order sieve. -/
@[expose] def RemainingOddLocalModel (S : Type*) [Group S] : Prop :=
  RemainingOddLocalRankTwoModel S ∨ Nonempty (S ≃* Janko4.Model)

private theorem sporadic_remaining {S : Type*} [Group S] {p : ℕ} (hp : 1 < p)
    (h : HasMathieuFixedSection S p) (hm : IsTheoremCSporadicModel S) :
    Nonempty (S ≃* M23) ∨ Nonempty (S ≃* M24) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨ Nonempty (S ≃* Janko4.Model) := by
  have hd := h.card_dvd
  rcases hm with ⟨name,hn,⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card M11 at hd
      rw [m11_order] at hd
      norm_num at hd
    | m12 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card M12 at hd
      rw [m12_order] at hd
      norm_num at hd
    | m22 => exact (no_mathieu_self_fixed_section hp (h.of_mulEquiv e)).elim
    | m23 => exact Or.inl ⟨e⟩
    | m24 => exact Or.inr (Or.inl ⟨e⟩)
    | hs => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    | j4 => exact Or.inr (Or.inr (Or.inr ⟨e⟩))
    | j2 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
      norm_num at hd
    | j3 => exact (hn rfl).elim
    | he =>
      rw [Nat.card_congr e.toEquiv] at hd
      have hh := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound
        Held.NormalizerGraph.Orbital.held_le_preservingGroup
        (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd
          Held.NormalizerGraph.Orbital.held_le_preservingGroup)
      have hb := hd.trans hh
      norm_num at hb
    | ru =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card Rudvalis.Model at hd
      rw [Rudvalis.model_card] at hd
      norm_num at hd
  · rw [Nat.card_congr e.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd

/-- A nontrivial odd action fixing the actual M₂₂ section excludes all
odd-characteristic, alternating, rank-one and classical rank-two C rows, and all sporadics
apart from J₄. -/
theorem HasMathieuFixedSection.theoremC_rows [Finite S] {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (h : HasMathieuFixedSection S p) (hm : IsTheoremCModel S) :
    RemainingOddLocalModel S := by
  cases hm with
  | alternating n hn iso =>
    exact (not_alternating_section h.section (by omega) iso.some).elim
  | odd hm => exact (h.not_odd hm).elim
  | bender hm => exact (not_bender_section h.section hm).elim
  | rank_two f hm => exact Or.inl (h.rank_two_rows hm)
  | linear_binary n hn hm => exact (not_binary_linear_section h.section hn hm).elim
  | sporadic hm =>
    rcases sporadic_remaining (by omega) h hm with he | he | hs | hj
    · exact (no_mathieu_odd_fixed_m23 hp hgt (h.of_mulEquiv he.some)).elim
    · exact (no_mathieu_odd_fixed_m24 hp hgt (h.of_mulEquiv he.some)).elim
    · exact (no_mathieu_odd_fixed_hs hp hgt (h.of_mulEquiv hs.some)).elim
    · exact Or.inr hj
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
