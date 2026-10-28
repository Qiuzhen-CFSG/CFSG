module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicSieve
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualBenderCenter
public import Theory.SpecificGroups.SL2.EvenCentralKernel
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The field-four endpoint of the M24 parabolic quotient sieve

An elementary subgroup normalized by the actual maximal Borel meets the
normal simple component: otherwise it fixes the Borel pointwise, contradicting
Borel rigidity and the trivial component centralizer. Borel transitivity
then puts the component Sylow omega subgroup in that elementary subgroup.
An image of order at most four forces the Bender field to have order four
and excludes Suzuki. The linear multiplier and unitary odd-center bounds
remove the full covering centers above both surviving models.

`NonFFSourceMathieuM24Normalization` applies this to the original H and V,
then excludes the unitary model and lifts the residual cover to the same
selected pair. No generation-parameter equality across quotients is used.
Source: Aschbacher--Smith E.2.2, pp.215--216, and 8.2.9, p.720,
refs/quasithin.pdf. Remaining Mathieu rows and ambient J4 recognition
remain with qt-d-1222-nonff-mathieu.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- The original maximal Borel forces its component omega into the
nontrivial elementary image, so bounds that omega by the image size. -/
theorem bender_omega_card_le
    (D M : Subgroup X) [D.Normal] [IsSimpleGroup D]
    (hm : ClassificationModels.IsBenderModel D) (S : Sylow 2 X) (R : Sylow 2 D)
    (hR : (R : Subgroup D) = (S : Subgroup X).subgroupOf D)
    (hM : M.subgroupOf D = normalizer (R : Set D))
    (hC : centralizer (D : Set X) = ⊥)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hne : W ≠ ⊥) (hMW : M ≤ normalizer (W : Set X)) :
    Nat.card (omegaOneAmbient (R : Subgroup D)) ≤ Nat.card W := by
  have hWD : W ⊓ D ≠ ⊥ := by
    intro he
    apply hne
    apply eq_bot_iff.mpr
    intro w hw
    have hα : (MulAut.conjNormal (H := D) : X →* MulAut D) w = 1 := by
      apply Structure.bender_pointwise_borel_eq_one hm R
      intro d hd
      have hdM : (d : X) ∈ M := by
        change d ∈ M.subgroupOf D
        rw [hM]
        exact hd
      have hcW : ⁅w,(d : X)⁆ ∈ W :=
        le_normalizer_iff_commutator_le_left.mp hMW (commutator_mem_commutator hw hdM)
      have hcD : ⁅w,(d : X)⁆ ∈ D :=
        commutator_le_right W D (commutator_mem_commutator hw d.property)
      have hc1 : ⁅w,(d : X)⁆ = 1 := by
        have hh : ⁅w,(d : X)⁆ ∈ W ⊓ D := ⟨hcW,hcD⟩
        simpa only [he,mem_bot] using hh
      apply Subtype.ext
      change w * (d : X) * w⁻¹ = d
      exact mul_inv_eq_one.mp (show (w * (d : X) * w⁻¹) * (d : X)⁻¹ = 1 from hc1)
    exact MulAut.conjNormal_injective_of_centralizer_eq_bot D hC (by
      simpa only [map_one] using hα)
  have hex : ∃ w : X, w ∈ W ⊓ D ∧ w ≠ 1 := by
    by_contra! he
    exact hWD (eq_bot_iff.mpr he)
  obtain ⟨w,hw,hwn⟩ := hex
  let z : D := ⟨w,hw.2⟩
  have hzR : z ∈ R := by
    change z ∈ (R : Subgroup D)
    rw [hR]
    exact hWS hw.1
  have hzQ : z ∈ omegaOneAmbient (R : Subgroup D) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl z hzR (Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian w hw.1))
  have hzn : z ≠ 1 := fun he => hwn (congrArg Subtype.val he)
  have hf := Chapter2.BenderFusion.OmegaNormalizerModels.of_bender_model hm R
  have hQn : omegaOneAmbient (R : Subgroup D) ≠ ⊥ := by
    intro he
    have hh := hf.size
    rw [he,card_bot] at hh
    omega
  have hN : normalizer (omegaOneAmbient (R : Subgroup D) : Set D) =
      normalizer (R : Set D) := by
    let : (omega₁ R (p := 2)).Characteristic := omega₁_characteristic R
    exact SylowCenterAction.normalizer_eq_of_unique_maximal R _ hQn
      (omegaOneAmbient_le _) (normalizer_le_normalizer_characteristic_image
        (R : Subgroup D) (omega₁ R (p := 2)))
      (Structure.bender_sylow_facts hm R).proper
      (Structure.bender_sylow_facts hm R).unique_maximal
  have hle : (omegaOneAmbient (R : Subgroup D)).map D.subtype ≤ W := by
    rintro _ ⟨y,hy,rfl⟩
    by_cases hy1 : y = 1
    · simpa only [hy1,map_one] using W.one_mem
    obtain ⟨b,hb,hby⟩ := hf.transitive z hzQ hzn y hy hy1
    rw [hN,←hM] at hb
    have hh := (mem_normalizer_iff.mp (hMW hb) w).mp hw.1
    have hh' : (b : X) * w * (b : X)⁻¹ = (y : X) := congrArg Subtype.val hby
    change (y : X) ∈ W
    rw [←hh']
    exact hh
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rwa [card_map_of_injective D.subtype_injective] at hc

/-- The actual omega order at most four leaves only the field-four linear
and unitary models. -/
theorem bender_models_of_small_omega
    (D : Type*) [Group D] [Finite D]
    (hm : ClassificationModels.IsBenderModel D) (S : Sylow 2 D)
    (hsmall : Nat.card (omegaOneAmbient (S : Subgroup D)) ≤ 4) :
    ClassicalGroup.IsPSL D 2 4 ∨ ClassicalGroup.IsPSU D 3 4 := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hsize)
    let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let a : Multiplicative F ≃* S := (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive R).trans
      (e.subgroupMap (S : Subgroup D)).symm
    have hp (x : S) : x^2 = 1 := by
      apply a.symm.injective
      rw [map_pow,map_one]
      change 2 • (a.symm x).toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
    have hΩ : omegaOneAmbient (S : Subgroup D) = S := by
      apply le_antisymm (omegaOneAmbient_le _)
      intro x hx
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
        (congrArg Subtype.val (hp ⟨x,hx⟩))
    rw [hΩ,←Nat.card_congr a.toEquiv,Nat.card_congr Multiplicative.toAdd,hsize] at hsmall
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hsmall
    have he : n=2 := by omega
    exact .inl ⟨F,hF,hfin,by simpa [he] using hsize,⟨e⟩⟩
  | unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hsize,hconj,⟨e⟩⟩ := hm
    obtain ⟨C,hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J n (by omega) hsize hconj
    let J0 := ChapterF.Source.Unitary.FormTransport.standardForm J
    let e0 := e.trans
      (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J0.conj 2 n
      (by omega) hsize hconj
    have hcard := (BenderSuzuki.MatrixGroups.HermitianForm.SylowOmega.omega_of_projective_equiv
      J0 hn hsize hfixed rfl e0 S).2.2
    rw [hcard] at hsmall
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hsmall
    have he : n=2 := by omega
    exact .inr ⟨F,hF,hfin,J,by simpa [he] using hsize,
      by simpa [he] using hconj,⟨e⟩⟩
  | suzuki m hm he =>
    rw [BenderSuzuki.MatrixGroups.suzukiSylow_omega_card (by omega) he.some S] at hsmall
    have hb : 2*m+1 ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hsmall
    omega

/-- The original elementary image bounds the normal Bender field, using
only its literal maximal normalization and nonzero star image. -/
theorem source_bender_field_four
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))))
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) ≤ 4) :
    ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) 2 4 ∨
    ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) 3 4 := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := W.map q
  let D := K.map q
  let M := (minimalParabolicMax S hP).map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image S hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hcore := Structure.source_star_minimal_core_free S hP
  have hC : centralizer (D : Set (X ⧸ J)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient D hi.2.1
      (isPGroup_quotient_of_sup_eq_top D (R : Subgroup (X ⧸ J)) R.isPGroup' hi.2.2.2)
      (bot_unique ((minimalParabolicTwoCore_le_core R hcore.1).trans hcore.2.le))
  have hAM : M ≤ normalizer (A : Set (X ⧸ J)) :=
    (map_mono hMW).trans (le_normalizer_map q)
  have hAn : A ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
  let f : (X ⧸ pCore 2 X) →* (X ⧸ J) := QuotientGroup.map _ _ (MonoidHom.id X)
    (by simpa using minimalParabolicTwoCore_le_core S hP)
  have hmap : (W.map (QuotientGroup.mk' (pCore 2 X))).map f = A := by
    rw [map_map]; rfl
  have hsmall : Nat.card A ≤ 4 := by
    rw [←hmap]
    exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_surjective
      (f.subgroupMap _) (f.subgroupMap_surjective _))).trans hcard
  obtain ⟨P,hP'⟩ := R.exists_subgroupOf_eq_of_normal D
  have hB := (Structure.source_original_star_bender S hP hs K hK hgen hm).1
  change M.subgroupOf D = normalizer ((R : Subgroup (X ⧸ J)).subgroupOf D : Set D) at hB
  rw [←hP'] at hB
  exact bender_models_of_small_omega D hm P
    ((bender_omega_card_le D M hm R P hP' hB hC A (map_mono hWS) hAn hAM).trans hsmall)

/-- No covering center survives for the field-four models in a group
with trivial two-core, including the exceptional PSL₂(4) multiplier. -/
theorem field_four_cover_models
    (Q : Type*) [Group Q] [Finite Q] [IsQuasisimple Q]
    (hcore : pCore 2 Q = ⊥)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 4 ∨
      ClassicalGroup.IsPSU (Q ⧸ center Q) 3 4) :
    center Q = ⊥ ∧ (ClassicalGroup.IsPSL Q 2 4 ∨ ClassicalGroup.IsPSU Q 3 4) := by
  have hz : center Q = ⊥ := by
    rcases hm with hl | hu
    · obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hl
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
      have hk : f.ker = center Q := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
      let c : PerfectCentralCovering.Cover Q (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := {
        toMonoidHom := f
        surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
        isPerfect := inferInstance
        ker_le_center := hk.le }
      have hp : IsPGroup 2 (center Q) := hk ▸ Theory.SL2.perfect_central_kernel_isTwoGroup
        2 (by decide) hsize c
      exact bot_unique ((show center Q ≤ pCore 2 Q from le_sSup ⟨inferInstance,hp⟩).trans hcore.le)
    · have ho : Odd (Nat.card (center Q)) := Nat.not_even_iff_odd.mp (fun hd =>
        PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore _ le_rfl
          (even_iff_two_dvd.mp hd))
      have hd := ChapterA.Section02.OddCenterCovers.unitary_center_card_dvd
        (n := 2) (by decide) hu ho
      norm_num at hd
      exact hd
  let c : Q ≃* (Q ⧸ center Q) := MulEquiv.ofBijective (QuotientGroup.mk' (center Q))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hz]),
      QuotientGroup.mk'_surjective _⟩
  refine ⟨hz,?_⟩
  rcases hm with ⟨F,hF,hfin,hsize,⟨e⟩⟩ | ⟨F,hF,hfin,J,hsize,hconj,⟨e⟩⟩
  · exact .inl ⟨F,hF,hfin,hsize,⟨c.trans e⟩⟩
  · exact .inr ⟨F,hF,hfin,J,hsize,hconj,⟨c.trans e⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
