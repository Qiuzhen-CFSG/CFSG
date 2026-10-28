module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeResidual
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.LinearRank
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Alternating.Reduction
public import Mathlib.Algebra.Group.Shrink
public import Theory.SpecificGroups.Alternating.FiveCoreHallBound
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup

/-!
# The full two-core quotient of an alternating residual

The genuine quasisimplicity clause of E.2.2 identifies the normal generating
component's two-core quotient. An A₅ radical quotient then has no remaining
central kernel: its only nontrivial perfect central cover has a two-kernel,
which the full two-core already removes. Rank-one E-generation through the
solvable radical gives n(H)≤2, including the outer involution.

In a proper overgroup of a full Sylow two-subgroup of an A₅ or S₅ two-core
extension, every odd subgroup has order at most three. The literal intrinsic
Hall–Cartan data consequently has exponent parameter two and cyclic actor
of order three. AlternatingResidual applies these facts to the original H.

Source: Aschbacher–Smith E.2.2, E.1.14(1), and 11.4.4,
printed pp.214–216,778 of refs/quasithin.pdf; GLS 5.2.9–10 for the
perfect central cover of A₅. All quotient kernels are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

/-- The E.2.2 quasisimple quotient belongs to the specified normal generating component. -/
theorem normal_component_core_quasisimple
    {J : Type*} [Group J] [Finite J] {κ : GroupClass}
    (hQ : IsSQTK κ J) (U : Sylow 2 J)
    (hP : ChapterB.IsMinimalParabolicOver U ⊤)
    (I : Subgroup J) [I.Normal] (hI : I.IsCComponent)
    (hgen : I ⊔ (U : Subgroup J) = ⊤) : IsQuasisimple (I ⧸ pCore 2 I) := by
  have hs : ¬ Group.IsSolvable J := by
    intro h
    let := h
    exact hI.not_isSolvable inferInstance
  obtain ⟨K,hK,hquasi,_,_⟩ := ChapterE.Structure.source_original_component hQ U hP hs
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsNilpotent (J ⧸ I) :=
    (isPGroup_quotient_of_sup_eq_top I U U.isPGroup' hgen).isNilpotent
  have he : K = I := hK.eq_of_le hI (le_of_isPerfect_of_solvable_quotient K I)
  exact he ▸ hquasi

/-- The A₅ radical quotient of a quasisimple two-core quotient is already its full quotient. -/
theorem core_quotient_alternating_five_of_radical
    {J : Type*} [Group J] [Finite J] [IsQuasisimple (J ⧸ pCore 2 J)]
    (hm : Nonempty ((J ⧸ solvableRadical J) ≃* alternatingGroup (Fin 5))) :
    Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hm
  let A := J ⧸ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let er : (A ⧸ solvableRadical A) ≃* alternatingGroup (Fin 5) :=
    (solvableRadicalQuotientEquiv q (QuotientGroup.mk'_surjective _)).symm.trans e
  let a : A →* alternatingGroup (Fin 5) := er.toMonoidHom.comp (QuotientGroup.mk' _)
  have ha : Function.Surjective a := er.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : a.ker = solvableRadical A := by
    rw [MonoidHom.ker_comp_of_injective _ _ er.injective,QuotientGroup.ker_mk']
  have hbot : a.ker = ⊥ := by
    by_contra hn
    let s : Shrink.{0} A ≃* A := Shrink.mulEquiv
    let : Finite (Shrink.{0} A) := Finite.of_equiv A s.symm.toEquiv
    let : Group.IsPerfect (Shrink.{0} A) :=
      Group.IsPerfect.ofSurjective (f := s.symm.toMonoidHom) s.symm.surjective
    let b := a.comp s.toMonoidHom
    have hbc : b.ker ≤ center (Shrink.{0} A) := by
      intro x hx
      apply mem_center_iff.mpr
      intro y
      apply s.injective
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        mem_center_iff.mp (IsQuasisimple.solvableRadical_le_center (hk ▸ hx)) (s y)
    have hbker : b.ker = a.ker.map s.symm.toMonoidHom := MonoidHom.ker_comp_mulEquiv a s
    have hbne : b.ker ≠ ⊥ := by
      rw [hbker]
      exact fun hh => hn ((map_eq_bot_iff_of_injective _ s.symm.injective).mp hh)
    have hc := GLS3.Chapter5.SchurPresentation.natCard_ker_eq_two_of_central_extension_alternatingGroup_five
      b (ha.comp s.surjective) hbc hbne
    rw [hbker,card_map_of_injective s.symm.injective] at hc
    have hp : IsPGroup 2 a.ker := IsPGroup.of_card (n := 1) (by simpa using hc)
    have hl : a.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hp⟩
    exact hn (bot_unique (hl.trans (pCore_quotient_pCore_eq_bot 2).le))
  exact ⟨MulEquiv.ofBijective a ⟨(MonoidHom.ker_eq_bot_iff a).mp hbot,ha⟩⟩

private theorem alternating_simple_socle_generation
    {J : Type*} [Group J] [Finite J] [IsSimpleGroup (generalizedFitting J)]
    (U : Sylow 2 J) (hn : ¬ IsMulCommutative (generalizedFitting J))
    (hgen : generalizedFitting J ⊔ (U : Subgroup J) = ⊤)
    (e : generalizedFitting J ≃* alternatingGroup (Fin 5)) :
    ChapterE.IsEGenerated 2 J := by
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (GaloisField.card 2 2 (by decide))
  intro W
  apply ChapterE.ValuesEvenClassical.RankOneUpper.linear_isEGeneratedAt_of_top_component
    (by decide) (e.trans e4.symm) (SimpleSocle.centralizer_eq_bot hn) W
  intro A hA hAW hne
  exact ChapterE.ValuesEvenClassical.RankOneUpper.eCaseComponent_top hn U hgen
    (W : Subgroup J) A hne

/-- A normal A₅ radical component with a Sylow supplement gives E-generation at rank two. -/
theorem generation_le_two_of_alternating_radical_component
    {J : Type*} [Group J] [Finite J] (U : Sylow 2 J)
    (I : Subgroup J) [I.Normal] (hI : I.IsCComponent)
    (hgen : I ⊔ (U : Subgroup J) = ⊤)
    (hm : Nonempty ((I ⧸ solvableRadical I) ≃* alternatingGroup (Fin 5))) :
    ChapterE.generationParameter J ≤ 2 := by
  let q := QuotientGroup.mk' (solvableRadical J)
  let D := I.map q
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical J))
  have hr : solvableRadical (J ⧸ solvableRadical J) = ⊥ :=
    solvableRadical_quotient_solvableRadical
  have hD : D.IsCComponent := hI.map_quotient (solvableRadical J)
  let : D.Normal := (inferInstance : I.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := hD.isSimpleGroup_of_solvableRadical_eq_bot hr
  have hDn := hD.not_isMulCommutative_of_solvableRadical_eq_bot hr
  have hDgen : D ⊔ (Uq : Subgroup (J ⧸ solvableRadical J)) = ⊤ := by
    change I.map q ⊔ (U : Subgroup J).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have htwo := isPGroup_quotient_of_sup_eq_top D Uq Uq.isPGroup' hDgen
  have hcore := SimpleSocle.pCore_eq_bot hr 2
  have hF := (simple_two_quotient_structure D hDn htwo hcore).1
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf le_rfl
  have hk := kernel_eq_solvableRadical_of_top_isCComponent htop
    (q.subgroupMap I) (q.subgroupMap_surjective I)
  let eI : (I ⧸ solvableRadical I) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap I) (q.subgroupMap_surjective I))
  obtain ⟨ea⟩ := hm
  let eF : generalizedFitting (J ⧸ solvableRadical J) ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hF).trans (eI.symm.trans ea)
  let : IsSimpleGroup (generalizedFitting (J ⧸ solvableRadical J)) :=
    hF.symm ▸ inferInstanceAs (IsSimpleGroup D)
  have hFn : ¬ IsMulCommutative (generalizedFitting (J ⧸ solvableRadical J)) := hF.symm ▸ hDn
  have hFgen : generalizedFitting (J ⧸ solvableRadical J) ⊔ (Uq : Subgroup _) = ⊤ :=
    hF.symm ▸ hDgen
  exact ChapterE.generationParameter_le (by decide)
    (ChapterE.IsEGenerated.of_solvableRadical_quotient (by decide)
      (alternating_simple_socle_generation Uq hFn hFgen eF))


private theorem symmetric_stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by
  have hi : (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hc := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).card_mul_index
  have hs : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hi,hs] at hc
  omega

/-- The odd part of any proper Sylow overgroup of a two-core extension
of A₅ or S₅ has order at most three. -/
theorem odd_subgroup_card_le_three_of_five_core_models
    {J : Type*} [Group J] [Finite J]
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5)))
    (U : Sylow 2 J) (M B : Subgroup J) (hUM : (U : Subgroup J) ≤ M)
    (hM : M ≠ ⊤) (hBM : B ≤ M) (ho : Odd (Nat.card B)) : Nat.card B ≤ 3 := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact Theory.SpecificGroups.Alternating.FiveSylowMaximal.odd_subgroup_card_le_three_of_core_quotient
      e U M B hUM hM hBM ho
  obtain ⟨e⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkM : q.ker ≤ M := hk ▸ (pCore_isPGroup.le_sylow_of_normal U).trans hUM
  have hproper : M.map q ≠ ⊤ := by
    intro hh
    apply hM
    have hh' := congrArg (comap q) hh
    simpa only [comap_map_eq_self hkM,comap_top] using hh'
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.exists_le_point_stabilizer
    (U.mapSurjective hq) (M.map q) (map_mono hUM) hproper
  have hd : Nat.card (B.map q) ∣ 24 := by
    rw [←symmetric_stabilizer_card i]
    exact card_dvd_of_le ((map_mono hBM).trans hi)
  let a := q.comp B.subtype
  have ha : IsPGroup 2 a.ker := by
    rw [←MonoidHom.comap_ker,hk]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  have hinj : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    have hodd := Odd.of_dvd_nat ho a.ker.card_subgroup_dvd_card
    obtain ⟨k,hkcard⟩ := ha.exists_card_eq
    have hkzero : k = 0 := by
      by_contra hh
      exact hodd.not_two_dvd_nat (hkcard ▸ dvd_pow_self 2 hh)
    apply Subgroup.eq_bot_of_card_eq
    exact hkcard.trans (by rw [hkzero]; rfl)
  have hrestrict : Function.Injective (q.subgroupMap B) := by
    intro x y hh
    exact hinj (congrArg Subtype.val hh)
  have hc : Nat.card B = Nat.card (B.map q) :=
    Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap B)
      ⟨hrestrict,q.subgroupMap_surjective B⟩).toEquiv
  rw [←hc] at hd
  exact Nat.le_of_dvd (by decide) ((ho.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left hd)

/-- The E.2.2 Hall actor is exactly cyclic of order three in the remaining
five-point case. Its marked exponent is forced to be two. -/
theorem hall_card_three_of_five_core_models
    {J : Type*} [Group J] [Finite J]
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5)))
    (U : Sylow 2 J) (hP : ChapterB.IsMinimalParabolicOver U ⊤)
    {n : ℕ} (hn : 2 ≤ n)
    (d : ChapterE.Section06.FixedPointBounds.ParabolicCartan.IntrinsicHallCartanData U hP n) :
    n = 2 ∧ Nat.card d.witness.abelianGroup = 3 ∧
      d.witness.cyclicGroup = d.witness.abelianGroup := by
  have hb := odd_subgroup_card_le_three_of_five_core_models hm U
    (ChapterB.minimalParabolicMax U hP) d.witness.abelianGroup
    (ChapterB.minimalParabolicMax_spec U hP).2
    (ChapterB.minimalParabolicMax_spec U hP).1.1 d.hall_le d.witness.odd
  have hc := Nat.card_le_card_of_injective (inclusion d.witness.cyclic_le)
    (inclusion_injective d.witness.cyclic_le)
  rw [d.witness.card] at hc
  have hn3 : n < 3 := by
    by_contra! hh
    have hx := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    norm_num at hx
    omega
  have hn2 : n = 2 := by omega
  have hcard : Nat.card d.witness.abelianGroup = 3 := by
    have hc' : 3 ≤ Nat.card d.witness.abelianGroup := by
      calc
        3 = 2 ^ n - 1 := by rw [hn2]; decide
        _ ≤ _ := hc
    omega
  exact ⟨hn2,hcard,eq_of_le_of_card_ge d.witness.cyclic_le (by
    rw [hcard,d.witness.card,hn2]; decide)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
