module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.FaithfulSections
public import Theory.GroupTheory.GeneralizedFitting.NormalQuasisimpleImage
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry

/-!
# Cubic barriers for the remaining odd rank-one components

The prime congruences in the swapped branch exclude cubic ratio at most two
on every faithful irreducible component section. The rank-one field bound
reduces this to the checked PSL₂(11) and PSL₂(13) exclusions.

For a self-centralizing normal component, its automorphism rank bounds a
small cubic actor's fixed codimension by four. The Borel degree bound makes
every Irr⁺ section larger than this, so the actor stabilizes the section.
Its faithful central quotient is irreducible on F*, giving the same exclusion
without assuming irreducibility of the original module. NormalizedActor uses
this result on the literal orbit quotient; CommonActor applies it to 12.1.4.

Source: Aschbacher--Smith A.1.42, D.2.7, K.2 and 12.1.4,
printed pp.32,190,453,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem odd_prime_irreducible_two_lt_cubicRatio
    {Q U : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [IsQuasisimple Q]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 2 p) (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    2 < cubicRatio ρ := by
  by_contra hn
  have hc : cubicRatio ρ ≤ 2 := le_of_not_gt hn
  have hfit : generalizedFitting Q = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let e : generalizedFitting Q ≃* Q := (MulEquiv.subgroupCongr hfit).trans topEquiv
  let : IsQuasisimple (generalizedFitting Q) := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup (generalizedFitting Q) := e.isSimpleGroup
  have hz : center (generalizedFitting Q) = ⊥ :=
    (inferInstance : (center (generalizedFitting Q)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  let eqt : (generalizedFitting Q ⧸ center (generalizedFitting Q)) ≃* Q :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hm' : ClassicalGroup.IsPSL
      (generalizedFitting Q ⧸ center (generalizedFitting Q)) 2 (p ^ 1) :=
    ⟨F,inferInstance,inferInstance,by simpa only [pow_one] using hF,⟨eqt.trans eF⟩⟩
  have hi' : IsIrreducible (ρ.comp (generalizedFitting Q).subtype) := by
    rw [hfit]
    exact (irreducible_comp_surjective_iff _ topEquiv.surjective ρ).mpr hi
  have hh : SourceAction ρ := ⟨hsq,inferInstance,hf,hi'⟩
  have hlo : 4 ≤ p ^ 1 := by simpa only [pow_one] using (show 4 ≤ p by omega)
  have hsmall := RankOneSize.source_field_order_le_twentyFive ρ hh hp ho
    (Or.inl rfl) hlo hm' hc
  have hcases : p = 11 ∨ p = 13 := by simp only [pow_one] at hsmall; omega
  rcases hcases with rfl | rfl
  · exact (not_lt_of_ge hc) (RankOneSmall.Eleven.two_lt_cubicRatio ρ hh (by simpa using hm'))
  · exact (not_lt_of_ge hc)
      (RankOneSmall.source_prime_exclusion ρ hh (Or.inl rfl) (by simpa using hm'))

private theorem section_bound
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Q V) (C : Subgroup Q)
    [IsSimpleGroup C] [IsQuasisimple C]
    (hsqC : IsSQTK KnownSimple.IsKnownSimple C)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmC : ClassicalGroup.IsPSL C 2 p) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus σ C I)
    (hfaith : Function.Injective (centralQuotientRepresentation σ C I hI.choose)) :
    2 < cubicRatio (σ.comp C.subtype) := by
  have hh := odd_prime_irreducible_two_lt_cubicRatio
    (centralQuotientRepresentation σ C I hI.choose)
    hsqC hfaith hI.choose_spec.2 hp ho hmC hmod
  apply lt_of_not_ge
  intro hle
  have hs := cubicRatio_subrepresentation_le_nat (σ.comp C.subtype)
    (invariantSubspace σ C I hI.choose) 2 hle
  have hq := cubicRatio_quotient_le_nat _
    (centralSubspace σ C I hI.choose) 2 hs
  exact (not_lt_of_ge hq) hh


theorem local_quotient_component_cubic_barrier
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (hf : Function.Injective ρ)
    (C : Subgroup (XiQuotient (localJoin T L)))
    (hC : IsComponent (XiQuotient (localJoin T L)) C)
    (he : Nonempty (C ≃* XiQuotient L))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient L))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    2 < cubicRatio (ρ.comp C.subtype) ∧
      2 < cubicRatio ((fixedQuotient ρ ⊤).comp C.subtype) := by
  let := hC.2
  let : IsSimpleGroup C := he.some.isSimpleGroup
  have hsqC : IsSQTK KnownSimple.IsKnownSimple C := (IsSQTK.equiv he.some).mpr hsq
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hmC : ClassicalGroup.IsPSL C 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨he.some.trans eF⟩⟩
  obtain ⟨⟨I,hI,hfI⟩,⟨J,hJ,hfJ⟩⟩ := local_quotient_component_sections ρ hf C hC he
  exact ⟨section_bound ρ C hsqC hp ho hmC hmod I hI hfI,section_bound (fixedQuotient ρ ⊤) C hsqC hp ho hmC hmod J hJ hfJ⟩

private theorem odd_prime_source_two_lt_cubicRatio
    {Q U : Type*} [Group Q] [Finite Q]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (h : SourceAction ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting Q) ⧸ center (generalizedFitting Q)) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) : 2 < cubicRatio ρ := by
  by_contra hn
  have hc : cubicRatio ρ ≤ 2 := le_of_not_gt hn
  have hm' : ClassicalGroup.IsPSL
      ((generalizedFitting Q) ⧸ center (generalizedFitting Q)) 2 (p ^ 1) := by
    simpa only [pow_one] using hm
  have hsmall := RankOneSize.source_field_order_le_twentyFive ρ h hp ho
    (Or.inl rfl) (by simpa only [pow_one] using (show 4 ≤ p by omega)) hm' hc
  have hcases : p = 11 ∨ p = 13 := by simp only [pow_one] at hsmall; omega
  rcases hcases with rfl | rfl
  · exact (not_lt_of_ge hc) (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm)
  · exact (not_lt_of_ge hc)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm)

private theorem faithful_central_section_of_simple
    {Q U : Type*} [Group Q] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C : Subgroup Q)
    [IsSimpleGroup C] [IsQuasisimple C]
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus ρ C I) :
    Function.Injective (centralQuotientRepresentation ρ C I hI.choose) := by
  have hz : center C = ⊥ :=
    (inferInstance : (center C).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc := (centralSection_kernel_le_centralizer ρ C C le_rfl I hI hI.choose
    C.le_normalizer (mem_map_of_mem C.subtype ha)).2
  have hm : a ∈ center C := mem_center_iff.mpr (fun b =>
    Subtype.ext ((mem_centralizer_iff.mp hc) b b.property))
  exact hz ▸ hm

private theorem small_actor_stabilizes_rank_one_seed
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C A : Subgroup Q)
    [IsSimpleGroup C] [IsQuasisimple C]
    (hn : A ≤ normalizer (C : Set Q)) (hd : fixedCodim ρ A ≤ 4)
    {p : ℕ} (ho : Odd p) (hp : 11 ≤ p) (hm : ClassicalGroup.IsPSL C 2 p)
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus ρ C I) :
    A ≤ subspaceStabilizer ρ I := by
  have hfaith := faithful_central_section_of_simple ρ C I hI
  have hdegree := ChapterG.Section07.OddCharacteristic.psl2_frobenius_degree_bound
    (centralQuotientRepresentation ρ C I hI.choose) hfaith ho hm
  have hdim : 5 ≤ Module.finrank (ZMod 2) (I.map (fixedSpace ρ C).mkQ) := by
    have he := (centralQuotientImageEquiv ρ C I).finrank_eq
    omega
  intro a ha
  apply (subspace_map_eq_iff ρ I a).mp
  by_contra hne
  have he := finrank_quotientDiagonal_eq ρ hI (hI.map_normalizer ρ (hn ha))
    (Ne.symm hne) (hn ha)
  have hl := finrank_quotientDiagonal_le_fixedCodim ρ C A I ha
  omega

/-- A faithful action with a self-centralizing normal PSL₂(p), for the remaining
prime congruences, cannot have cubic ratio at most two. No irreducibility of
the original module is assumed. -/
theorem normal_rank_one_cubic_barrier
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q)
    (C : Subgroup Q) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hcent : centralizer (C : Set Q) = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL C 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) : 2 < cubicRatio ρ := by
  have hrank : primeRank 2 Q ≤ 2 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fact p.Prime := ⟨hp⟩
    have hr := Theory.GroupTheory.primeRank_le_of_injective 2 (MulAut.conjNormal : Q →* MulAut C)
      (MulAut.conjNormal_injective_of_centralizer_eq_bot C hcent)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    exact hr.trans (Theory.PSL2.prime_card_automorphism_two_rank F hF (by omega))
  by_contra hn
  obtain ⟨A,hA,hAc,hAd⟩ := (cubicRatio_le_nat_iff ρ 2).mp (le_of_not_gt hn)
  have hd : fixedCodim ρ A ≤ 4 :=
    hAd.trans (Nat.mul_le_mul_left 2 (hA.rank_le_of_primeRank_le hrank))
  have hne : C ≠ ⊥ := by
    intro he
    have hs : Subsingleton C := he ▸ inferInstance
    exact not_subsingleton C hs
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf C hne
  have hAN : A ≤ normalizer (C : Set Q) := by rw [C.normalizer_eq_top]; exact le_top
  have hAI := small_actor_stabilizes_rank_one_seed ρ C A hAN hd ho (by omega) hm I hI
  let J := C ⊔ A
  have hCJ : C ≤ J := le_sup_left
  have hAJ : A ≤ J := le_sup_right
  have hJI : J ≤ subspaceStabilizer ρ I := sup_le hI.choose hAI
  have hJN : J ≤ normalizer (C : Set Q) := sup_le C.le_normalizer hAN
  let σ := centralSectionRepresentation ρ C J I hJI hJN
  have hσ : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hc := (centralSection_kernel_le_centralizer ρ C J hCJ I hI hJI hJN
      (mem_map_of_mem J.subtype ha)).2
    apply Subtype.ext
    exact (mem_bot.mp (hcent ▸ hc))
  let C₀ := C.subgroupOf J
  let : C₀.Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hJN
  let eC : C₀ ≃* C := subgroupOfEquivOfLe hCJ
  let : IsQuasisimple C₀ := IsQuasisimple.of_mulEquiv eC.symm
  have hc₀ : centralizer (C₀ : Set J) = ⊥ := by
    apply bot_unique
    intro a ha
    have hc : (a : Q) ∈ centralizer (C : Set Q) := by
      intro c hc
      exact congrArg Subtype.val (ha ⟨c,hCJ hc⟩ hc)
    exact Subtype.ext (mem_bot.mp (hcent ▸ hc))
  have hfit : generalizedFitting J = C₀ :=
    generalizedFitting_eq_of_quasisimple_centralizer C₀ hc₀
  have hi : IsIrreducible (σ.comp C₀.subtype) := by
    change IsIrreducible ((centralQuotientRepresentation ρ C I hI.choose).comp eC.toMonoidHom)
    exact (irreducible_comp_surjective_iff _ eC.surjective _).mpr hI.choose_spec.2
  have hσc : cubicRatio σ ≤ 2 := by
    let A₀ := A.subgroupOf J
    let : IsElementaryAbelian 2 A := hA.2
    have hA₀ : IsElementaryTwo A₀ := by
      refine ⟨?_,IsElementaryAbelian.subgroupOf hAJ⟩
      intro hz
      exact hA.1 (by rw [←map_subgroupOf_eq_of_le hAJ,show A.subgroupOf J = ⊥ from hz,Subgroup.map_bot])
    let R := invariantSubspace ρ J I hJI
    let N := centralSectionFixedSubspace ρ C J I hJI hJN
    have hcR : IsCubic R.toRepresentation A₀ :=
      cubic_subrepresentation (ρ.comp J.subtype) R
        (fun a ha b hb c hc v => hAc a ha b hb c hc v)
    have hcσ : IsCubic σ A₀ := cubic_quotient R.toRepresentation N hcR
    have hb := fixedCodim_quotient_add_subrepresentation_le R.toRepresentation N A₀
    have hs := fixedCodim_subrepresentation_le (ρ.comp J.subtype) R A₀
    rw [fixedCodim_subgroupOf ρ hAJ] at hs
    apply (cubicRatio_le_nat_iff σ 2).mpr
    refine ⟨A₀,hA₀,hcσ,?_⟩
    rw [rank_subgroupOf hAJ]
    exact (Nat.le_add_right _ _).trans (hb.trans (hs.trans hAd))
  let eF : generalizedFitting J ≃* C := (MulEquiv.subgroupCongr hfit).trans eC
  let : IsSimpleGroup (generalizedFitting J) := eF.isSimpleGroup
  let : IsQuasisimple (generalizedFitting J) := IsQuasisimple.of_mulEquiv eF.symm
  have hz : center (generalizedFitting J) = ⊥ :=
    (inferInstance : (center (generalizedFitting J)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  let eqt : (generalizedFitting J ⧸ center (generalizedFitting J)) ≃* C :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eF
  have hh : SourceAction σ := ⟨hsq.subgroup J,inferInstance,hσ,by rw [hfit]; exact hi⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hm' : ClassicalGroup.IsPSL
      (generalizedFitting J ⧸ center (generalizedFitting J)) 2 p :=
    ⟨F,inferInstance,inferInstance,hF,⟨eqt.trans e⟩⟩
  exact (not_lt_of_ge hσc) (odd_prime_source_two_lt_cubicRatio σ hh hp ho hm' hmod)


end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
