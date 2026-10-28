module
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.CoprimeGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanFree
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# Full residual-normalizer fusion of the original natural point

Let K = O²(H), N = N_G(K), and Z₁ = Ω₁Z(T) ∩ V for the actual
FundamentalSetup module. The nonfaithful residual centralizes Z₁ and
therefore its full N-conjugate span U. Characteristic two makes U reduced.
The faithful action N/C_N(U) is solvable, and nine does not divide its
order: the image of the actual quotient-centralizer kernel is a solvable
three-prime group, while its remaining quotient has order dividing twelve.

The original Cartan has order coprime to six in every odd field degree
and satisfies [Z₁,D_L] = Z₁. Thus its displacements normally generate U.
The solvable Thompson-factor argument in CoprimeGeneration forces J(T)
to centralize U. Baumann Frattini now supplies a factorization of all N,
so each N-conjugate of Z₁ is realized in N_G(L), where point TI is proved.
This also handles the self-normalizing index-three C_K H case.

This replaces the Zsigmondy fusion step in Aschbacher–Smith 5.1.17,
printed p.640 (refs/quasithin.pdf), without a product-TI inference.
Solvability of the literal quotient-action kernel remains explicit; its
independent source discharge belongs to qt-f112-linear-suzuki-containment.
Final parity assembly remains with qt-d-1222-linear-field-parity.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}
omit [Finite G] in
/-- A quotient killing the actual residual is solvable and has three-part at most three. -/
theorem residual_trivial_image_solvable_threePart
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (h3 : ¬ 3 ∣ Nat.card
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    {Q : Type*} [Group Q] [Finite Q]
    (f : normalizer (residual H : Set G) →* Q) (hf : Function.Surjective f)
    (hk : (residual H).subgroupOf (normalizer (residual H : Set G)) ≤ f.ker) :
    Group.IsSolvable Q ∧ ¬ 9 ∣ Nat.card Q := by
  let K := residual H
  let N := normalizer (K : Set G)
  let C := (normalizerQuotientAction K (pCore 2 K)).ker
  let D := C.map f
  let : D.Normal := Normal.map inferInstance f hf
  let q := QuotientGroup.mk' D
  let r := q.comp f
  let a := pCoreNormalizerOuterAction 2 K
  have har : a.ker ≤ r.ker := by
    rw [pCoreNormalizerOuterAction_ker]
    apply sup_le
    · intro x hx
      change q (f x) = 1
      rw [show f x = 1 from hk hx,map_one]
    · intro x hx
      exact (QuotientGroup.eq_one_iff (f x)).mpr (mem_map_of_mem f hx)
  have hout : Nat.card (MulAut.Outer (K ⧸ pCore 2 K)) ∣ 12 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := linear_residual_quotient hm
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF
  have hd : Nat.card (Q ⧸ D) ∣ 12 := by
    have he : r.ker.index = Nat.card (Q ⧸ D) := by
      rw [index_ker, r.range_eq_top_of_surjective ((QuotientGroup.mk'_surjective D).comp hf),card_top]
    rw [← he]
    apply (index_dvd_of_le har).trans
    rw [index_ker]
    exact (card_subgroup_dvd_card a.range).trans hout
  have h3D : ¬ 3 ∣ Nat.card D := fun hh => h3
    (hh.trans (card_dvd_of_surjective (f.subgroupMap C) (f.subgroupMap_surjective C)))
  have h9D : Nat.Coprime 9 (Nat.card D) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr h3D).pow_left 2
  let : Group.IsSolvable C := hsolv
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f.subgroupMap_surjective C)
  have hs : Group.IsSolvable (Q ⧸ D) := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hpd
    have hdiv := hpd.trans hd
    have he : 12 = 2^2*3 := by decide
    rw [he] at hdiv
    rcases hp.dvd_mul.mp hdiv with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  refine ⟨(Group.isSolvable_iff_subgroup_quotient D).mpr ⟨inferInstance,hs⟩,?_⟩
  intro h9
  rw [← D.card_mul_index,index_eq_card] at h9
  exact (by decide : ¬ 9 ∣ 12) ((h9D.dvd_of_dvd_mul_left h9).trans hd)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- The unchanged natural point is generated by its original Cartan commutators. -/
theorem fundamental_point_cartan_commutator
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    ⁅Z,A⁆ = Z := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
  let := D.module_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion (show Z ≤ D.moduleSubgroup from inf_le_right)) (inclusion_injective _)
  have hAZ : A ≤ normalizer (Z : Set G) :=
    (c.left_le.trans (fundamental_point_normalizer (H := H) (A := A) D h.sylow_normalizes h.linear hodd hnat).ge).trans
      inf_le_right
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 Z).exists_card_eq
    rw [hk]
    exact ((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6)).pow_right k
  have hfix : Z ⊓ centralizer (A : Set G) = ⊥ := bot_unique
    ((inf_le_inf_right _ (show Z ≤ D.moduleSubgroup from inf_le_right)).trans_eq
      (natural_cartan_fixed_eq_bot h.sylow_normalizes h.linear h.exponent c hnat))
  have he := eq_commutator_sup_centralizer_of_solvable_coprime Z A hAZ inferInstance hcop
  simpa only [hfix,sup_bot_eq] using he.symm

/-- The full residual normalizer factors over the point-span centralizer and Baumann normalizer. -/
theorem fundamental_point_residual_factorization
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    let N := normalizer (residual H : Set G)
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    N = (N ⊓ centralizer (conjugateSpanBy Z N : Set G)) ⊔
      (N ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) := by
  let K := residual H
  let N := normalizer (K : Set G)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
  let U := conjugateSpanBy Z N
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hZT : Z ≤ (T : Subgroup G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1).1
  have hZC : Z ≤ centralizer (T : Set G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have he : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hsq : IsStronglyQuasithin N := (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin
  have hcN := h.qtke.evenCharacteristic T N hmax hTN
  have hchar : centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
    rw [← generalizedFitting_eq_pCore_of_sylow_overgroup T N N hTN le_rfl hcN]
    exact centralizer_generalizedFitting_le N
  let := D.module_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion (show Z ≤ D.moduleSubgroup from inf_le_right)) (inclusion_injective _)
  have hUN : U ≤ N := conjugateSpanBy_le (hZT.trans hTN) N.le_normalizer
  have hr : IsPReduced 2 (U.subgroupOf N) :=
    reduced_conjugateSpan_of_sylow_central T N Z hTN hZT hZC hchar
  let : (U.subgroupOf N).Normal := hr.normal
  let : IsElementaryAbelian 2 (U.subgroupOf N) := hr.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUN).symm.toMonoidHom (subgroupOfEquivOfLe hUN).symm.injective
  have hKC : K ≤ centralizer (Z : Set G) :=
    (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf).trans
      (Subgroup.centralizer_le (show Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) from inf_le_left))
  have hUC : U ≤ centralizer (K : Set G) :=
    conjugateSpanBy_le (le_centralizer_iff.mp hKC) (normalizer_le_normalizer_centralizer K)
  let q := QuotientGroup.mk' (centralizer (U.subgroupOf N : Set N))
  have hqker : q.ker = centralizer (U.subgroupOf N : Set N) := QuotientGroup.ker_mk' _
  have hkq : K.subgroupOf N ≤ q.ker := by
    rw [hqker]
    intro k hk u hu
    exact Subtype.ext ((le_centralizer_iff.mp hUC) hk u hu)
  have h3 := Nat.prime_three.coprime_iff_not_dvd.mp
    (CubicEscape.quotientAction_kernel_three_prime K hsq (linear_residual_quotient hm))
  obtain ⟨hs,h9⟩ := residual_trivial_image_solvable_threePart hm hsolv h3 q
    (QuotientGroup.mk'_surjective _) hkq
  have hAN : A ≤ N := (cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hm).trans
    (map_subtype_le _)
  have hA : Nat.Coprime (Nat.card (A.subgroupOf N)) 6 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv]
    exact cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd
  have hmove : ⁅Z,A⁆ = Z := fundamental_point_cartan_commutator h D c hodd hnat
  have hgen : U.subgroupOf N ≤ conjugateSpanBy ⁅U.subgroupOf N,A.subgroupOf N⁆ ⊤ := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_conjugateSpanBy,map_commutator,map_subgroupOf_eq_of_le hUN,
      map_subgroupOf_eq_of_le hAN,← MonoidHom.range_eq_map,range_subtype]
    exact conjugateSpanBy_mono (hmove ▸ commutator_mono (le_conjugateSpanBy Z N) le_rfl) le_rfl
  have ht := ChapterB.thompson_centralizes_of_coprime_moved_generation
    (U.subgroupOf N) q (QuotientGroup.mk'_surjective _) hqker hs h9 hr.quotient_pCore_eq_bot
    (A.subgroupOf N) hA hgen (T.subtype hTN)
  have hj := map_mono (f := N.subtype) ht
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,map_centralizer_subtype,
    map_subgroupOf_eq_of_le hUN] at hj
  have hf := ChapterB.BaumannFrattini.centralizing_characteristic_factorization
    T N U hTN hUN hj (⊤ : Subgroup (ChapterB.baumann (T : Subgroup G)))
  simpa only [← MonoidHom.range_eq_map,range_subtype] using hf
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
/-- Every residual-normalizer conjugate of the original point is realized in N_G(L). -/
theorem fundamental_point_residual_fusion
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    {g : G} (hg : g ∈ normalizer (residual H : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    ∃ b ∈ normalizer (L : Set G),
      Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom := by
  let N := normalizer (residual H : Set G)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
  let U := conjugateSpanBy Z N
  let C := N ⊓ centralizer (U : Set G)
  let J := N ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
  have hNC : N ≤ normalizer (C : Set G) :=
    (le_inf N.le_normalizer ((le_normalizer_conjugateSpanBy Z N).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hf : N = J ⊔ C := by
    rw [sup_comm]
    exact fundamental_point_residual_factorization h hH hK hnf hm hsolv D c hodd hnat
  have hp : g ∈ (J : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right J C (inf_le_left.trans hNC), ← hf]
    exact hg
  obtain ⟨b,hb,d,hd,rfl⟩ := hp
  refine ⟨b,baumann_normalizer_le_of_nonfaithful_residual h hH hK hnf hb.2,?_⟩
  have he : Z.map (MulAut.conj d).toMonoidHom = Z := by
    have hzfix (z : G) (hz : z ∈ Z) : (MulAut.conj d) z = z := by
      change d * z * d⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hd.2 z
        (le_conjugateSpanBy Z N hz)).symm
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      change (MulAut.conj d) z ∈ Z
      rw [hzfix z hz]
      exact hz
    · intro z hz
      exact ⟨z,hz,hzfix z hz⟩
  have hc : (MulAut.conj (b*d)).toMonoidHom =
      (MulAut.conj b).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  change Z.map (MulAut.conj (b*d)).toMonoidHom = _
  rw [hc,← map_map,he]

/-- Full residual-normalizer TI for the unchanged natural point in every odd degree. -/
theorem fundamental_point_ti_under_residual_normalizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    {g : G} (hg : g ∈ normalizer (residual H : Set G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨b,hb,he⟩ := fundamental_point_residual_fusion h hH hK hnf hm hsolv D c hodd hnat hg
  dsimp only
  rw [he]
  exact fundamental_point_ti_under_normalizer D h.sylow_normalizes h.linear hodd hnat hb
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
