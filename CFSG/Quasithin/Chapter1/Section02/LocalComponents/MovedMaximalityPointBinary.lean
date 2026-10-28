module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairOrders
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityOddModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsHigmanSims
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Moved binary components for an arbitrary local Sylow

For R an arbitrary two-subgroup, retain the Sylow witnesses in the literal
joins B ∨ R and K ∨ R. Restricting to K ∨ R permits reuse of the checked
full-Sylow embedding results. The nonnormal containing models force equality;
the normalized case reduces to the genuine Theorem C catalogue. Existing
component-uniqueness calculations exclude its ordinary rows, and the squared
order of the actual moved binary pair excludes J₄, Held and Rudvalis.
Thus a moved PSL₂(2ⁿ) local component, n > 2, is maximal in L(G,R).

Original 1.2.4 then makes it a component of a containing local group H
when R is Sylow in H. The source orbit bound makes its R-span normal in H.
The Chapter 10 consumer takes R = C_T(v), H = C_G(v); no simple-QTKE
hypothesis is imposed on H and R need not be Sylow in the ambient G.

Source: Aschbacher--Smith, 1.2.1(3), 1.2.4 and 1.2.8(2--3),
printed pp.504--507; model calculations from A.3.12, pp.47--48.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximalityPoint
open MovedMaximality ChapterA.Section03
variable {G : Type*} [Group G] [Finite G]

private def quotientEquiv {B H : Subgroup G} (hBH : B ≤ H) :
    ((B.subgroupOf H) ⧸ pCore 2 (B.subgroupOf H)) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBH))

omit [Finite G] in
/-- Restrict the literal local Sylow to the containing join. -/
private theorem local_sylow {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R)
    (hBK : B ≤ K) :
    ∃ S : Sylow 2 (K ⊔ R : Subgroup G), (S : Subgroup (K ⊔ R : Subgroup G)) = R.subgroupOf (K ⊔ R) ∧
      B.subgroupOf (K ⊔ R) ∈ localCComponents S := by
  obtain ⟨S,hS⟩ := hK.2.1
  have he : (S : Subgroup (K ⊔ R : Subgroup G)) = R.subgroupOf (K ⊔ R) := by
    apply map_injective (K ⊔ R).subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]
  refine ⟨S,he,?_⟩
  rw [he]
  exact ((mem_LIn_iff_subgroupOf le_sup_right (hBK.trans le_sup_left)).mp
    ⟨hBK.trans le_sup_left,hB⟩).1

/-- The source four-model overcomponent analysis retains an arbitrary local Sylow. -/
private theorem chain_eq_or_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R) (hBK : B ≤ K)
    (hmB : NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    B = K ∨ R ≤ normalizer (K : Set G) := by
  let H := K ⊔ R
  have hBH : B ≤ H := hBK.trans le_sup_left
  obtain ⟨S,hS,hb⟩ := local_sylow hB hK hBK
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  rcases proposition_1_2_1_three_index_knownSimple hq hK.1 with hn | ⟨_,hm⟩
  · exact Or.inr (le_sup_right.trans
      ((normal_subgroupOf_iff_le_normalizer (show K ≤ H from le_sup_left)).mp hn))
  · left
    have hnot' : ¬ ClassicalGroup.IsPSL
        ((B.subgroupOf H) ⧸ pCore 2 (B.subgroupOf H)) 2 4 :=
      fun hh => hnot (hh.of_mulEquiv (quotientEquiv hBH).symm)
    have he : B.subgroupOf H = K.subgroupOf H := by
      cases hm with
      | linear_even n hn hmodel =>
        exact eq_of_bender_quotient S hb hK.1 (comap_mono hBK) (.linear n hn hmodel)
      | suzuki m hm hmodel =>
        exact eq_of_bender_quotient S hb hK.1 (comap_mono hBK) (.suzuki m hm hmodel)
      | linear_prime p hp ho hmodel =>
        exact eq_of_primePSL2_quotient S hb hK.1 (comap_mono hBK) hnot' hp ho hmodel
      | janko hmodel =>
        exact eq_of_janko_quotient S hb hK.1 (comap_mono hBK)
          (hmB.of_mulEquiv (quotientEquiv hBH)) hnot' hmodel.some
    simpa only [map_subgroupOf_eq_of_le hBH,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using congrArg (map H.subtype) he

/-- Component uniqueness in the intrinsic Sylow overgroups fixes the smaller component. -/
private theorem normalizes_of_unique
    {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R)
    (hBK : B ≤ K) (hRK : R ≤ normalizer (K : Set G))
    (hu : SylowOvergroupComponentUnique K) : R ≤ normalizer (B : Set G) := by
  let H := K ⊔ R
  have hBH : B ≤ H := hBK.trans le_sup_left
  obtain ⟨S,hS,hb⟩ := local_sylow hB hK hBK
  have hk : (S : Subgroup H) ≤ normalizer (K.subgroupOf H : Set H) := by
    rw [hS,←subgroupOf_normalizer_eq (show K ≤ H from le_sup_left)]
    exact comap_mono hRK
  have hn := SylowOvergroupComponentUnique.normalizes_local_component S hb
    hK.1.subnormal (comap_mono hBK) hk
    (hu.of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  rw [hS,←subgroupOf_normalizer_eq hBH] at hn
  intro r hr
  exact hn (show (⟨r,(show R ≤ H from le_sup_right) hr⟩ : H) ∈ R.subgroupOf H from hr)

private theorem local_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple H := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

/-- A moved local component forces a genuine simple-model obstruction in the containing join. -/
private theorem normalized_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R)
    (hBK : B ≤ K) (hRK : R ≤ normalizer (K : Set G))
    (hm : ¬ R ≤ normalizer (B : Set G)) :
    let C := K.subgroupOf (K ⊔ R)
    let Q := C ⧸ solvableRadical C
    IsSimpleGroup Q ∧ RemainingSimpleModel Q ∧ ¬ SylowOvergroupComponentUnique Q := by
  let H := K ⊔ R
  let C := K.subgroupOf H
  let Q := C ⧸ solvableRadical C
  let hs : IsSimpleGroup Q := hK.1.isSimpleGroup_quotient_solvableRadical
  let := hK.1.perfect
  have hna := hK.1.not_isMulCommutative_quotient_solvableRadical
  have hq := ChapterA.Section03.SourceComponents.GenerationCore.radical_quotient_sqtk
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (local_sqtk hG hK.2.2) hK.1
  have hmodel : LocalModels.TheoremCModel Q :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna
      (ChapterA.Section02.theoremC_knownSimple hs hna hq.stronglyQuasithin hq.isKGroup)
  have hu : ¬ SylowOvergroupComponentUnique Q := by
    intro hu
    let : Group.IsSolvable (QuotientGroup.mk' (solvableRadical C)).ker := by
      rw [QuotientGroup.ker_mk']; infer_instance
    have huC : SylowOvergroupComponentUnique C :=
      hu.of_surjective (QuotientGroup.mk' (solvableRadical C)) (QuotientGroup.mk'_surjective _)
    have huK := huC.of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm
    exact hm (normalizes_of_unique hB hK hBK hRK huK)
  exact ⟨hs,remaining_simple_model_of_not_unique hmodel hu,hu⟩
/-- The actual moved pair has squared radical order dividing the containing quotient. -/
private theorem square_dvd
    {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R)
    (hBK : B ≤ K) (hRK : R ≤ normalizer (K : Set G))
    (hm : ¬ R ≤ normalizer (B : Set G)) :
    Nat.card (B ⧸ solvableRadical B)^2 ∣ Nat.card (K ⧸ solvableRadical K) := by
  let H := K ⊔ R
  have hBH : B ≤ H := hBK.trans le_sup_left
  obtain ⟨S,hS,hb⟩ := local_sylow hB hK hBK
  have hk : (S : Subgroup H) ≤ normalizer (K.subgroupOf H : Set H) := by
    rw [hS,←subgroupOf_normalizer_eq (show K ≤ H from le_sup_left)]
    exact comap_mono hRK
  have hm' : B.subgroupOf H < conjugateSpanBy (B.subgroupOf H) (S : Subgroup H) := by
    refine lt_of_le_of_ne (le_conjugateSpanBy _ _) ?_
    intro he
    have hn := le_normalizer_conjugateSpanBy (B.subgroupOf H) (S : Subgroup H)
    rw [←he,hS,←subgroupOf_normalizer_eq hBH] at hn
    apply hm
    intro r hr
    exact hn (show (⟨r,(show R ≤ H from le_sup_right) hr⟩ : H) ∈ R.subgroupOf H from hr)
  have hd := actual_pair_square_dvd S hb (comap_mono hBK) hk hm'
  change Nat.card ((B.subgroupOf H) ⧸ solvableRadical (B.subgroupOf H))^2 ∣
    Nat.card ((K.subgroupOf H) ⧸ solvableRadical (K.subgroupOf H)) at hd
  let a := subgroupOfEquivOfLe hBH
  let b := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  rwa [Nat.card_congr (QuotientGroup.congr _ _ a (map_solvableRadical_equiv a)).toEquiv,
    Nat.card_congr (QuotientGroup.congr _ _ b (map_solvableRadical_equiv b)).toEquiv] at hd

private theorem binary_square_exclusion
    {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : 2 < n)
    (hmodel : ClassicalGroup.IsPSL X 2 (2^n)) {N : ℕ}
    (hN : N = 145926144000 ∨ N = 86775571046077562880 ∨
      N = 2^12 * (3^3*5^2*7^3*17)) (hd : Nat.card X ^ 2 ∣ N) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc : Nat.card X = 2^n * ((2^n)^2-1) := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
  have hd2 : 2^(n*2) ∣ N := by
    rw [pow_mul]
    exact (pow_dvd_pow_of_dvd (hc ▸ dvd_mul_right _ _) 2).trans hd
  have hhigh : n ≤ 10 := by
    by_contra! hh
    have hbad : 2^22 ∣ N := (pow_dvd_pow 2 (show 22 ≤ n*2 by omega)).trans hd2
    rcases hN with rfl | rfl | rfl <;> norm_num at hbad
  interval_cases n <;> rw [hc] at hd
  all_goals rcases hN with rfl | rfl | rfl <;> norm_num at hd

/-- The normalized overcomponent alternative is impossible for a moved binary
rank-one component larger than A₅, with the literal arbitrary local Sylow. -/
private theorem normalized_binary_impossible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B K : Subgroup G} (hB : B ∈ L G R) (hK : K ∈ L G R)
    (hBK : B ≤ K) (hRK : R ≤ normalizer (K : Set G))
    (hm : ¬ R ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 2 < n) (hbinary : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : False := by
  let C := K.subgroupOf (K ⊔ R)
  let Q := C ⧸ solvableRadical C
  obtain ⟨hs,hmodel,hu⟩ := normalized_obstruction hG hB hK hBK hRK hm
  let := hs
  let := hK.1.perfect
  rcases hmodel with (ha | ha) | ⟨p,hp,ho,unitary,ho3⟩ | hr | hb | hspor
  · exact hu (alternating_seven_sylow_overgroup_component_unique ha)
  · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inr ha)))
  · exact hu (odd_ternary_sylow_overgroup_component_unique hp ho unitary ho3)
  · exact hu (even_sylow_overgroup_component_unique (Or.inl hr))
  · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inl hb)))
  · have hsimple : IsSimpleGroup (B ⧸ pCore 2 B) := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hbinary
      have hlarge : 3 < Nat.card F := by
        rw [hF]
        have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ n by omega)
        norm_num at hpow ⊢
        omega
      let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
      exact e.isSimpleGroup
    let := hsimple
    let := hB.1.perfect
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ R from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ B ⊔ R from le_sup_left)).surjective
    have hrad : solvableRadical B = pCore 2 B := radical_eq_core_of_perfect_simple_core_quotient
    have hd := square_dvd hB hK hBK hRK hm
    rw [hrad] at hd
    let e := (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).symm
    have hcard : Nat.card (K ⧸ solvableRadical K) = Nat.card Q :=
      Nat.card_congr (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).toEquiv
    rw [hcard] at hd
    obtain ⟨name,hname,iso⟩ := sporadic_model_remaining_after_higman_sims hspor hu
    rcases hname with rfl | rfl | rfl
    · rw [Nat.card_congr iso.some.toEquiv] at hd
      change Nat.card (B ⧸ pCore 2 B)^2 ∣ Nat.card Janko4.Model at hd
      rw [Janko4.Cardinality.model_card] at hd
      exact binary_square_exclusion hn hbinary (Or.inr (Or.inl rfl)) hd
    · rw [Nat.card_congr iso.some.toEquiv] at hd
      have hheld : Nat.card Held.He ∣ 2^12 * (3^3*5^2*7^3*17) := by
        have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
        exact Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
          (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)
      exact binary_square_exclusion hn hbinary (Or.inr (Or.inr rfl)) (hd.trans hheld)
    · rw [Nat.card_congr iso.some.toEquiv] at hd
      change Nat.card (B ⧸ pCore 2 B)^2 ∣ Nat.card Rudvalis.Model at hd
      rw [Rudvalis.model_card] at hd
      exact binary_square_exclusion hn hbinary (Or.inl rfl) hd

/-- Source 1.2.8(3) for the binary rank-one quotient consumed by Chapter 10.
The actor is arbitrary; it is required to be Sylow only in each literal local join. -/
theorem binary_mem_LStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B : Subgroup G} (hB : B ∈ L G R)
    (hm : ¬ R ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 2 < n) (hbinary : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) : B ∈ LStar G R := by
  refine ⟨hB,fun K hK hBK => ?_⟩
  rcases chain_eq_or_normalized hG hB hK hBK (.linear_even n (by omega) hbinary) hnot with he | hk
  · exact he.symm
  · exact (normalized_binary_impossible hG hB hK hBK hk hm hn hbinary).elim

/-- Original 1.2.4 and moved maximality make the binary seed a component
of every containing local overgroup with the same full Sylow. -/
theorem binary_component_in_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B H : Subgroup G} (hB : B ∈ L G R) (hBH : B ≤ H)
    (hH : H ∈ Chapter1.H G) (hR : IsSylowIn 2 R H)
    (hm : ¬ R ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 2 < n) (hbinary : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    (B.subgroupOf H).IsCComponent := by
  have hmax := binary_mem_LStar hG hB hm hn hbinary hnot
  obtain ⟨S,hS⟩ := hR
  have hRH : R ≤ H := hS ▸ map_subtype_le _
  have he : (S : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRH]
  have hb : B.subgroupOf H ∈ L H (S : Subgroup H) := by
    rw [he]
    exact (mem_LIn_iff_subgroupOf hRH hBH).mp ⟨hBH,hB⟩
  obtain ⟨K,⟨hK,hBK⟩,_⟩ := lemma_1_2_4_containment_of_A_3_12
    (containment_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
    (uniqueness_local_quotient_sqtk hG hH) S hb
  have hKH : K.map H.subtype ≤ H := map_subtype_le _
  have hcomp : ((K.map H.subtype).subgroupOf H).IsCComponent := by
    change (comap H.subtype (map H.subtype K)).IsCComponent
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact hK
  have hKB : K.map H.subtype = B := hmax.2 _
    (mem_L_of_cComponent hH ⟨S,hS⟩ hKH hcomp) (by
      simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f := H.subtype) hBK)
  exact hKB ▸ hcomp

/-- The literal local Sylow orbit of a relative component is normal in its overgroup. -/
theorem relative_sylow_orbit_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {R B H : Subgroup G} (hBH : B ≤ H) (hH : H ∈ Chapter1.H G)
    (hR : IsSylowIn 2 R H) (hB : (B.subgroupOf H).IsCComponent) :
    H ≤ normalizer (conjugateSpanBy B R : Set G) := by
  obtain ⟨S,hS⟩ := hR
  have hRH : R ≤ H := hS ▸ map_subtype_le _
  let V := conjugateSpanBy (B.subgroupOf H) (S : Subgroup H)
  have horbit := proposition_1_2_1_three_index_knownSimple
    (uniqueness_local_quotient_sqtk hG hH) hB
  have hn : V.Normal := conjugateSpanBy_sylow_normal _ S
    (horbit.imp_right fun h => h.1)
  have he : V.map H.subtype = conjugateSpanBy B R := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hBH,hS]
  have hd : (V.map H.subtype).subgroupOf H = V :=
    comap_map_eq_self_of_injective H.subtype_injective V
  have hv : ((conjugateSpanBy B R).subgroupOf H).Normal := by
    rw [←he,hd]
    exact hn
  exact (normal_subgroupOf_iff_le_normalizer
    (conjugateSpanBy_le hBH (hRH.trans H.le_normalizer))).mp hv

end CFSG.Quasithin.Chapter1.Section02.MovedMaximalityPoint
