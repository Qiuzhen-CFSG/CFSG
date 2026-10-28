module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorBinaryBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.LinearTorus
public import Theory.NumberTheory.BinarySignedTorus

/-!
# Binary field degree in the original tensor H-star

For the actual KT of QuietTensorBinaryBorel, a generation parameter greater
than one supplies the source odd Hall subgroup of M intersect KT. The
proved Hall action is faithful and has three-group image in the original
SL₃(2) orbit. Thus no prime greater than three divides this overlap.
The literal component Borel has Cartan divisor 2^n - 1; its arithmetic
forces n = 2. Consequently a larger binary degree has parameter one in
KT itself, not merely in a quotient or an unrelated model.

The final theorem applies this calculation to the actual detected component
and every original cubic Sylow. The parameter-one binary extension, adequate
Held row, tensor recognition, remaining 8.3 centralizer arguments and quiet
fixed-support exclusions stay with qt-d-10-nona5-point-selection. This is
checked progress toward 8.3.7, not its full model exclusion.
Source: Aschbacher--Smith 8.3.7 and 10.2.3(ii), pp.724--725,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1 Chapter1.XiEmbedding ChapterF.Source
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem quiet_binaryThree_hstar_no_large_overlap_prime
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ Nat.card (D.maximalLocal.subgroupOf H) := by
  have hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨a⟩
    have hc := Nat.card_congr (cL.symm.trans a).toEquiv
    rw [Matrix.PSL3Two.card_SL,nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  obtain ⟨_,_,_,_,d,he,hperm,_⟩ := source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hBM := he ▸ d.hall_le
  have hHall := he ▸ d.hall
  have hfaith := source_nonnormalHallFaithful hmany L D hmin hn hna H hH hlarge
    d.witness.abelianGroup hBM hHall d.witness.abelian hperm
  have hcentral : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (quiet_hstar_centralizes_omega D hJ hH)
  let c : CentralHall.Context D H d.witness.abelianGroup :=
    ⟨hmany,hmin,hn,hna,hH,hlarge,hcentral,hBM,hHall,d.witness.abelian,hperm,hfaith⟩
  have hthree : IsPGroup 3 d.witness.abelianGroup :=
    CentralHall.isThreeGroup_of_image D _ hBM hfaith
      (CentralHall.LinearThree.source_image_isThreeGroup D c cL)
  let B := d.witness.abelianGroup.subgroupOf (D.maximalLocal.subgroupOf H)
  intro hd
  rw [←B.card_mul_index] at hd
  rcases hp.dvd_mul.mp hd with hcard | hindex
  · rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv] at hcard
    obtain ⟨k,hk⟩ := hthree.exists_card_eq
    rw [hk] at hcard
    have heq := (Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow hcard)
    rcases heq with heq | heq <;> omega
  · exact hHall.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hindex (by change p ≠ 2; omega)

/-- A swapped binary factor of degree greater than two forces parameter one
for its literal H-star. In the larger-parameter branch the original Borel
Cartan divisor contradicts the actual faithful Hall three-group. -/
theorem quiet_tensor_point_binary_degree_or_parameter_one
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hs : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
        ((P : Subgroup d.X).map d.X.subtype) d.Gz K)
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    n = 2 ∨ generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) = 1 := by
  obtain ⟨_,hBM,_,hH,_⟩ :=
    quiet_tensor_point_binary_hstar D hmany hmin hn hJ cL e hbase hzV hz1 hzT P hs hclosure hn2 hm
  by_cases hlarge : 1 < generationParameter (K ⊔ (T : Subgroup G) : Subgroup G)
  · left
    by_contra hn'
    have hn3 : 2 < n := by omega
    obtain ⟨p,hp,hp3,hpdiv⟩ : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2^n-1 := by
      by_cases heq : n = 3
      · subst n
        exact ⟨7,by norm_num,by norm_num,by norm_num⟩
      · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)
    have htorus : 2^n-1 ∣ Nat.card (borel K (T : Subgroup G)) := by
      obtain ⟨S,hS⟩ := SwappedSylow.component_sylow hs
      obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
      exact linear_torus_dvd_borel K (T : Subgroup G) S hS (by omega) hF a
    have hBjoin : borel K (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) :=
      inf_le_left.trans le_sup_left
    have hB : borel K (T : Subgroup G) ≤ D.maximalLocal := by rw [←hBM]; exact inf_le_right
    have hdiv := card_dvd_of_le (subgroupOf_mono (K ⊔ (T : Subgroup G)) hB)
    rw [Nat.card_congr (subgroupOfEquivOfLe hBjoin).toEquiv] at hdiv
    exact quiet_binaryThree_hstar_no_large_overlap_prime D hmany hmin hn hJ cL hH hlarge hp hp3
      (hpdiv.trans (htorus.trans hdiv))
  · right
    have hpos := source_hstar_generation_positive D hH
    omega

/-- The original point-centralizer sieve with the binary H-star, Borel
intersection, and field-degree reduction all supplied on the detected component.
The parameter-one binary extension and adequate Held row remain explicit. -/
theorem quiet_tensor_point_component_analysis
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let P₀ := (P : Subgroup d.X).map d.X.subtype
    ∃ K : Subgroup G,
      K ∈ cComponentsIn d.Gz ∧ ¬ K ≤ D.maximalLocal ∧ IsQuasisimple (XiQuotient K) ∧
      d.Kz = componentOrbit K (T : Subgroup G) ∧ ⁅d.Kz,P₀⁆ = d.Kz ∧
      Nonempty (P₀ ≃* Plane 3) ∧
      ((SwappedFactors (T : Subgroup G) P₀ K ∧
        ((∃ n : ℕ, 2 ≤ n ∧ Even n ∧ Nat.ModEq 3 (2^n) 1 ∧
          ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n) ∧
          K ⊓ D.maximalLocal = borel K (T : Subgroup G) ∧
          (K ⊔ (T : Subgroup G)) ⊓ D.maximalLocal = borel K (T : Subgroup G) ⊔ (T : Subgroup G) ∧
          K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
          generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) ≤ 2 ∧
          (n = 2 ∨ generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) = 1)) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p)) ∨
      (d.Kz = K ∧ (ClassicalGroup.IsPSL (XiQuotient K) 4 2 ∨
        ClassicalGroup.IsPSL (XiQuotient K) 5 2 ∨ Nonempty (XiQuotient K ≃* Held.He)))) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let P₀ := (P : Subgroup d.X).map d.X.subtype
  have hi : LocalInput 3 (T : Subgroup G) d.X P₀ d.Gz :=
    quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hT : IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.Gz :=
    D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases hi.normal_or_detected_containment hA hC hsq hT with
    hnormal | ⟨K,hK,hKn,hcomm,hPK,hX⟩
  · exact (quiet_tensor_point_residual_not_normal D hmany hmin hn hJ cL e hbase
      hzV hz1 hzT hnormal).elim
  have hKH : componentOrbit K (T : Subgroup G) ≤ d.Gz :=
    (componentOrbit_le_sup K (T : Subgroup G)).trans (sup_le hK.mem.1 hzT)
  have he : d.Kz = componentOrbit K (T : Subgroup G) :=
    Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.normalClosure_eq_of_commutator
      hi.complement_le hX hKH hKn hcomm
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hKM : ¬ K ≤ D.maximalLocal := by
    intro hKM
    exact quiet_tensor_point_normalClosure_not_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
      (he.le.trans (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) D.maximalLocal hKM
        (hTM.trans D.maximalLocal.le_normalizer)))
  obtain ⟨_,_,_,_,_,hPplane,_⟩ :=
    quiet_tensor_point_normalClosure_models D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
  refine ⟨K,hK.mem,hKM,hK.quasisimple,he,by change ⁅d.Kz,P₀⁆ = d.Kz; rw [he]; exact hcomm,hPplane,?_⟩
  by_cases hTK : (T : Subgroup G) ≤ normalizer (K : Set G)
  · have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) K le_rfl hTK)
        (le_componentOrbit K (T : Subgroup G))
    have heK : d.Kz = K := he.trans horbit
    rw [horbit] at hKn hcomm hPK
    have hr := InvariantThree.Source.alternatives_knownSimple hi hsq hT hK.mem.1
      hKn hK.quasisimple hPK hcomm
    have hx := quiet_tensor_point_invariant_exclusions D hn e hbase hzV hz1 hzT P
    change ¬ LinearThreeModel 3 (XiQuotient d.Kz) ∧
      ¬ Nonempty (XiQuotient d.Kz ≃* Sporadic.Mathieu.M11) at hx
    rw [heK] at hx
    refine Or.inr ⟨heK,?_⟩
    rcases hr with ⟨_,hs | ⟨_,hl | hsym | hexc⟩⟩ | ⟨_,_,_,hh⟩
    · exact (hs.1.1 hTK).elim
    · exact (hx.1 hl).elim
    · exact (quiet_tensor_point_automizer_not_cyclic D hn e hbase hzV hz1 hzT P hsym.2).elim
    · rcases hexc.2 with hm | h4 | h5
      · exact (hx.2 hm).elim
      · exact Or.inl h4
      · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr hh)
  · let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X P₀ d.Gz K :=
      { toLocalInput := hi
        sqtk := hsq
        component := hK.mem
        quasisimple := hK.quasisimple
        orbit_normal := hKn
        complement_le_orbit := hPK
        orbit_commutator := hcomm
        noncentral := hK.noncentral_component_core
        not_invariant := hTK
        sylow_two := hT }
    obtain ⟨_,hsf,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
    refine Or.inl ⟨hsf,?_⟩
    rcases hm with ⟨n,hnEven,hnMod,hm⟩ | hm
    · have hn0 : n ≠ 0 := by
        intro hn0
        obtain ⟨F,_,_,hF,_⟩ := hm
        have hh := Finite.one_lt_card (α := F)
        simp only [hn0,pow_zero] at hF
        omega
      have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hnEven; omega
      obtain ⟨_,hBM,hEM,hH,hgen⟩ :=
        quiet_tensor_point_binary_hstar D hmany hmin hn hJ cL e hbase hzV hz1 hzT P hs he hn2 hm
      exact Or.inl ⟨n,hn2,hnEven,hnMod,hm,hBM,hEM,hH,hgen,
        quiet_tensor_point_binary_degree_or_parameter_one D hmany hmin hn hJ cL e hbase
          hzV hz1 hzT P hs he hn2 hm⟩
    · exact Or.inr hm

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
