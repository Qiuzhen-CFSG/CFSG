module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorBinaryNumerical
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.BinarySylow
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# Excluding larger binary fields in the original tensor point centralizer

The checked binary Borel geometry puts T intersect K_z inside the original
S = O₂(XT). Consequently the subgroup K_z S is normalized by KT and its
intersection with T is exactly S. Restrict the E-family to this normal
section. The existing low weak-closure and normalizer bounds then place KT
inside M if its generation parameter is one, contradicting component escape.
Together with the actual Hall/Cartan numerical reduction, this forces the
binary degree to be two. The actual PSL₂(4) ≃ PSL₂(5) comparison absorbs
this row into the odd-prime alternative of the original component sieve.

Every original cubic Sylow, the full two-core extension, and the tensor-base
marking are retained. The adequate Held exclusion, tensor recognition,
8.3.8--12, both quiet exclusions, and FixedSupportRowsAt/ModuleChoiceAt remain
with qt-d-10-nona5-point-selection. Final unconditional point control remains
with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 8.3.6--7, printed pp.724--725, using E.3.19 and
the source Hall-faithfulness argument of 10.2.3(ii), printed p.745.
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

/-- The literal binary H-star cannot have parameter one: restrict its
E-family to the normalized orbit joined to the original S. -/
theorem quiet_tensor_binary_parameter_ne_one
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
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
    (hKM : ¬ K ≤ D.maximalLocal)
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 (2^n)) :
    generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) ≠ 1 := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let B := componentOrbit K (T : Subgroup G)
  let Y := B ⊔ d.S
  let H := K ⊔ (T : Subgroup G)
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    le_normalizer_componentOrbit K (T : Subgroup G)
  have hTS : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    le_sup_right.trans (d.XT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.XT (pCore 2 d.XT)))
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (le_inf hTB hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHY : H ≤ normalizer (Y : Set G) :=
    sup_le (((le_componentOrbit K (T : Subgroup G)).trans le_sup_left).trans Y.le_normalizer) hTY
  have hSbound : (T : Subgroup G) ⊓ B ≤ d.S :=
    Chapter1.RadicalExclusions.ModelReduction.binary_swapped_orbit_sylow_le_core hs hn2 hm
  have hinter : (T : Subgroup G) ⊓ Y = d.S := by
    apply le_antisymm _ (le_inf d.S_le_T le_sup_right)
    rintro y ⟨hyT,hyY⟩
    have hyprod : y ∈ (B : Set G) * (d.S : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (d.S_le_T.trans hTB)]
      exact hyY
    obtain ⟨b,hb,s,hsS,hbs⟩ := hyprod
    have hbT : b ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem hyT ((T : Subgroup G).inv_mem (d.S_le_T hsS))
      rwa [←hbs,mul_inv_cancel_right] at hh
    rw [←hbs]
    exact d.S.mul_mem (hSbound ⟨hbT,hb⟩) hsS
  intro hgen
  change generationParameter H = 1 at hgen
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hR : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hg : IsEGeneratedAt 1 R := by
    have hh := isEGenerated_generationParameter_of_pos (G := H) (by omega) R
    rwa [hgen] at hh
  have hHM : H ≤ D.maximalLocal := by
    apply NormalSectionContainment.le_of_isEGenerated (Y := Y) (V := D.fullModule) R hg hHY
    · rw [hR]
      exact (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
    · rw [hR,hinter]
      exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
    · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
        (source_fullModule_normalizer D).le)
    · intro j hj
      rw [hR,hinter]
      exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj
    · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
      decide
  exact hKM (le_sup_left.trans hHM)


/-- Every binary field in the original swapped point-centralizer row has
degree two. The original two-core and exchanging Sylow remain in place. -/
theorem quiet_tensor_point_binary_degree_two
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
    n = 2 := by
  have hKM : ¬ K ≤ D.maximalLocal := by
    intro hKM
    have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
      le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
    exact quiet_tensor_point_normalClosure_not_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
      (hclosure.le.trans (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) D.maximalLocal hKM
        (hTM.trans D.maximalLocal.le_normalizer)))
  exact (quiet_tensor_point_binary_degree_or_parameter_one D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P hs hclosure hn2 hm).resolve_right
      (quiet_tensor_binary_parameter_ne_one D hn e hbase hzV hz1 hzT P hs hKM hn2 hm)

private theorem binary_four_is_prime_five {Q : Type*} [Group Q]
    (hm : ClassicalGroup.IsPSL Q 2 (2^2)) : ClassicalGroup.IsPSL Q 2 5 := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (by simpa using hF)
  obtain ⟨c⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5,inferInstance,inferInstance,by simp,⟨a.trans (b.trans c.symm)⟩⟩

/-- The point-centralizer component sieve after eliminating every larger
binary field. The degree-two overlap is transported through the actual
PSL₂(4) ≃ PSL₂(5) equivalence. The adequate Held row remains. -/
theorem quiet_tensor_point_prime_models
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
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p) ∨
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
    rcases hm with ⟨n,hnEven,_,hm⟩ | hm
    · have hn0 : n ≠ 0 := by
        intro hn0
        obtain ⟨F,_,_,hF,_⟩ := hm
        have hh := Finite.one_lt_card (α := F)
        simp only [hn0,pow_zero] at hF
        omega
      have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hnEven; omega
      have hnTwo := quiet_tensor_point_binary_degree_two D hmany hmin hn hJ cL e hbase
        hzV hz1 hzT P hs he hn2 hm
      subst n
      exact ⟨5,by decide,by decide,binary_four_is_prime_five hm⟩
    · exact hm

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
