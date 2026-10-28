module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorModels
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Orbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BinaryResidual
public import Theory.GroupTheory.PCoreNormalizerAction.Frattini
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer
public import Theory.GroupTheory.AutomorphismSquareOuterTwo

/-!
# Full original point-centralizer factorization

The even-characteristic swapped rows have a quotient which is the square
of the actual PSL₂ factor. Borel geometry makes the cubic-plane/Sylow join
characteristic in its Sylow normalizer. Its two-residual is the original X
image, and perfect residual recovery lifts normalization. Relative Frattini
then gives G_z = K_z N_{G_z}(X). For odd-prime factors, the square has a
two-group outer automorphism group, so the residual-normalizer factorization
applies directly. The invariant rows are handled by QuietTensorModels.

The proved N_{G_z}(X) ≤ M now gives the exact setwise product G_z = K_z M_z
in every adequate model row. Original point escape shows K_z is not contained
in M. All cubic complements and two-core quotients are the original ones.
The even-degree swapped and Held exclusions, tensor recognition, r > 3,
point-core containment and both quiet exclusions remain with this owner.
Source: Aschbacher--Smith 8.3.7, printed pp.724--725. The binary quotient
calculation follows the existing intrinsic BinaryThreeAction/Even proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1 Chapter1.XiEmbedding InvariantThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {X P H I : Subgroup G}

/-- The actual orbit quotient in the swapped Sylow configuration. -/
theorem swapped_product
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I) :
    Nonempty (XiQuotient (componentOrbit I (T : Subgroup G)) ≃* XiQuotient I × XiQuotient I) := by
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨hi,hm⟩ := SwappedSylow.nonnormal_model_of_theoremsAC hA hC hs.toSwappedInput
  exact SwappedFactorsProof.quotient_product ChapterA.Section03.CComponentCommutation.universal_A_3_7
    hs.toSwappedInput hi (SwappedFactorsProof.quotient_simple hs.toSwappedInput hm)

/-- The original Sylow-intersection normalizer preserves X in the binary pair. -/
theorem swapped_binary_normalizer
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
    let K := componentOrbit I (T : Subgroup G)
    H ⊓ normalizer ((T : Subgroup G) ⊓ K : Set G) ≤ normalizer (X : Set G) := by
  let K := componentOrbit I (T : Subgroup G)
  have hi := hs.toLocalInput
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hi.overgroup
  have hTK := hTH.trans hHKn
  have hXK : X ≤ K := hi.le_of_complement_le hs.complement_le_orbit hHKn
  have hPK : P ≤ K := hs.complement_le_orbit
  obtain ⟨S,hS⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  obtain ⟨e⟩ := swapped_product hs
  have hpc := hi.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput e)
  let : IsElementaryAbelian 3 P := hpc.1
  let ep := complementEquiv hi hPK
  let : IsElementaryAbelian 3 (quotientImage K P) :=
    IsElementaryAbelian.of_surjective ep.toMonoidHom ep.surjective
  have hcard : Nat.card (quotientImage K P) = 9 :=
    (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  have hrank : primeRank 3 (XiQuotient K) ≤ 2 :=
    (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3 (by decide) (by decide)
  let : Group.IsSolvable (quotientImage K P ⊔ (S : Subgroup (XiQuotient K)) : Subgroup _) := by
    rw [hS]
    exact SwappedSylow.quotient_solvable hs.toSwappedInput
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h1 := pCoreIn_mono_of_normalizes (p := 2)
      (show K ≤ H from hKH) hHKn
    obtain ⟨R,hR⟩ := hs.sylow_two
    exact h1.trans ((pCoreIn_le_sylow H R).trans_eq hR)
  have hres : (pResidual 2 (quotientImage K X ⊔ quotientImage K (T : Subgroup G) :
      Subgroup (XiQuotient K))).map
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).subtype = quotientImage K X := by
    have hp : IsPPerfect 2 (X.subgroupOf K) := hi.perfect.of_surjective
      (subgroupOfEquivOfLe hXK).symm.toMonoidHom (subgroupOfEquivOfLe hXK).symm.surjective
    have hnormal : (T : Subgroup G).subgroupOf K ≤ normalizer (X.subgroupOf K : Set K) := by
      rw [←subgroupOf_normalizer_eq hXK]
      exact comap_mono hi.invariant
    have he := embedded_pResidual_join_pGroup (X.subgroupOf K) ((T : Subgroup G).subgroupOf K)
      hp T.isPGroup'.comap_subtype hnormal
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
    rw [map_embedded_pResidual,Subgroup.map_sup] at hh
    exact hh
  have hjoin : quotientImage K P ⊔ (S : Subgroup (XiQuotient K)) =
      quotientImage K X ⊔ quotientImage K (T : Subgroup G) := by
    rw [hS]
    apply le_antisymm (sup_le_sup_right (map_mono (comap_mono hi.complement_le)) _)
    apply sup_le _ le_sup_right
    have he := congrArg (fun A : Subgroup G => quotientImage K A) hi.complement.symm
    dsimp only [quotientImage] at he
    rw [subgroupOf_sup ((pCoreIn_le 2 X).trans hXK) hPK,Subgroup.map_sup] at he
    exact he.le.trans
      (sup_le ((map_mono (comap_mono hi.core_le_two_group)).trans le_sup_right) le_sup_left)
  have hcore : (quotientImage K P ⊔ (S : Subgroup (XiQuotient K))).pCoreIn 2 ≤
      (S : Subgroup (XiQuotient K)) := by
    have hh := pCoreIn_le_sylow (quotientImage K P ⊔ (S : Subgroup (XiQuotient K)))
      (S.subtype (show (S : Subgroup (XiQuotient K)) ≤ quotientImage K P ⊔ S from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  change H ⊓ normalizer ((T : Subgroup G) ⊓ K : Set G) ≤ normalizer (X : Set G)
  intro g hg
  let a := pCoreNormalizerAction 2 K ⟨g,hHKn hg.1⟩
  have ha : (S : Subgroup (XiQuotient K)).map a.toMonoidHom = S := by
    have hh := pCoreNormalizerAction_preserves_image 2 K ((T : Subgroup G) ⊓ K)
      ⟨g,hHKn hg.1⟩ hg.2
    have hei : ((T : Subgroup G) ⊓ K).subgroupOf K = (T : Subgroup G).subgroupOf K := by
      ext x
      exact and_iff_left x.property
    rw [hei] at hh
    change (quotientImage K (T : Subgroup G)).map a.toMonoidHom = quotientImage K (T : Subgroup G) at hh
    rwa [←hS] at hh
  have hpres := SwappedSylow.binary_pair_preserves_join hn hm e S (quotientImage K P)
    (S : Subgroup (XiQuotient K)) hcard hrank hcore le_rfl a ha
  have himage : (quotientImage K X).map a.toMonoidHom = quotientImage K X := by
    rw [←hres,←hjoin,map_embedded_pResidual,hpres]
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hi.perfect
    (hcT.trans hi.invariant) ⟨g,hHKn hg.1⟩ himage

private theorem swapped_binary_factor
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 (2^n)) :
    componentOrbit I (T : Subgroup G) ⊔ (H ⊓ normalizer (X : Set G)) = H := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  obtain ⟨R,hR⟩ := SwappedSylow.orbit_sylow hs
  have hf := relative_sylow_frattini K H hKH hHKn R
  rw [hR] at hf
  apply le_antisymm (sup_le hKH inf_le_left)
  exact hf.ge.trans (sup_le_sup_left
    (le_inf inf_le_left (swapped_binary_normalizer hs hn hm)) K)

private theorem swapped_odd_outer_two
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) :
    IsPGroup 2 (MulAut.Outer (XiQuotient (componentOrbit I (T : Subgroup G)))) := by
  obtain ⟨F,_,_,hF,⟨c⟩⟩ := hm
  have hc := Theory.PSL2.primeField_center_outer_of_equiv hp hodd hF c
  let := hs.quasisimple
  obtain ⟨e⟩ := swapped_product hs
  exact (AutomorphismSquare.outer_isPGroup_two hc.1 hc.2).of_equiv (MulAut.outerCongr e).symm

variable {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The full original point centralizer factors through its actual normal closure. -/
theorem quiet_tensor_point_factor
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
    (d.Gz : Set G) = (d.Kz : Set G) * (d.Mz : Set G) := by
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
    hnormal | ⟨K,hK,hKn,hcomm,hP,hX⟩
  · exact (quiet_tensor_point_residual_not_normal D hmany hmin hn hJ cL e hbase
      hzV hz1 hzT hnormal).elim
  have hKH : componentOrbit K (T : Subgroup G) ≤ d.Gz :=
    (componentOrbit_le_sup K (T : Subgroup G)).trans (sup_le hK.mem.1 hzT)
  have he : d.Kz = componentOrbit K (T : Subgroup G) :=
    Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.normalClosure_eq_of_commutator
      hi.complement_le hX hKH hKn hcomm
  by_cases hTK : (T : Subgroup G) ≤ normalizer (K : Set G)
  · have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) K le_rfl hTK)
        (le_componentOrbit K (T : Subgroup G))
    have heK : d.Kz = K := he.trans horbit
    rw [horbit] at hKn hcomm hP
    have hr := InvariantThree.Source.alternatives_knownSimple hi hsq hT hK.mem.1
      hKn hK.quasisimple hP hcomm
    have hx := quiet_tensor_point_invariant_exclusions D hn e hbase hzV hz1 hzT P
    change ¬ LinearThreeModel 3 (XiQuotient d.Kz) ∧
      ¬ Nonempty (XiQuotient d.Kz ≃* Sporadic.Mathieu.M11) at hx
    rw [heK] at hx
    have hmodels : ClassicalGroup.IsPSL (XiQuotient K) 4 2 ∨
        ClassicalGroup.IsPSL (XiQuotient K) 5 2 ∨ Nonempty (XiQuotient K ≃* Held.He) := by
      rcases hr with ⟨_,hs | ⟨_,hl | hsym | hexc⟩⟩ | ⟨_,_,_,hh⟩
      · exact (hs.1.1 hTK).elim
      · exact (hx.1 hl).elim
      · exact (quiet_tensor_point_automizer_not_cyclic D hn e hbase hzV hz1 hzT P hsym.2).elim
      · rcases hexc.2 with hm | h4 | h5
        · exact (hx.2 hm).elim
        · exact Or.inl h4
        · exact Or.inr (Or.inl h5)
      · exact Or.inr (Or.inr hh)
    apply quiet_tensor_point_invariant_factor D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
    change ClassicalGroup.IsPSL (XiQuotient d.Kz) 4 2 ∨
      ClassicalGroup.IsPSL (XiQuotient d.Kz) 5 2 ∨ Nonempty (XiQuotient d.Kz ≃* Held.He)
    rw [heK]
    exact hmodels
  · let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X P₀ d.Gz K :=
      { toLocalInput := hi
        sqtk := hsq
        component := hK.mem
        quasisimple := hK.quasisimple
        orbit_normal := hKn
        complement_le_orbit := hP
        orbit_commutator := hcomm
        noncentral := hK.noncentral_component_core
        not_invariant := hTK
        sylow_two := hT }
    obtain ⟨_,_,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
    rcases hm with ⟨n,hnEven,_,hm⟩ | ⟨p,hp,hodd,hm⟩
    · have hn0 : n ≠ 0 := by
        intro hn0
        obtain ⟨F,_,_,hF,_⟩ := hm
        have hh := Finite.one_lt_card (α := F)
        simp only [hn0,pow_zero] at hF
        omega
      have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hnEven; omega
      have hf : d.Kz ⊔ (d.Gz ⊓ normalizer (d.X : Set G)) = d.Gz := by
        simpa only [he] using swapped_binary_factor hs hn2 hm
      have hNM := quiet_tensor_point_normalizer_le D hmany hmin
        hn hJ cL e hbase hzV hz1 hzT
      have hNM' : d.Gz ⊓ normalizer (d.X : Set G) ≤ d.Mz := by
        change d.Gz ⊓ normalizer (d.X : Set G) ≤ D.maximalLocal ⊓ d.Gz
        exact le_inf hNM inf_le_left
      have hf' : d.Kz ⊔ d.Mz = d.Gz :=
        le_antisymm (sup_le d.Kz_le_Gz inf_le_right)
          (hf.ge.trans (sup_le le_sup_left (hNM'.trans le_sup_right)))
      exact (congrArg (fun A : Subgroup G => (A : Set G)) hf').symm.trans
        (coe_mul_of_right_le_normalizer_left d.Kz d.Mz
          (inf_le_right.trans (le_normalizer_conjugateSpanBy _ _)))
    · have ho : IsPGroup 2 (MulAut.Outer (XiQuotient d.Kz)) := by
        rw [he]
        exact swapped_odd_outer_two hs hp hodd hm
      exact quiet_tensor_point_factor_of_outer_two D hmany hmin hn hJ cL e hbase hzV hz1 hzT P ho

/-- The literal normal closure escapes the original maximal local subgroup.
This uses the completed full product and the already proved point escape. -/
theorem quiet_tensor_point_normalClosure_not_le
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
    ¬ d.Kz ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  change ¬ d.Kz ≤ D.maximalLocal
  intro hK
  have hf : (d.Gz : Set G) = (d.Kz : Set G) * (d.Mz : Set G) :=
    quiet_tensor_point_factor D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
  apply quiet_point_centralizer_not_le D hmany hJ hzV hzT
  intro g hg
  have hg' : g ∈ (d.Kz : Set G) * (d.Mz : Set G) := by rwa [←hf]
  obtain ⟨k,hk,m,hm,hgm⟩ := hg'
  rw [←hgm]
  exact D.maximalLocal.mul_mem (hK hk) hm.1

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
