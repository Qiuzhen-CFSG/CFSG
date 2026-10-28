module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualKernel
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.KernelCounterexample
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Torus
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Complete
public import Theory.Alternating.FivePairTorusAxes
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace
public import Theory.GroupAction.CardFourCubic.Conjugation
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPlaneMovement

/-!
# The actual cubic Cartan in the field-four tensor configuration

The section kernel fixes the full module. The original odd-normalizer control
therefore makes the intrinsic Hall Cartan faithful on the component section.
It embeds in an elementary abelian torus of order nine. Such a full torus has
no nonzero fixed vector in the tensor module, whereas the original H-star
group fixes a central Sylow involution. Thus the Hall Cartan has order three,
and the generation parameter is two in the nontrivial branch. Its action on
the tensor line is trivial, identifying it with the line-centralizing part of
the extended torus and proving that the old residual moves the tensor plane.

The odd-normalizer premise is the independent source 4.4.3 input. Recognition
of the old residual modulo its two-core is not asserted here.
Source: Aschbacher--Smith 9.2.5--7, printed pp.731--732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- A torus of order nine in the original component orbit fixes no nonidentity module element. -/
theorem three_torus_fixed_eq_one (C : Subgroup G) (hCR : C ≤ localOrbit T L)
    (hC : IsPGroup 3 C) (hc : Nat.card C = 9)
    {v : D.fullModule} (hv : (v : G) ∈ centralizer (C : Set G)) : v = 1 := by
  let R := localOrbit T L
  let a := m.firstMarking.symm.prodCongr m.firstMarking.symm
  let r : C →* Binary.G := m.quotient.comp (inclusion hCR)
  let q := a.toMonoidHom.comp r
  have hi : Function.Injective r := by
    have hi := Theory.AlternatingFive.injective_on_three_subgroup m.quotient
      (m.kernel_eq ▸ (pCore_isPGroup (p := 2) (G := R)))
      (C.subgroupOf R) hC.comap_subtype
    exact hi.comp (subgroupOfEquivOfLe hCR).symm.injective
  have hq : Function.Injective q := a.injective.comp hi
  have haxes := Theory.AlternatingFive.nine_torus_coordinate_kernels q hq hC hc
  let E := ((MonoidHom.snd _ _).comp q).ker
  have hE : Nat.card E = 3 := haxes.2.1
  have hne : E ≠ ⊥ := by
    intro hh
    rw [hh,Subgroup.card_bot] at hE
    omega
  obtain ⟨b,hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb2 : (r b).2 = 1 := by
    have hb : m.firstMarking.symm (r b).2 = 1 := b.property
    exact m.firstMarking.symm.map_eq_one_iff.mp hb
  have hb3 : b^3 = 1 := hE ▸ pow_card_eq_one'
  have hb3' : (r b).1 ^ 3 = 1 := by
    have hh := congrArg (fun x : E => (r x).1) hb3
    simpa using hh
  have hb1 : (r b).1 ≠ 1 := by
    intro hh
    apply hbne
    apply Subtype.ext
    apply hi
    change r (b : C) = r 1
    rw [map_one]
    exact Prod.ext hh hb2
  have hord : orderOf (r b).1 = 3 := orderOf_eq_prime hb3' hb1
  have hfix : Binary.action (r b) (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd := by
    have hh := m.sectionData.equivariant (inclusion hCR b) v
    have he : (⟨(b : G)*(v : G)*(b : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized (hCR b.val.property)) v).mp v.property⟩ :
        D.fullModule) = v := by
      apply Subtype.ext
      change (b : G)*(v : G)*(b : G)⁻¹ = v
      rw [hv b b.val.property,mul_inv_cancel_right]
    change (m.sectionData.coordinates ⟨(b : G)*(v : G)*(b : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized (hCR b.val.property)) v).mp v.property⟩).toAdd =
        Binary.action (r b) _ at hh
    rw [he] at hh
    exact hh.symm
  have hz : (m.sectionData.coordinates v).toAdd = 0 := by
    have hleft : (r b).1.val * (m.sectionData.coordinates v).toAdd =
        (m.sectionData.coordinates v).toAdd := by
      simpa only [Binary.action_apply,hb2,inv_one,Matrix.SpecialLinearGroup.coe_one,mul_one] using hfix
    funext i j
    have hh := SL2FourNatural.cubic_fixed_eq_zero (r b).1 hord
      (fun k => (m.sectionData.coordinates v).toAdd k j) (by
        funext k
        exact congrArg (fun A : Binary.V => A k j) hleft)
    exact congrFun hh i
  apply Subtype.ext
  exact (m.sectionData.coordinates_eq_one_iff v).mp (Multiplicative.toAdd.injective hz)

/-- The actual H-star fixed involution excludes a torus of order nine inside H. -/
theorem hstar_three_subgroup_card_ne_nine {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBR : B ≤ localOrbit T L)
    (hB : IsPGroup 3 B) : Nat.card B ≠ 9 := by
  intro h9
  obtain ⟨z,hz2,hzV,hzT⟩ := m.exists_central_involution_tensorLine
  have hzΩ : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨m.tensorLine_le_sylow hzV,hz2 ▸ pow_orderOf_eq_one z,hzT⟩
  have hz : (⟨z,m.tensorLine_le_fullModule hzV⟩ : D.fullModule) = 1 :=
    m.three_torus_fixed_eq_one B hBR hB h9 (fun b hb =>
      ((m.hstar_centralizes_sylowOmega hH) (hBH hb) z hzΩ).symm)
  have hzone := congrArg Subtype.val hz
  change z = 1 at hzone
  rw [hzone,orderOf_one] at hz2
  omega

/-- Source 4.4.3 control removes the section kernel from the intrinsic Hall Cartan. -/
theorem hstar_faithful_hall_data
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    ∃ n : ℕ, IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H ∧
        d.witness.abelianGroup.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  obtain ⟨n,hg,hb,d,hm,_⟩ := source_a5_hstar_cartan_data D e m.sylow_not_normalizes_component hH hlarge
  have hk : d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ := by
    by_contra hk
    obtain ⟨p,A,hp,ho,hA,hAe,hAY,hAC,hAS⟩ := source_hall_sectionKernel_elementary hH.1.1.2 _ d hk
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    have hout := source_a5_hstar_elementary_hall_escape_of_source4413 D e
      m.sylow_not_normalizes_component (NormalizerEscape.source4413One_knownSimple G)
      hH hlarge d hm hp A hAe hAY hAS
    apply hout
    exact hcontrol p hp ho (A.map H.subtype)
      (fun hb => hA ((map_eq_bot_iff_of_injective A H.subtype_injective).mp hb))
      (IsElementaryAbelian.map H.subtype) hAC
      ((le_inf (map_subtype_le A) hAC).trans (m.hstar_sectionKernel_centralizes_fullModule hH)) hAS
  refine ⟨n,hg,hb,d,hm,?_⟩
  apply bot_unique
  rintro x ⟨⟨a,ha,rfl⟩,hC⟩
  have ha1 : a = 1 := by
    have ham : a ∈ d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H := ⟨ha,hC⟩
    simpa only [hk,mem_bot] using ham
  simp only [ha1,map_one,mem_bot]

/-- A cubic element of H normalizing the tensor line centralizes that line. -/
theorem hstar_cubic_centralizes_tensorLine {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (b : G) (hbH : b ∈ H) (hbN : b ∈ normalizer (m.tensorLine : Set G))
    (hb3 : b^3 = 1) : b ∈ centralizer (m.tensorLine : Set G) := by
  let a := m.tensorLine.normalizerMonoidHom ⟨b,hbN⟩
  have ha3 : a^3 = 1 := by
    change m.tensorLine.normalizerMonoidHom ⟨b,hbN⟩ ^ 3 = 1
    rw [←map_pow]
    have hh : (⟨b,hbN⟩ : normalizer (m.tensorLine : Set G))^3 = 1 := Subtype.ext hb3
    rw [hh,map_one]
  have ha : a = 1 := by
    by_contra hane
    obtain ⟨z,hz2,hzV,hzT⟩ := m.exists_central_involution_tensorLine
    have hzΩ : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
      (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨m.tensorLine_le_sylow hzV,hz2 ▸ pow_orderOf_eq_one z,hzT⟩
    apply Theory.GroupAction.CardFourCubic.moves_nonidentity m.card_tensorLine a ha3 hane ⟨z,hzV⟩
    · intro hh
      have hz1 : z = 1 := congrArg Subtype.val hh
      rw [hz1,orderOf_one] at hz2
      omega
    · apply Subtype.ext
      change b*z*b⁻¹ = z
      rw [←m.hstar_centralizes_sylowOmega hH hbH z hzΩ,mul_inv_cancel_right]
  have hk : (⟨b,hbN⟩ : normalizer (m.tensorLine : Set G)) ∈
      m.tensorLine.normalizerMonoidHom.ker := ha
  rwa [normalizerMonoidHom_ker] at hk

/-- The original orbit Borel normalizes the tensor line. -/
theorem borel_normalizes_tensorLine :
    sourceOrbitBorel T L ≤ normalizer (m.tensorLine : Set G) := by
  have hBR : sourceOrbitBorel T L ≤ localOrbit T L := (map_subtype_le _).trans inf_le_left
  have hBN : sourceOrbitBorel T L ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) :=
    (map_subtype_le _).trans inf_le_right
  change sourceOrbitBorel T L ≤
    normalizer (((T : Subgroup G) ⊓ localOrbit T L : Subgroup G) : Set G) at hBN
  exact (le_inf (hBR.trans m.sectionData.normalized)
    (hBN.trans (normalizer_le_normalizer_centralizer
      ((T : Subgroup G) ⊓ localOrbit T L)))).trans inf_normalizer_le_normalizer_inf

omit m [Finite G] in
private theorem card_le_three_of_dvd_nine {n : ℕ} (hn : n ∣ 9) (hne : n ≠ 9) : n ≤ 3 := by
  obtain ⟨k,hk,hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show n ∣ 3^2 from hn)
  interval_cases k <;> norm_num at hke <;> omega

/-- The actual Hall Cartan is cyclic of order three and is marked by the original tensor line. -/
theorem hstar_cartan_of_control
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    generationParameter H = 2 ∧
    ∃ B A : Subgroup G, B ≤ H ∧ B ≤ (pResidual 2 H).map H.subtype ∧
      B ≤ A ∧ A ≤ sourceOrbitBorel T L ∧ Nat.card A = 9 ∧
      IsElementaryAbelian 3 A ∧ Nat.card B = 3 ∧ IsCyclic B ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal)) ∧
      B = A ⊓ centralizer (m.tensorLine : Set G) := by
  obtain ⟨n,hg,hn,d,hm,hfaith⟩ := m.hstar_faithful_hall_data hcontrol hH hlarge
  let BH := d.witness.abelianGroup
  let B := BH.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hBHM : BH ≤ D.maximalLocal.subgroupOf H := by
    simpa only [←hm] using d.hall_le
  have hBM : B ≤ D.maximalLocal := map_le_iff_le_comap.mpr hBHM
  have hodd : Odd (Nat.card B) := by
    rw [card_map_of_injective H.subtype_injective]
    exact d.witness.odd
  obtain ⟨A,hBA,hAB,hHallA,hA9,hAe⟩ := source_a5_hstar_faithful_odd_subgroup_hall_torus
    D e m.sylow_not_normalizes_component hH B hBH hBM hodd hfaith
  have hAR : A ≤ localOrbit T L := hAB.trans ((map_subtype_le _).trans inf_le_left)
  have hBR : B ≤ localOrbit T L := hBA.trans hAR
  have hBp : IsPGroup 3 B := hAe.isPGroup.to_le hBA
  have hB9 : Nat.card B ∣ 9 := hA9 ▸ card_dvd_of_le hBA
  have hBsmall := card_le_three_of_dvd_nine hB9
    (m.hstar_three_subgroup_card_ne_nine hH B hBH hBR hBp)
  have hcyc : 2^n-1 ≤ Nat.card B := by
    rw [card_map_of_injective H.subtype_injective]
    exact d.witness.card ▸ Nat.card_le_card_of_injective
      (inclusion d.witness.cyclic_le) (inclusion_injective d.witness.cyclic_le)
  have hn2 : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    have hpos : 0 < 2^n := pow_pos (by decide) _
    omega
  have hgen2 : generationParameter H = 2 := by omega
  have hnexact : n = 2 := by omega
  have hB3 : Nat.card B = 3 := by
    rw [hnexact] at hcyc
    omega
  have hBcube (b : G) (hb : b ∈ B) : b^3 = 1 := by
    have hh : (⟨b,hb⟩ : B)^3 = 1 := hB3 ▸ pow_card_eq_one'
    exact congrArg Subtype.val hh
  have hBL : B ≤ centralizer (m.tensorLine : Set G) := by
    intro b hb
    exact m.hstar_cubic_centralizes_tensorLine hH b (hBH hb)
      (m.borel_normalizes_tensorLine (hAB (hBA hb))) (hBcube b hb)
  have hBK : B ≤ (pResidual 2 H).map H.subtype := by
    intro b hb
    refine ⟨⟨b,hBH hb⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    apply (by decide : Nat.Coprime 2 3).coprime_dvd_right
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hBcube b hb))
  let F := A ⊓ centralizer (m.tensorLine : Set G)
  have hBF : B ≤ F := le_inf hBA hBL
  have hF9 : Nat.card F ≠ 9 := by
    intro hF
    obtain ⟨z,hz2,hzV,_⟩ := m.exists_central_involution_tensorLine
    have hz : (⟨z,m.tensorLine_le_fullModule hzV⟩ : D.fullModule) = 1 :=
      m.three_torus_fixed_eq_one F (inf_le_left.trans hAR) (hAe.isPGroup.to_le inf_le_left) hF
        (fun x hx => (hx.2 z hzV).symm)
    have hz1 : z = 1 := congrArg Subtype.val hz
    rw [hz1,orderOf_one] at hz2
    omega
  have hFsmall : Nat.card F ≤ 3 := card_le_three_of_dvd_nine
    (hA9 ▸ card_dvd_of_le (show F ≤ A from inf_le_left)) hF9
  have hBF_eq : B = F := eq_of_le_of_card_ge hBF (by omega)
  have hBHall : IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal)) := by
    have hhall := hm ▸ d.hall
    have hcard : Nat.card (B.subgroupOf (H ⊓ D.maximalLocal)) =
        Nat.card (BH.subgroupOf (D.maximalLocal.subgroupOf H)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_inf hBH hBM)).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hBHM).toEquiv,
        card_map_of_injective H.subtype_injective]
    have hindex : (B.subgroupOf (H ⊓ D.maximalLocal)).index =
        (BH.subgroupOf (D.maximalLocal.subgroupOf H)).index := by
      have hmap : (D.maximalLocal.subgroupOf H).map H.subtype = H ⊓ D.maximalLocal := by
        rw [subgroupOf_map_subtype,inf_comm]
      have hh := relIndex_map_map_of_injective BH (D.maximalLocal.subgroupOf H) H.subtype_injective
      rw [hmap] at hh
      exact hh
    exact ⟨fun p hp => hhall.p_in_pi_of_p_dvd_card p (hcard ▸ hp),
      fun p hp => hhall.p_in_pi_of_p_dvd_index p (hindex ▸ hp)⟩
  refine ⟨hgen2,B,A,hBH,hBK,hBA,hAB,hA9,hAe,hB3,?_,hBHall,hBF_eq⟩
  exact isCyclic_of_prime_card hB3

/-- Under source 4.4.3 control, the original generation parameter is one or two. -/
theorem hstar_generation_one_or_two_of_control
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H = 1 ∨ generationParameter H = 2 := by
  by_cases hn : 1 < generationParameter H
  · exact Or.inr (m.hstar_cartan_of_control hcontrol hH hn).1
  · have hp := source_hstar_generation_positive D hH
    exact Or.inl (by omega)

/-- The constructed cubic Cartan supplies the old-residual plane-movement premise of 9.3.6--7. -/
theorem old_residual_moves_tensorPlane_of_control
    (hcontrol : ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G) := by
  obtain ⟨_,B,A,_,hBK,hBA,hAB,_,_,hB3,_⟩ := m.hstar_cartan_of_control hcontrol hH hlarge
  exact m.old_residual_moves_tensorPlane_of_cartan H B hBK
    (hBA.trans (hAB.trans ((map_subtype_le _).trans inf_le_left))) hB3

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
