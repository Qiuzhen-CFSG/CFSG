module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOpposedKernelRadical
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSylow

/-!
# Generation by the two opposed point kernels

The two actual point kernels have distinct nontrivial images on the original
rank-four module.  The first fixes the exchanged four and moves the original
four; the second has the opposite behavior.  Since the plane-stabilizer image
is the elementary four, these two images generate it.  Pulling the equality
back through the actual actor gives the literal generation by `d.R`, `N`, and
`Nᵍ`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem point_stabilizer_eq_S_generation (d : LocalData G)
    (i : OrthogonalPlaneIndex) :
    planeStabilizer d.T (d.action.plane i) = d.S := by
  apply le_antisymm
  · intro x hx
    have hn : (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
        (normalizer (d.action.plane i : Set G)).subgroupOf d.M := hx.2
    rw [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker] at hn
    refine ⟨hx.1, ?_⟩
    change (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M
    rwa [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]
  · exact le_inf inf_le_left (OutsideStructure.LocalBranches.s_normalizes_plane d i)

omit [Finite G] in
private theorem center_image_le_centralizer_generation (N : Subgroup G) :
    (center N).map N.subtype ≤ centralizer (N : Set G) := by
  rintro _ ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

/-- The literal rank-two Sylow is generated over the original radical by the
two opposed point kernels attached to an actual outside element. -/
theorem binary_three_source_opposed_kernel_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    d.S = d.R ⊔ (centralizer ({z} : Set G)).pCoreIn 2 ⊔
      ((centralizer ({z} : Set G)).pCoreIn 2).conjBy g := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let Ng := N.conjBy g
  let H := intrinsicFour c.L
  let V := d.V
  let S := d.S
  let R := d.R
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hrad := binary_three_source_opposed_kernel_radical
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm g hgT hgS
  have hR : R = (d.T : Subgroup G) ⊓ centralizer (V : Set G) :=
    htwo.2.2.2.2.1
  have hSleT : S ≤ (d.T : Subgroup G) := inf_le_left
  have hSN : S ≤ normalizer N := (le_sup_right.trans hLS).trans
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
  have hNS : N ≤ S := by
    change N ≤ d.S
    exact hP ▸ pCoreIn_le_sylow C P
  have hRS : R ≤ S := R_le_S d hR
  have hNgS : Ng ≤ S := by
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    have hTS : (d.T : Subgroup G) ≤ normalizer S :=
      (normal_subgroupOf_iff_le_normalizer (show S ≤ (d.T : Subgroup G) from hSleT)).mp
        (normal_of_index_eq_two hi)
    have hSg : S.map (MulAut.conj g).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
    have hNS : N ≤ S := by
      change N ≤ d.S
      exact hP ▸ pCoreIn_le_sylow C P
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNS
    rwa [hSg] at hh
  have hRN : (d.T : Subgroup G) ≤ normalizer R := by
    have hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G) :=
      d.sylow_le.trans (OutsideStructure.LocalBranches.m_normalizes_y d)
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    have hTS : (d.T : Subgroup G) ≤ normalizer S :=
      (normal_subgroupOf_iff_le_normalizer (show S ≤ (d.T : Subgroup G) from hSleT)).mp
        (normal_of_index_eq_two hi)
    have hYS : (d.T : Subgroup G) ≤ normalizer ((d.Y ⊔ S : Subgroup G) : Set G) :=
      (le_inf hTY hTS).trans (normalizer_inf_normalizer_le_normalizer_sup d.Y S)
    change (d.T : Subgroup G) ≤ normalizer (d.R : Set G)
    rw [htwo.2.2.1]
    exact hYS.trans (normalizer_le_normalizer_characteristic_image _ _)
  have hRg : R.conjBy g = R := mem_normalizer_iff_map_conj_eq.mp (hRN hgT)
  have hIdx : R.relIndex N = 2 := hrad.2.2.2
  have hIdxg : R.relIndex Ng = 2 := by
    have hh := relIndex_map_map_of_injective
      (f := (MulAut.conj g).toMonoidHom) R N (MulAut.conj g).injective
    change (R.conjBy g).relIndex (N.conjBy g) = R.relIndex N at hh
    rw [hRg] at hh
    exact hh.trans hIdx
  have hHNg : H ≤ centralizer (Ng : Set G) := by
    have hh := (binary_three_source_binary_opposed_class_two
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
        (K.map q) hBK (Or.inl rfl) hm g⁻¹ (d.T.inv_mem hgT)
          (fun hi => hgS (d.S.inv_mem_iff.mp hi))).1.trans
      (center_image_le_centralizer_generation N)
    have hh' := map_mono (f := (MulAut.conj g).toMonoidHom) hh
    have hh'' := hh'.trans (map_centralizer_le_centralizer_image
      (N : Set G) (MulAut.conj g).toMonoidHom)
    change (H.conjBy g⁻¹).conjBy g ≤ _ at hh''
    rwa [conjBy_inv'] at hh''
  obtain ⟨_, hFH, _, hex⟩ := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  rw [hFH] at hex
  have hHV : H ≤ V := le_sup_left.trans (hex g hgT hgS).le
  have hRcentral : R ≤ centralizer (V : Set G) := hR ▸ inf_le_right
  have hmeet : N ⊓ R = N ⊓ centralizer (H : Set G) := hrad.2.2.1
  have hNnotR : ¬ N ≤ R := by
    intro hle
    have : R.relIndex N = 1 := by
      rw [← inf_relIndex_left, inf_eq_left.mpr hle, relIndex_self]
    omega
  have hSplane : planeStabilizer d.T (d.action.plane 1) = S :=
    point_stabilizer_eq_S_generation d 1
  let ι : S →* d.M := inclusion (hSleT.trans d.sylow_le)
  let f : S →* OrthogonalActor := d.action.actor.comp ι
  have hfker : f.ker = R.subgroupOf S := by
    ext x
    change (ι x) ∈ d.action.actor.ker ↔ (x : G) ∈ R
    rw [d.action.ker_actor]
    change (x : G) ∈ centralizer (V : Set G) ↔ (x : G) ∈ R
    rw [hR]
    exact (and_iff_right (hSleT x.property)).symm
  have himage : f.range = d.action.image S := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨ι s, s.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have himagecard : Nat.card f.range = 4 := by
    rw [himage]
    rw [← hSplane]
    exact d.action.card_image_planeStabilizer d.T d.sylow_le 1
  let NS := N.subgroupOf S
  let NgS := Ng.subgroupOf S
  let RS := R.subgroupOf S
  let AN := NS.map f
  let ANg := NgS.map f
  have hANcard : Nat.card AN = 2 := by
    change Nat.card (NS.map f) = 2
    rw [← relIndex_ker NS f, hfker, relIndex_subgroupOf hNS]
    exact hIdx
  have hANgcard : Nat.card ANg = 2 := by
    change Nat.card (NgS.map f) = 2
    rw [← relIndex_ker NgS f, hfker, relIndex_subgroupOf hNgS]
    exact hIdxg
  have hNgfix : Ng ≤ centralizer (H : Set G) := le_centralizer_iff.mp hHNg
  have hANne : AN ≠ ANg := by
    intro heq
    obtain ⟨n, hnN, hnR⟩ := SetLike.not_le_iff_exists.mp hNnotR
    let ns : S := ⟨n, hNS hnN⟩
    have hmem : f ns ∈ ANg := by
      rw [← heq]
      exact mem_map_of_mem f (show ns ∈ NS from hnN)
    obtain ⟨m, hmNg, hfm⟩ := hmem
    have hker : ns * m⁻¹ ∈ f.ker := by
      change f (ns * m⁻¹) = 1
      rw [map_mul, map_inv, ← hfm, mul_inv_cancel]
    have hr : (ns * m⁻¹ : S) ∈ R.subgroupOf S := hfker ▸ hker
    have hrC : ((ns : G) * (m : G)⁻¹) ∈ centralizer (H : Set G) := by
      have hr' : ((ns : G) * (m : G)⁻¹) ∈ R := hr
      exact centralizer_le hHV (hRcentral hr')
    have hmC : (m : G) ∈ centralizer (H : Set G) := hNgfix hmNg
    have hnC : (n : G) ∈ centralizer (H : Set G) := by
      have he : (n : G) = ((ns : G) * (m : G)⁻¹) * (m : G) := by simp [ns]
      rw [he]
      exact (centralizer (H : Set G)).mul_mem hrC hmC
    have : n ∈ N ⊓ centralizer (H : Set G) := ⟨hnN, hnC⟩
    have : n ∈ N ⊓ R := by rwa [hmeet]
    exact hnR this.2
  have hdis : Disjoint AN ANg := by
    apply disjoint_iff.mpr
    have hdiv : Nat.card ↥(AN ⊓ ANg : Subgroup OrthogonalActor) ∣ Nat.card AN :=
      card_dvd_of_le (show AN ⊓ ANg ≤ AN from inf_le_left)
    rw [hANcard] at hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hc | hc
    · exact card_eq_one.mp hc
    · have ha : AN ⊓ ANg = AN :=
        eq_of_le_of_card_ge inf_le_left (by rw [hc, hANcard])
      have hb : AN ⊓ ANg = ANg :=
        eq_of_le_of_card_ge inf_le_right (by rw [hc, hANgcard])
      exact (hANne (ha.symm.trans hb)).elim
  let : NS.Normal := normal_subgroupOf_of_le_normalizer hSN
  have hANnorm : ANg ≤ normalizer AN :=
    (map_mono (f := f) (show NgS ≤ normalizer NS from le_normalizer_of_normal)).trans
      (le_normalizer_map f)
  have hsupcard : Nat.card ↥(AN ⊔ ANg : Subgroup OrthogonalActor) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint AN ANg hANnorm hdis,
      hANcard, hANgcard]
  have hjoinImage : AN ⊔ ANg = f.range := by
    apply eq_of_le_of_card_ge
    · exact sup_le (map_le_range f NS) (map_le_range f NgS)
    · rw [hsupcard, himagecard]
  let KS := RS ⊔ NS ⊔ NgS
  have hmapK : KS.map f = f.range := by
    rw [show KS = RS ⊔ NS ⊔ NgS from rfl, Subgroup.map_sup, Subgroup.map_sup]
    have hRmap : RS.map f = ⊥ := (map_eq_bot_iff RS).mpr hfker.ge
    rw [hRmap, bot_sup_eq, hjoinImage]
  have hKtop : KS = ⊤ := by
    apply top_unique
    intro s _
    have hm : f s ∈ KS.map f := by
      rw [hmapK]
      exact ⟨s, rfl⟩
    obtain ⟨k,hk,hfk⟩ := hm
    have hr : s * k⁻¹ ∈ R.subgroupOf S := by
      rw [← hfker]
      change f (s * k⁻¹) = 1
      rw [map_mul, map_inv, ← hfk, mul_inv_cancel]
    have he : s = (s * k⁻¹) * k := by simp
    rw [he]
    exact KS.mul_mem (show s * k⁻¹ ∈ KS from (show RS ≤ KS from le_sup_left.trans le_sup_left) hr)
      (show k ∈ KS from hk)
  have hmapKambient : KS.map S.subtype = R ⊔ N ⊔ Ng := by
    rw [Subgroup.map_sup, Subgroup.map_sup,
      map_subgroupOf_eq_of_le (show R ≤ S from R_le_S d hR),
      map_subgroupOf_eq_of_le hNS, map_subgroupOf_eq_of_le hNgS]
  apply le_antisymm
  · intro s hs
    have hm : (⟨s, hs⟩ : S) ∈ KS := hKtop ▸ mem_top _
    exact hmapKambient ▸ mem_map_of_mem S.subtype hm
  · exact sup_le (sup_le hRS hNS) hNgS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
