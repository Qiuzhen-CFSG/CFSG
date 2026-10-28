module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The two point-centralizer kernels under the original T-exchange

At the original displacement point z, put C = C_G(z) and N = O₂(C),
with N embedded in G. The original full Sylow S contains N and Nᵍ for
every g in T outside S. These are the actual two-cores of C_G(z) and
C_G(gzg⁻¹). They have the same order but neither contains the other.

Indeed, L cannot normalize N joined with Nᵍ: that nontrivial two-group
would also be normalized by T, contradicting the original unique maximal
two-local overgroup of YT. Pulling back through the literal map
C → C/O₂(C) shows that the image of Nᵍ is nontrivial and is not normalized
by the image of L. Thus the T-exchange does not act on a single invariant
point kernel. This constraint retains information inside and modulo that
kernel; it does not supply an additional cubic or exclude the configuration.

The final application uses the original nonabelian large-distance input,
discharges CommonFacts and Earlier, and retains the original displacement
line and full Sylow. The remaining contradiction in 15.3.23, and its
15.3.13 and Theorem E consumers, is still open.

Source: Aschbacher–Smith 15.3.6–8 and the original setup of 15.3.23,
printed pp.1122–1123 and 1128–1129; MS93 (4.4)–(4.5), pp.890–900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem point_core_ne_bot (z : G) (hz : orderOf z = 2) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≠ ⊥ := by
  let C := centralizer ({z} : Set G)
  let zz : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzz : orderOf zz = 2 := (Subgroup.orderOf_coe zz).symm.trans hz
  have hc : zz ∈ center C := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hle : zpowers zz ≤ center C := zpowers_le.mpr hc
  let : (zpowers zz).Normal :=
    ⟨fun a ha x => by simpa [mem_center_iff.mp (hle ha) x] using ha⟩
  have hp : IsPGroup 2 (zpowers zz) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hzz]; rfl)
  have hmem : z ∈ C.pCoreIn 2 := mem_map_of_mem C.subtype
    ((le_sSup ⟨inferInstance,hp⟩ : zpowers zz ≤ pCore 2 C) (mem_zpowers zz))
  intro he
  have hz1 : z = 1 := he.le hmem
  rw [hz1,orderOf_one] at hz
  omega

private theorem point_core_pair_not_normalized
    (d : LocalData G) (L : Subgroup G) (hout : ¬ L ≤ d.M)
    (hY : d.Y ≤ L ⊔ (d.T : Subgroup G))
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (z : G) (hz : orderOf z = 2) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let N := (centralizer ({z} : Set G)).pCoreIn 2
    N ≤ d.S ∧ d.S ≤ normalizer (N.conjBy g : Set G) ∧
      ¬ L ≤ normalizer ((N ⊔ N.conjBy g : Subgroup G) : Set G) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hCN : C ≤ normalizer (N : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hSN : d.S ≤ normalizer (N : Set G) := le_sup_right.trans (hLS.trans hCN)
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSa : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hSNt : d.S ≤ normalizer (N.conjBy g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSN
    rwa [hSa,map_equiv_normalizer_eq] at hh
  refine ⟨hNS,hSNt,?_⟩
  intro hLN
  exact outside_conjugatePair_contradiction d hout (point_core_ne_bot z hz) hNS
    g hgT hgS hi hSN
    (sup_le hLN ((le_inf hSN hSNt).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)))
    hY hunique

omit [Finite G] in
private theorem point_core_pair_quotient_not_normalized
    (L C N : Subgroup G) (hLC : L ≤ C) (hN : N = C.pCoreIn 2)
    (g : G) (hNtC : N.conjBy g ≤ C)
    (hbad : ¬ L ≤ normalizer ((N ⊔ N.conjBy g : Subgroup G) : Set G)) :
    let q := QuotientGroup.mk' (pCore 2 C)
    let D := ((N.conjBy g).subgroupOf C).map q
    ¬ (L.subgroupOf C).map q ≤ normalizer (D : Set (C ⧸ pCore 2 C)) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let D := ((N.conjBy g).subgroupOf C).map q
  have hpre : (D.comap q).map C.subtype = N ⊔ N.conjBy g := by
    rw [comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,
      map_subgroupOf_eq_of_le hNtC]
    change N.conjBy g ⊔ C.pCoreIn 2 = N ⊔ N.conjBy g
    rw [←hN,sup_comm]
  change ¬ (L.subgroupOf C).map q ≤ normalizer (D : Set _)
  intro hnorm
  have hh : L.subgroupOf C ≤ normalizer (D.comap q : Set C) :=
    (map_le_iff_le_comap.mp hnorm).trans (D.le_normalizer_comap q)
  have hm := (map_mono hh).trans ((D.comap q).le_normalizer_map C.subtype)
  rw [map_subgroupOf_eq_of_le hLC,hpre] at hm
  exact hbad hm

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
include hG hempty hM hu hmany hI htwo hf e

/-- The exchanged actual point two-core survives modulo the first point
 two-core, and the original component does not normalize its image. -/
theorem binary_three_source_point_core_exchange
    (z : G) (hz : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let D := ((N.conjBy g).subgroupOf C).map q
    N ≤ d.S ∧ N.conjBy g ≤ d.S ∧
      N.conjBy g = (centralizer ({g * z * g⁻¹} : Set G)).pCoreIn 2 ∧
      ¬ N.conjBy g ≤ N ∧ ¬ N ≤ N.conjBy g ∧
      IsPGroup 2 D ∧ D ≠ ⊥ ∧
      ¬ (c.L.subgroupOf C).map q ≤ normalizer (D : Set (C ⧸ pCore 2 C)) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let D := ((N.conjBy g).subgroupOf C).map q
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,_,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  have hY := Y_le_component_sylow d c.L hg.generation g hgT (hg.exchange g hgT hgS)
  obtain ⟨hNS,hSNt,hbad⟩ := point_core_pair_not_normalized d c.L c.outside hY hunique
    z hz hLS P hP g hgT hgS
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hNtS : N.conjBy g ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNS
    have he : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
      mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
    rwa [he] at hh
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hNtC : N.conjBy g ≤ C := hNtS.trans (le_sup_right.trans hLS)
  have hCN : C ≤ normalizer (N : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hne : N.conjBy g ≠ N := by
    intro he
    apply hbad
    rw [he,sup_idem]
    exact hLC.trans hCN
  have hcard : Nat.card (N.conjBy g) = Nat.card N :=
    card_map_of_injective (MulAut.conj g).injective
  have hnot : ¬ N.conjBy g ≤ N := fun hh => hne (eq_of_le_of_card_ge hh hcard.ge)
  have hnot' : ¬ N ≤ N.conjBy g := fun hh =>
    hne (eq_of_le_of_card_ge hh hcard.le).symm
  have hD0 : D ≠ ⊥ := by
    intro he
    apply hnot
    intro x hx
    have hx1 : q ⟨x,hNtC hx⟩ = 1 := he.le (mem_map_of_mem q hx)
    exact mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp hx1)
  refine ⟨hNS,hNtS,?_,hnot,hnot',
    ((isPGroup_pCoreIn 2 C).map (MulAut.conj g).toMonoidHom).comap_subtype.map q,hD0,?_⟩
  · change (C.pCoreIn 2).map (MulAut.conj g).toMonoidHom = _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    congr 1
    exact (map_centralizer_equiv ({z} : Set G) (MulAut.conj g)).trans (by
      rw [Set.image_singleton,MulAut.conj_apply])
  · exact point_core_pair_quotient_not_normalized c.L C N hLC rfl g hNtC hbad

/-- The original nonabelian large-distance input supplies the actual
 displacement point and the two distinct point-centralizer kernels. -/
theorem binary_three_large_distance_point_core_exchange
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, orderOf z = 2 ∧
      ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = zpowers z ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      let C := centralizer ({z} : Set G)
      let N := C.pCoreIn 2
      let q := QuotientGroup.mk' (pCore 2 C)
      let D := ((N.conjBy g).subgroupOf C).map q
      N ≤ d.S ∧ N.conjBy g ≤ d.S ∧
        N.conjBy g = (centralizer ({g * z * g⁻¹} : Set G)).pCoreIn 2 ∧
        ¬ N.conjBy g ≤ N ∧ ¬ N ≤ N.conjBy g ∧
        IsPGroup 2 D ∧ D ≠ ⊥ ∧
        ¬ (c.L.subgroupOf C).map q ≤ normalizer (D : Set (C ⧸ pCore 2 C)) ∧
        ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S := by
  obtain ⟨z,hz,hdisp,hLS,hTS,_,_,P,hP⟩ :=
    binary_three_large_distance_displacement_point
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  obtain ⟨hNS,hNtS,hNt,hnot,hnot',hD,hD0,hBD⟩ := binary_three_source_point_core_exchange
    hG d hempty hM hu hmany hI htwo hf c e z hz hLS P hP g hgT hgS
  exact ⟨z,hz,hdisp,hLS,hTS,hNS,hNtS,hNt,hnot,hnot',hD,hD0,hBD,P,hP⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
