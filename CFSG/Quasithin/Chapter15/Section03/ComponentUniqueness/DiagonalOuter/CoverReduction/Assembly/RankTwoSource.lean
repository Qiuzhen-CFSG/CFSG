module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.GraphComponent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeEnvelope
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly
public import CFSG.Quasithin.ChapterI.Section03.OrdinaryBalance

/-!
# The actual Chapter 15 balance applications without a B₂ catalogue

The representative centralizer uses the proved rank-two source deduction
from the full A.3.6/A.3.8 and GLS 5.22 inputs. The graph centralizer needs
only S₂ and the two-layer bound: the already-proved odd-core bound by nine
makes every ambient two-component ordinary. All marked covers, subgroups,
involutions and source model assumptions are retained.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, and I.3.1.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G]

/-- With odd core of order dividing nine, a nontrivial local two-component
and the genuine two-layer inclusion produce an ambient ordinary component. -/
theorem exists_component_of_local_twoComponent_of_small_oddCore [Finite G]
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u})
    (P D B : Subgroup G) (hP : IsPGroup 2 P)
    (hCD : centralizer (P : Set G) ≤ D)
    (hB : IsTwoComponent (B.subgroupOf (D ⊓ centralizer (P : Set G))))
    (hodd : Nat.card (pPrimeCore 2 G) ∣ 9) :
    ∃ K : Subgroup G, IsComponent G K := by
  classical
  have he : D ⊓ centralizer (P : Set G) = centralizer (P : Set G) :=
    inf_eq_right.mpr hCD
  rw [he] at hB
  let C := centralizer (P : Set G)
  let J := B.subgroupOf C
  have hJ : Subgroup.IsTwoComponent J := hB
  have hb := source517 G
    (ChapterI.OrdinaryBalance.hasTwoSchreier_of_simpleSylowFixer sourceS2 G) P hP
  have hm : J.map C.subtype ≤ twoComponentLayer G :=
    (map_mono (f := C.subtype) hJ.le_twoComponentLayer).trans hb
  by_contra hn
  have hz : twoComponentLayer G ≤ ⊥ := by
    apply sSup_le
    intro K hK
    let : Group.IsPerfect K := hK.1.perfect
    have hc := perfect_centralizes_normal_of_card_dvd_nine K (pPrimeCore 2 G) hodd
    exact (hn ⟨K, hK.isComponent_of_centralizes_oddCore hc⟩).elim
  have hmap : J.map C.subtype = ⊥ := le_bot_iff.mp (hm.trans hz)
  have hker : C.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective
  have hle : J ≤ C.subtype.ker := (Subgroup.map_eq_bot_iff _).mp hmap
  exact hJ.1.ne_bot (le_bot_iff.mp (hker ▸ hle))

private theorem psl_four_properties {B : Type*} [Group B] [Finite B]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : B ≃* PSL(2,F)) : IsQuasisimple B ∧ pPrimeCore 2 B = ⊥ := by
  obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := (MulEquiv.isSimpleGroup_congr (e.trans ea)).mpr inferInstance
  let : Group.IsPerfect PSL(2,F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)).elim
  have hquasi : IsQuasisimple B := {
    simple := (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := B)))).mpr
        inferInstance }
  refine ⟨hquasi, ?_⟩
  rcases (inferInstance : (pPrimeCore 2 B).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hcard : Nat.card B = 60 := by
      rw [Nat.card_congr (e.trans ea).toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hp := pPrimeCore_coprime_card (p := 2) (G := B)
    rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv, hcard] at hp
    norm_num at hp

private theorem local_twoComponent_of_normal_psl_four [Finite G]
    (B D : Subgroup G) (hBD : B ≤ D) (hDB : D ≤ normalizer (B : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : B ≃* PSL(2,F)) : IsTwoComponent (B.subgroupOf D) := by
  let J := B.subgroupOf D
  let ej : J ≃* B := subgroupOfEquivOfLe hBD
  obtain ⟨hq, ho⟩ := psl_four_properties hF (ej.trans e)
  let : J.Normal := normal_subgroupOf_of_le_normalizer hDB
  have hj : IsComponent D J := ⟨(inferInstance : J.Normal).isSubnormal, hq⟩
  refine ⟨component_isCComponent hj, ?_⟩
  let : IsQuasisimple J := hq
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq ho).trans (QuotientGroup.quotientBot (G := J))).symm

theorem exists_graph_component_of_two_layer_source [Finite G] {κ : GroupClass.{u}}
    (_hG : IsSimpleQTKE κ G)
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u})
    (T : Sylow 2 G) (Y S L V I J : Subgroup G) [IsKleinFour V]
    (c : ProjectiveMarking L 4) (d : SylowThreeLift T Y S L c)
    (hI : I = normalizer (V : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (v : G) (hv : v ∈ V) (hv1 : v ≠ 1) (hv2 : orderOf v = 2)
    (hSCv : S ≤ centralizer ({v} : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I) (hJI : J ≤ I)
    (htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : J, (MulAut.conj (m : G)) x = y)
    (hfixed : (d.dihedral.firstReflection : G) * (d.dihedral.halfTurn : G) ∈
      centralizer (V : Set G))
    (emodel : pPrimeCore 2 ↥(I ⊓ centralizer
      ({(d.dihedral.firstReflection : G) * (d.dihedral.halfTurn : G)} : Set G)) ≃*
        Multiplicative (Fin 2 → ZMod 3))
    (graphModel : graphResidualIn L (d.dihedral.firstReflection : G) ≃* PSL(2,c.F)) :
    ∃ K : Subgroup (centralizer ({(d.dihedral.firstReflection : G)} : Set G)),
      IsComponent (centralizer ({(d.dihedral.firstReflection : G)} : Set G)) K := by
  let τ : G := d.dihedral.firstReflection
  let H := centralizer ({τ} : Set G)
  let D := I.subgroupOf H
  let A := L.subgroupOf H
  let B := graphResidualIn L τ
  have hvH : v ∈ H := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hSCv d.first_mem)).symm
  let vH : H := ⟨v, hvH⟩
  let P := zpowers vH
  have hP : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hv2, pow_one])
  have hCD : centralizer (P : Set H) ≤ D := by
    intro x hx
    apply hCv
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (hx vH (mem_zpowers vH))).symm
  have hDA : D ≤ normalizer (A : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hIL hx) y
  have hDB : D ≤ normalizer (B : Set H) :=
    hDA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hBA : B ≤ A := map_subtype_le _
  have hBD : B ≤ D := hBA.trans (comap_mono hLI)
  have hBC : B ≤ centralizer (P : Set H) := by
    change B ≤ centralizer (zpowers vH : Set H)
    rw [zpowers_eq_closure, centralizer_closure]
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    obtain ⟨w, hw, hwv⟩ := mem_map.mp (hZ.symm ▸ hv)
    have he := congrArg Subtype.val (mem_center_iff.mp hw ⟨x, hBA hx⟩)
    change (w : G) = v at hwv
    change (x : G) * (w : G) = (w : G) * (x : G) at he
    change (x : G) * v = v * (x : G)
    rwa [hwv] at he
  have hlocal : IsTwoComponent (B.subgroupOf (D ⊓ centralizer (P : Set H))) :=
    local_twoComponent_of_normal_psl_four B _ (le_inf hBD hBC)
      (inf_le_left.trans hDB) c.card graphModel
  have hodd := (graph_oddCore_card_dvd_nine T Y S L V I J c d hI v hv hv1 hCv
    hJI htrans hfixed emodel).2
  exact exists_component_of_local_twoComponent_of_small_oddCore sourceS2 source517
    P D B hP hCD hlocal hodd

/-- Fill the existing, unrestricted rank-two balance input from its genuine
earlier source implications. No local or projected quasisimplicity is assumed. -/
theorem earlierRankTwoBalance_of_source {κ : GroupClass.{u}}
    (hA36 : ChapterI.RankTwoSource.EarlierA36 κ)
    (hA38 : ChapterI.RankTwoSource.EarlierA38 κ)
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection κ) : EarlierRankTwoBalance κ := by
  intro H _ _ hH P hP L hL hr
  exact (ChapterI.RankTwoSource.lemma_I_3_1_three hA36 hA38 hGLS hH P hP L hL hr).2

/-- The literal marked-cover representative-centralizer application. -/
theorem representative_component_envelope_of_rank_two_source [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierEmbeddings κ)
    (hA36 : ChapterI.RankTwoSource.EarlierA36 κ)
    (hA38 : ChapterI.RankTwoSource.EarlierA38 κ)
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection κ)
    (hG : IsSimpleQTKE κ G)
    (I L V S : Subgroup G) [IsKleinFour V] [IsQuasisimple L]
    (hI : I = normalizer (V : Set G))
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (hoL : pPrimeCore 2 L = ⊥) (hrank : primeRank 3 L = 2)
    (hlocal : L ∈ Chapter1.L G S)
    (v : G) (hv : v ∈ V) (hv2 : orderOf v = 2)
    (P : Sylow 2 (centralizer ({v} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({v} : Set G)).subtype = S) :
    let H := centralizer ({v} : Set G)
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype ∧
      A312Embedding ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
        (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  exact representative_component_envelope earlier
    (earlierRankTwoBalance_of_source hA36 hA38 hGLS) hG
    I L V S hI hIL hZ hoL hrank hlocal v hv hv2 P hP

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open Subgroup Theory.GroupTheory
open Chapter1 LocalCover LocalCover.SourceBorel GlobalGeometry
open scoped MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The existing geometric assembly with the adequate source balance route. -/
theorem geometry_of_lift_of_rank_two_source {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embeddings : EarlierEmbeddings κ)
    (hA36 : ChapterI.RankTwoSource.EarlierA36 κ)
    (hA38 : ChapterI.RankTwoSource.EarlierA38 κ)
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection κ)
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u}) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowThreeLift d.T d.Y d.S L r.marking)
    (hZS : Nat.card d.ZS = 4)
    (hfixedSylow : ∀ i : OrthogonalPlaneIndex, IsSylowIn 2 d.S
      (centralizer (fixedPlane (d.action.plane i) d.S : Set G)))
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (hfixed : (b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G) ∈
      centralizer (r.cover.borel.W₁ : Set G))
    (emodel : pPrimeCore 2 ↥(I ⊓ centralizer
      ({(b.dihedral.firstReflection : G) * (b.dihedral.halfTurn : G)} : Set G)) ≃*
        Multiplicative (Fin 2 → ZMod 3))
    (graphModel : graphResidualIn L (b.dihedral.firstReflection : G) ≃* PSL(2,r.marking.F)) :
    I = normalizer (r.cover.borel.W₁ : Set G) ∧
      Nonempty (RepresentativeGeometry r.cover.borel.W₁ d.ZS d.S I) ∧
      ∃ K : Subgroup (centralizer ({(b.dihedral.firstReflection : G)} : Set G)),
        IsComponent (centralizer ({(b.dihedral.firstReflection : G)} : Set G)) K := by
  obtain ⟨i, hi⟩ := r.plane
  let V := r.cover.borel.W₁
  have hV : V = d.action.plane i := hi
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (hV ▸ d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hV, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨hV ▸ d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  have hI : I = normalizer (V : Set G) := normalizer_eq hG embeddings s h r
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  have hIL := h.normalizes_component s.earlier
  have hZ : (center L).map L.subtype = V := r.cover.center_plane
  obtain ⟨v, hv1, hv2, hline, hSv⟩ := exists_fixed_line_generator V d.ZS d.S
    inf_le_right (by rw [hV]; exact source_fixed_line_card d hZS i)
  have hv : v ∈ V := (hline ▸ mem_zpowers v).2
  have hSylow := representative_sylow_of_fixed_line d.V V d.ZS d.S
    (hV ▸ d.action.plane_le i) rfl v hline (hV ▸ hfixedSylow i)
  have henv := representative_envelope_of_outside embeddings
    (earlierRankTwoBalance_of_source hA36 hA38 hGLS) hG h.outside
    s.earlier.sylow h.component_le h.component (s.earlier.odd I h.outside)
    hI hIL hZ h.component_rank v hv hv2 hSylow
  have hCv : centralizer ({v} : Set G) ≤ I :=
    representative_centralizer_le_of_envelope hG I L V r.marking hI hZ
      r.cover.center_core h.component_rank v hv2 hm henv
  have hJI : planeActor d.action ≤ I := hI.symm ▸ (hV ▸ planeActor_normalizes d.action i)
  have htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : planeActor d.action, (MulAut.conj (m : G)) x = y :=
    hV ▸ planeActor_transitive d.action i
  refine ⟨hI, ⟨{
    v := v, ne_one := hv1, order := hv2, generator := hline
    sylow_centralizes := hSv, centralizer_le := hCv
    actor := planeActor d.action, actor_le := hJI, transitive := htrans }⟩, ?_⟩
  exact exists_graph_component_of_two_layer_source hG sourceS2 source517 d.T d.Y d.S L V I (planeActor d.action)
    r.marking b hI h.component_le hIL hZ v hv hv1 hv2 hSv hCv hJI htrans
    hfixed emodel graphModel

/-- Return the original reduction record, consumed unchanged by
`Reduction.field_fusion`, with no full B₂ balance premise. -/
theorem cover_reduction_of_rank_two_source {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embeddings : EarlierEmbeddings κ)
    (hA36 : ChapterI.RankTwoSource.EarlierA36 κ)
    (hA38 : ChapterI.RankTwoSource.EarlierA38 κ)
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection κ)
    (sourceS2 : ChapterI.OrdinaryBalance.SimpleSylowFixerSolvability.{u})
    (source517 : ChapterI.OrdinaryBalance.TwoLayerCentralizerBalance.{u}) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (hZS : Nat.card d.ZS = 4)
    (hfixedSylow : ∀ i : OrthogonalPlaneIndex, IsSylowIn 2 d.S
      (centralizer (fixedPlane (d.action.plane i) d.S : Set G)))
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (sylowModels : ∀ r : LocalResult d I L, SylowCalculations d I L r)
    (fixedModels : ∀ (r : LocalResult d I L) (b : SylowResult d I L r),
      Nonempty (FixedCalculations d I L r b)) : Nonempty (Reduction d I L) := by
  obtain ⟨r⟩ := local_result s h
  obtain ⟨b⟩ := sylow_result s h r (sylowModels r)
  obtain ⟨m⟩ := fixedModels r b
  obtain ⟨hI, ⟨v⟩, K, hK⟩ := geometry_of_lift_of_rank_two_source hG embeddings hA36 hA38 hGLS sourceS2 source517 s h r b.lift
    hZS hfixedSylow hm b.fixes m.odd_core m.graph_residual
  obtain ⟨ha, hk⟩ := normalizer_action_and_kernel r.cover.borel.W₁ I L hI
    (h.normalizes_component s.earlier) r.cover.overgroup_centralizer
  exact ⟨⟨r, b, hI, v, K, hK, h.normalizes_component s.earlier, ha, hk⟩⟩


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
