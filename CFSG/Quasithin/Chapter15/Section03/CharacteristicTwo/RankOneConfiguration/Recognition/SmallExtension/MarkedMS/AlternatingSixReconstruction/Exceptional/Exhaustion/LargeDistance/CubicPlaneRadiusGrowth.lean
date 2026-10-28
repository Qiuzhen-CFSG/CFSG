module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusImage
public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneJointSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration

/-!
# Opposite-edge growth of the full cubic radius line

The full seed fixers of two generating plane edges intersect in exactly
the endpoint seed's intersection with the endpoint center. Consequently,
an order-two line in one edge seed, disjoint from that center, cannot be
fixed by a subactor of the other edge with image larger than two.

The whole opposite edge has image eight over the endpoint two-core. The
centralizer tower therefore has index at least four. An orbit-stabilizer
count for the nonidentity element of the line puts at least four elements
in its commutator with that edge. Quadraticity puts this displacement in
the opposite edge seed. It is disjoint from the original line, so adjoining
it produces an elementary subgroup of order at least eight.

At distance four with uniformly small critical images, reverse the same
escaping critical path to select an opposite edge. The exact four-element
images already proved for the midpoint radius kernel and the whole last-edge
radius kernel make each generate the endpoint stabilizer with this edge.
The growth theorem then applies to the very same full-kernel commutator
line, which still centralizes both original radii. In particular the
opposite edge cannot normalize that line. No identification of different
graphs, deletion of a central attachment, or substitution of Q for the
cubic projection kernel E is used.

The whole-core and literal C.1.32 applications retain both full moving
covers and the Borel branch. These conclusions isolate the missing
normalizer comparison; they do not exclude the configuration or prove
MS93 (5.12). Its terminal argument, the remaining image and distance cases,
and both whole-core reconstruction outcomes remain to be assembled.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the common-fixer and generation comparisons in (5.6), (5.12)(1),
printed pp.917--918,924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


private theorem line_centralizer_index_le_commutator {F : Type*} [Group F] [Finite F]
    (H A : Subgroup F) (hcard : Nat.card H = 2) :
    (centralizer (H : Set F)).relIndex A ≤ Nat.card (⁅H,A⁆ : Subgroup F) := by
  obtain ⟨x,hx,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have he : H = zpowers (x : F) := by
    apply le_antisymm
    · intro y hy
      by_cases hy1 : y = 1
      · exact hy1 ▸ one_mem _
      · have hyx : (⟨y,hy⟩ : H) = x := hunique _ (fun he => hy1 (congrArg Subtype.val he))
        rw [show y = (x : F) from congrArg Subtype.val hyx]
        exact mem_zpowers _
    · exact zpowers_le.mpr x.property
  have hC : centralizer (H : Set F) = centralizer ({(x : F)} : Set F) := by
    exact (congrArg (fun K : Subgroup F => centralizer (K : Set F)) he).trans
      (by rw [zpowers_eq_closure,centralizer_closure])
  have hb := card_le_commutator_card_mul_centralizer A (x : F)
  rw [←he,commutator_comm A] at hb
  have hm := ((centralizer (H : Set F)).subgroupOf A).index_mul_card
  change (centralizer (H : Set F)).relIndex A *
    Nat.card ((centralizer (H : Set F)).subgroupOf A) = Nat.card A at hm
  rw [←hC,←hm] at hb
  exact Nat.le_of_mul_le_mul_right hb Nat.card_pos

include h e hz hk in
private theorem plane_edge_core_index_eight
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    (Q Rg a).relIndex (Q Rg t) = 8 := by
  obtain ⟨i,hi,_,hiR,hiQ,_⟩ := remaining_edge_coordinates h e hz ha hat
  rw [←hiR,←hiQ,relIndex_map_map_of_injective _ _ hi,
    ←CubicAction.permutation_image_card_of_two h e hz hk Rg h.relative_radical.isPGroup,
    hR,card_map_of_injective (MulAut.conj u).injective,D_card]

include h e hz hk in
/-- The full omega-centers on a generating pair of plane edges intersect
in precisely the full endpoint seed's fixed subgroup. -/
theorem plane_generating_edge_seed_intersection
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t s : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (has : Adjacent Rg a s)
    (hgen : Q Rg t ⊔ Q Rg s = stabilizer Rg a) :
    Z Rg t ⊓ Z Rg s =
      Z Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  have ht := (plane_edge_full_seed_fixer h e hz hk u hR ha hat).1
  have hs := (plane_edge_full_seed_fixer h e hz hk u hR ha has).1
  have htg : Q Rg t ≤ stabilizer Rg a := hgen ▸ le_sup_left
  have hsg : Q Rg s ≤ stabilizer Rg a := hgen ▸ le_sup_right
  apply le_antisymm
  · refine le_inf (inf_le_left.trans (adjacent_Z_le Rg ha hat)) ?_
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans (ht ▸ inf_le_right)))
      (le_centralizer_iff.mp (inf_le_right.trans (hs ▸ inf_le_right)))
  · rw [←ht,←hs]
    exact le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le htg)))
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le hsg)))

include h e hz hk in
/-- A noncentral line in one edge seed has at least four commutators under
the opposite generating edge. Its displacement is in the opposite edge seed
and disjoint from the original line. -/
theorem plane_generating_edge_line_growth
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t s : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (has : Adjacent Rg a s)
    (hgen : Q Rg t ⊔ Q Rg s = stabilizer Rg a)
    (H : Subgroup (FreeAmalgam Rg)) (hHt : H ≤ Z Rg t)
    (hcard : Nat.card H = 2)
    (hnon : H ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥) :
    (Q Rg a).relIndex (Q Rg s ⊓ centralizer (H : Set (FreeAmalgam Rg))) ≤ 2 ∧
      4 ≤ (centralizer (H : Set (FreeAmalgam Rg))).relIndex (Q Rg s) ∧
      4 ≤ Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
      ⁅H,Q Rg s⁆ ≤ Z Rg s ∧
      H ⊓ Z Rg s = ⊥ ∧ H ⊓ ⁅H,Q Rg s⁆ = ⊥ ∧
      ¬ Q Rg s ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
  let C := Q Rg s ⊓ centralizer (H : Set (FreeAmalgam Rg))
  have hHZ : H ≤ Z Rg a := hHt.trans (adjacent_Z_le Rg ha hat)
  have htfix : H ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) :=
    hHt.trans ((plane_edge_full_seed_fixer h e hz hk u hR ha hat).1 ▸ inf_le_right)
  have hnot : ¬ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    intro hh
    have hzH : H = ⊥ := by simpa only [inf_eq_left.mpr hh] using hnon
    rw [hzH,Subgroup.card_bot] at hcard
    omega
  have hCsmall : (Q Rg a).relIndex C ≤ 2 := by
    by_contra! hn
    have hg := plane_edge_pair_large_subactor_generates h e hz hk u hR ha hat has
      hgen C inf_le_left hn
    apply hnot
    apply le_centralizer_iff.mpr
    rw [←hg]
    exact sup_le (le_centralizer_iff.mp htfix) inf_le_right
  have hscolor : color Rg s = true := by
    have hh := adjacent_color_ne Rg has
    rw [ha] at hh
    cases he : color Rg s <;> simp_all
  have hQa : Q Rg a ≤ C := le_inf (Q_le_adjacent_h Rg hscolor has)
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a ha))).trans (centralizer_le hHZ))
  have hmul := relIndex_mul_relIndex (Q Rg a) C (Q Rg s) hQa inf_le_left
  rw [plane_edge_core_index_eight h e hz hk u hR ha has,inf_relIndex_left] at hmul
  have hidx : 4 ≤ (centralizer (H : Set (FreeAmalgam Rg))).relIndex (Q Rg s) := by
    change (Q Rg a).relIndex C * _ = 8 at hmul
    nlinarith
  have hmove : ⁅H,Q Rg s⁆ ≤ Z Rg s := (commutator_mono hHZ le_rfl).trans
    (plane_edge_seed_commutator h e hz hk u hR ha has)
  have hbound : (centralizer (H : Set (FreeAmalgam Rg))).relIndex (Q Rg s) ≤
      Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) := by
    obtain ⟨i,hi,hir,hiR,_,_⟩ := remaining_edge_coordinates h e hz ha has
    have hmH : (H.comap i).map i = H :=
      map_comap_eq_self ((hHZ.trans (Z_le_stabilizer Rg a)).trans_eq hir.symm)
    have hh := line_centralizer_index_le_commutator (H.comap i) Rg (by
      rw [←card_map_of_injective hi,hmH]
      exact hcard)
    have hiC : (centralizer (H : Set (FreeAmalgam Rg))).relIndex (Q Rg s) =
        (centralizer (H.comap i : Set M)).relIndex Rg := by
      calc
        _ = (centralizer ((H.comap i).map i : Set (FreeAmalgam Rg))).relIndex ((Rg).map i) := by
          rw [hmH,hiR]
        _ = _ := by
          rw [←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
            relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]
    have hc : Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) =
        Nat.card (⁅H.comap i,Rg⁆ : Subgroup M) := by
      calc
        _ = Nat.card ((⁅H.comap i,Rg⁆ : Subgroup M).map i) := by
          rw [map_commutator,hmH,hiR]
        _ = _ := card_map_of_injective hi
    rwa [hiC,hc]
  have hdis : H ⊓ Z Rg s = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ hnon.le
    refine le_inf inf_le_left ?_
    have hh : H ⊓ Z Rg s ≤ Z Rg t ⊓ Z Rg s := inf_le_inf_right _ hHt
    rw [plane_generating_edge_seed_intersection h e hz hk u hR ha hat has hgen] at hh
    exact hh.trans inf_le_right
  refine ⟨hCsmall,hidx,hidx.trans hbound,hmove,hdis,
    le_bot_iff.mp ((inf_le_inf_left H hmove).trans hdis.le),?_⟩
  intro hn
  apply hnot
  apply le_centralizer_iff.mpr
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp htfix)
    (hn.trans (normalizer_le_centralizer_of_card_two H hcard))

include h e hz hk in
/-- At distance four with uniformly small critical images, the same escaping
radius kernel generates the endpoint stabilizer with an actual opposite edge.
That edge displaces the retained line by at least a four-group; adjoining
this displacement gives an elementary subgroup of order at least eight. -/
theorem plane_small_four_radius_growth
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
      let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
      ∃ s, Adjacent Rg z s ∧
        Q Rg s ⊔ Q Rg (p.walk.getVert 3) = stabilizer Rg z ∧
        Q Rg s ⊔ Y = stabilizer Rg z ∧
        Q Rg s ⊔ W = stabilizer Rg z ∧
        (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
        Z Rg (p.walk.getVert 3) ⊓ Z Rg s =
          Z Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
        Nat.card H = 2 ∧
        H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
        H ≤ Z Rg (p.walk.getVert 3) ∧
        H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
          Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
        H ⊓ Z Rg s = ⊥ ∧
        4 ≤ (centralizer (H : Set (FreeAmalgam Rg))).relIndex (Q Rg s) ∧
        4 ≤ Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
        ⁅H,Q Rg s⁆ ≤ Z Rg s ∧
        H ⊓ ⁅H,Q Rg s⁆ = ⊥ ∧
        8 ≤ Nat.card (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
        IsElementaryAbelian 2 (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
        ¬ Q Rg s ≤ normalizer (H : Set (FreeAmalgam Rg)) ∧
        ¬ ⁅Y,X Rg z⁆ ≤ Z Rg a := by
  obtain ⟨a,z,p,hiY,hiW,hfixY,hfixW,hfixU,hcard,hwhole,hHZ,hHC,hlt,hTZ,hquad,
    hescape,hdis,halign⟩ := plane_small_four_radius_indices h e hz hk u hR hb4 hsmall
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
  let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : Y ≤ Q Rg (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      reverse_pair h e p⟩
  have hpr1 : pr.walk.getVert 1 = p.walk.getVert 3 := by
    change p.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  obtain ⟨s,hzs,hgen⟩ := plane_small_critical_first_edge_partner h e hz hk u hR
    pr (hsmall _ _ pr)
  rw [hpr1] at hgen
  have hgenY := plane_edge_pair_large_subactor_generates h e hz hk u hR
    p.end_color hzs hzt hgen Y hYt (by rw [hiY]; decide)
  have hgenW := plane_edge_pair_large_subactor_generates h e hz hk u hR
    p.end_color hzs hzt hgen W inf_le_right (by rw [hiW]; decide)
  have hHlast : H ≤ Z Rg (p.walk.getVert 3) := hlt.le.trans (hTZ.trans inf_le_left)
  have hpair : Q Rg (p.walk.getVert 3) ⊔ Q Rg s = stabilizer Rg z :=
    (sup_comm _ _).trans hgen
  obtain ⟨hCsmall,hCindex,hDcard,hDle,hHs,hHD,hN⟩ :=
    plane_generating_edge_line_growth h e hz hk u hR p.end_color hzt hzs hpair H
      hHlast hcard hdis
  have hspanZ : H ⊔ ⁅H,Q Rg s⁆ ≤ Z Rg z :=
    sup_le (hHlast.trans (adjacent_Z_le Rg p.end_color hzt))
      (hDle.trans (adjacent_Z_le Rg p.end_color hzs))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have helem : IsElementaryAbelian 2 (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) :=
    IsElementaryAbelian.of_le hspanZ
  have hn : ⁅H,Q Rg s⁆ ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (((le_sup_right.trans hspanZ).trans (le_centralizer (Z Rg z))).trans
      (centralizer_le (show H ≤ Z Rg z from le_sup_left.trans hspanZ))).trans (Subgroup.centralizer_le_normalizer _)
  have hspan : 8 ≤ Nat.card (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint H ⁅H,Q Rg s⁆ hn
      (disjoint_iff.mpr hHD),hcard]
    omega
  exact ⟨a,z,p,s,hzs,hgen,hgenY,hgenW,hiY,hiW,
    plane_generating_edge_seed_intersection h e hz hk u hR p.end_color hzt hzs hpair,
    hcard,hHZ,hHlast,hHC,hHs,hCindex,hDcard,hDle,hHD,hspan,helem,hN,hescape⟩

omit hk in
include h e hz in
/-- Whole-core application of the opposite-edge growth on the original cubic
plane graph. The Borel case, both full covers and the cubic kernel E remain. -/
theorem coreExhaustion_or_cubic_plane_radius_growth :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              Nat.card H = 2 ∧
              H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
              H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
                Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              4 ≤ Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
              ⁅H,Q Rg s⁆ ≤ Z Rg s ∧ H ⊓ Z Rg s = ⊥ ∧
              8 ≤ Nat.card (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
              ¬ Q Rg s ≤ normalizer (H : Set (FreeAmalgam Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall
    obtain ⟨a,z,p,s,hadj,_,hgen,_,_,_,_,hcard,hHZ,_,hHC,hdis,_,hD,hDZ,_,hspan,_,hN,_⟩ :=
      plane_small_four_radius_growth h e hz hk u hplane hb4 hsmall
    exact ⟨a,z,p,s,hadj,hgen,hcard,hHZ,hHC,hD,hDZ,hdis,hspan,hN⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the same-line opposite-edge growth.
The distance-four/small-image specialization does not discharge the terminal
contradiction or any other reconstruction branch. -/
theorem rankTwo_or_cubic_plane_radius_growth :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              Nat.card H = 2 ∧
              H ≤ Z Rg a ⊓ Z Rg (p.walk.getVert 2) ∧
              H ≤ centralizer ((V Rg a ⊔ V Rg (p.walk.getVert 2) :
                Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
              4 ≤ Nat.card (⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
              ⁅H,Q Rg s⁆ ≤ Z Rg s ∧ H ⊓ Z Rg s = ⊥ ∧
              8 ≤ Nat.card (H ⊔ ⁅H,Q Rg s⁆ : Subgroup (FreeAmalgam Rg)) ∧
              ¬ Q Rg s ≤ normalizer (H : Set (FreeAmalgam Rg)))) :=
  (coreExhaustion_or_cubic_plane_radius_growth h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
