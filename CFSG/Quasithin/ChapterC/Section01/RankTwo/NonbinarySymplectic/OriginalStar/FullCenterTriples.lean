module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Distance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalTriples
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalTriples

/-!
# Full source-center triples for the original star

For the selected characteristic star T in the ORIGINAL radical R, let
Q₀ = T ∩ O₂(H), T₀ = T ∩ K and U be the complete intrinsic moving core.
The nonsylow marked radical has abelian image, so [T,T] lies in Q₀.
For every original automorphism a, this also puts [T,T] in a(Q₀).
Consequently [a(X),T₀] lies in U for the ENTIRE X = Ω₁(Z(Q₀)).
Since U centralizes Q₀ and a(X) centralizes a(Q₀), the three-subgroups
identity gives [a(X),Q₀,T₀] = 1. Both complete cores are retained.

The original star's actual graph Z-layer is pulled through embedM and the
overgroup inclusion into R. We prove that mapping it back recovers the
whole layer, and that it lies in this X, using the established equality
between the star's full two-core and its original-core intersection.
Thus the same triples hold for the FULL graph Z, including its fixed
attachment. Applying a inverse and mapping back gives the opposite pair.

The final consumer supplies the actual marked, saturated star and its
intrinsic distance-two geometry, and applies the full-Z identities to an
original automorphism which supplies a critical pair in the minimum graph.
No minimum automorphism is extended and no minimum saturation is assumed.
The internal import of OriginalTriples deliberately reuses that source
family's private component-intersection and derived-core calculations.

This proves the nonsylow full-Z step of MS93 (3.7)(1), printed p.873.
The next inference (3.7)(2), pp.873--874, must still exclude the large
movement of the opposite full core, with D and D′ retained. In particular
these triples do not exclude the extra action on the minimum center.
Minimum marked preservation and saturation, the Sylow branch, n = 2 and
whole-block reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6)--(3.7), printed pp.870--877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar

private theorem full_layer_triples {G : Type*} [Group G]
    (T Q B U V : Subgroup G) [T.Characteristic] [B.Normal]
    (hQT : Q ≤ T) (hBT : B ≤ T) (hBQ : B ⊓ Q ≤ U)
    (hderived : ⁅T,T⁆ ≤ Q) (hUcentral : U ≤ centralizer (Q : Set G))
    (hVT : V ≤ T) (hVcentral : V ≤ centralizer (Q : Set G)) (a : MulAut G) :
    ⁅V.map a.toMonoidHom,B⁆ ≤ U ∧ ⁅⁅V.map a.toMonoidHom,Q⁆,B⁆ = ⊥ := by
  have hV'T : V.map a.toMonoidHom ≤ T := (map_mono hVT).trans_eq
    (characteristic_iff_map_eq.mp inferInstance a)
  have hfirst : ⁅V.map a.toMonoidHom,B⁆ ≤ U :=
    (le_inf (commutator_le_right _ _) ((commutator_mono hV'T hBT).trans hderived)).trans hBQ
  have hderived' : ⁅T,T⁆ ≤ Q.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hderived
    rwa [map_commutator,characteristic_iff_map_eq.mp inferInstance a] at hh
  have hcentral' : V.map a.toMonoidHom ≤ centralizer (Q.map a.toMonoidHom : Set G) :=
    (map_mono hVcentral).trans (map_centralizer_le_centralizer_image _ _)
  have h1 : ⁅⁅Q,B⁆,V.map a.toMonoidHom⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hQT hBT).trans hderived').trans
        (le_centralizer_iff.mp hcentral'))
  have h2 : ⁅⁅B,V.map a.toMonoidHom⁆,Q⁆ = ⊥ := by
    rw [commutator_comm B]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hfirst.trans hUcentral)
  exact ⟨hfirst,commutator_commutator_eq_bot_of_rotate h1 h2⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Both source triples hold on the full central omega subgroup of the
actual original-star core, for every automorphism of the original radical. -/
theorem star_original_full_center_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) (a : MulAut R) :
    let T := starCentralizer R Y
    let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
    let T₀ := T ⊓ K.comap R.subtype
    let U₀ := ((blockU K).map K.subtype).subgroupOf R
    let X := omegaCenter Q₀
    ⁅X.map a.toMonoidHom,T₀⁆ ≤ U₀ ∧
      ⁅⁅X.map a.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ := by
  let := h.component_normal
  let T := starCentralizer R Y
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let T₀ := T ⊓ K.comap R.subtype
  let U₀ := ((blockU K).map K.subtype).subgroupOf R
  have hBQ : T₀ ⊓ Q₀ ≤ U₀ := by
    rintro x ⟨⟨_,hxK⟩,_,hxQ⟩
    exact (original_component_inf_core h).le ⟨hxK,hxQ⟩
  have hderived : ⁅T,T⁆ ≤ Q₀ := by
    apply le_inf
    · exact (Subgroup.commutator_le_sup _ _).trans (sup_idem T).le
    · apply map_le_iff_le_comap.mp
      rw [map_commutator]
      exact star_derived_le_original_core h d P Y hY hnsyl
  have hcentral : U₀ ≤ centralizer (Q₀ : Set R) := by
    intro u hu q hq
    apply R.subtype_injective
    exact ((original_whole_core_centralizer h d g hb).ge hq.2 u hu).symm
  apply full_layer_triples T Q₀ T₀ U₀ (omegaCenter Q₀)
    inf_le_left inf_le_left hBQ hderived hcentral
    ((omegaCenter_le _).trans inf_le_left) _ a
  intro x hx
  exact (mem_omegaCenter_iff.mp hx).2.2

omit d in
/-- The literal graph Z-layer embeds in the original radical without loss
and lies in the central omega subgroup of the actual star two-core. -/
theorem star_graph_center_in_original_core_center
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (gs : Geometry (((starCentralizer R Y).map R.subtype).subgroupOf
      (K ⊔ (starCentralizer R Y).map R.subtype)))
    (hpos : 0 < gs.b (((starCentralizer R Y).map R.subtype).subgroupOf
      (K ⊔ (starCentralizer R Y).map R.subtype))) :
    let T := (starCentralizer R Y).map R.subtype
    let M := K ⊔ T
    let S := T.subgroupOf M
    let Z₀ := (((Z S (alpha S)).comap (embedM S)).map M.subtype).subgroupOf R
    Z₀.map R.subtype = ((Z S (alpha S)).comap (embedM S)).map M.subtype ∧
      Z₀ ≤ omegaCenter (starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype) := by
  let T := (starCentralizer R Y).map R.subtype
  let M := K ⊔ T
  let S := T.subgroupOf M
  let Q₀ := starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype
  let ZM := (Z S (alpha S)).comap (embedM S)
  have hp : IsPGroup 2 S := (h.radical.isPGroup.to_le (map_subtype_le _)).comap_subtype
  obtain ⟨original,hb,_⟩ := h.positive_even_geometry
  have hc : pCore 2 M ≤ S := (star_pair_core_le h original hb P Y hY hn).2.1
  have hZ : ZM ≤ omegaCenter (pCore 2 M) := by
    intro x hx
    have hh := gs.omega_bound (alpha S) rfl (by rwa [gs.distance_constant (alpha S) rfl]) hx
    change embedM S x ∈ omegaCenter (Q S (alpha S)) at hh
    rw [Q_alpha S hp hc,omegaCenter_map _ _ (embedM_injective S)] at hh
    exact (mem_map_iff_mem (embedM_injective S)).mp hh
  have hQ : Q₀.map R.subtype = (pCore 2 M).map M.subtype := by
    rw [star_core_eq_original_intersection h P Y hY hn]
    change (starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype).map R.subtype = _
    rw [map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype]
    rw [←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
  have hZX : ZM.map M.subtype ≤ (omegaCenter Q₀).map R.subtype := by
    rw [←omegaCenter_map _ _ R.subtype_injective,hQ,
      omegaCenter_map _ _ M.subtype_injective]
    exact map_mono hZ
  have hZR : ZM.map M.subtype ≤ R := hZX.trans (map_subtype_le _)
  refine ⟨map_subgroupOf_eq_of_le hZR,?_⟩
  intro x hx
  exact (mem_map_iff_mem R.subtype_injective).mp (hZX hx)

/-- MS93 (3.7)(1) for the full original-star Z-layer and its image under
the same original automorphism, in both directions. -/
theorem star_original_graph_center_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (gs : Geometry (((starCentralizer R Y).map R.subtype).subgroupOf
      (K ⊔ (starCentralizer R Y).map R.subtype)))
    (hpos : 0 < gs.b (((starCentralizer R Y).map R.subtype).subgroupOf
      (K ⊔ (starCentralizer R Y).map R.subtype))) (a : MulAut R) :
    let T := starCentralizer R Y
    let M := K ⊔ T.map R.subtype
    let S := (T.map R.subtype).subgroupOf M
    let Z₀ := (((Z S (alpha S)).comap (embedM S)).map M.subtype).subgroupOf R
    let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
    let T₀ := T ⊓ K.comap R.subtype
    let U₀ := ((blockU K).map K.subtype).subgroupOf R
    ⁅Z₀.map a.toMonoidHom,T₀⁆ ≤ U₀ ∧
      ⁅Z₀,T₀.map a.toMonoidHom⁆ ≤ U₀.map a.toMonoidHom ∧
      ⁅⁅Z₀.map a.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ ∧
      ⁅⁅Z₀,Q₀.map a.toMonoidHom⁆,T₀.map a.toMonoidHom⁆ = ⊥ := by
  let T := starCentralizer R Y
  let M := K ⊔ T.map R.subtype
  let S := (T.map R.subtype).subgroupOf M
  let Z₀ := (((Z S (alpha S)).comap (embedM S)).map M.subtype).subgroupOf R
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let T₀ := T ⊓ K.comap R.subtype
  let U₀ := ((blockU K).map K.subtype).subgroupOf R
  have hZX : Z₀ ≤ omegaCenter Q₀ :=
    (star_graph_center_in_original_core_center h P Y hY hn gs hpos).2
  have hf (b : MulAut R) : ⁅Z₀.map b.toMonoidHom,T₀⁆ ≤ U₀ ∧
      ⁅⁅Z₀.map b.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ := by
    obtain ⟨hmove,htriple⟩ := star_original_full_center_triples h d g hb P Y hY hnsyl b
    exact ⟨(commutator_mono (map_mono hZX) le_rfl).trans hmove,
      bot_unique ((commutator_mono (commutator_mono (map_mono hZX) le_rfl) le_rfl).trans_eq htriple)⟩
  have hcomp : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id R :=
    MonoidHom.ext a.apply_symm_apply
  have hbmove := map_mono (f := a.toMonoidHom) (hf a.symm).1
  rw [map_commutator,map_map,hcomp,Subgroup.map_id] at hbmove
  have hbtriple := congrArg (fun J : Subgroup R => J.map a.toMonoidHom) (hf a.symm).2
  rw [map_commutator,map_commutator,map_map,hcomp,Subgroup.map_id,Subgroup.map_bot] at hbtriple
  exact ⟨(hf a).1,hbmove,(hf a).2,hbtriple⟩

/-- The actual marked, saturated source star satisfies the full-Z triples
at an original automorphism supplying the minimum graph critical pair.
The full star core and source layer are identified through their literal maps. -/
theorem exists_source_star_original_full_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R, ∃ a : MulAut R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let z := act d.radical (minimumAutomorphismElement d a)⁻¹ (alpha d.radical)
       Adjacent d.radical z (beta d.radical) ∧
       ¬ U d.radical z ≤ Q d.radical (alpha d.radical) ∧
       Nonempty (CriticalPath d.radical g (alpha d.radical) z)) ∧
      (let T := starCentralizer R Y
       let M := K ⊔ T.map R.subtype
       let S := (T.map R.subtype).subgroupOf M
       let Z₀ := (((Z S (alpha S)).comap (embedM S)).map M.subtype).subgroupOf R
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let T₀ := T ⊓ K.comap R.subtype
       let U₀ := ((blockU K).map K.subtype).subgroupOf R
       ∃ hs : Input (K.subgroupOf M) S n F,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         (pCore 2 M).map M.subtype = Q₀.map R.subtype ∧
         (∃ gs : Geometry S, gs.b S = 2) ∧
         Z₀.map R.subtype = ((Z S (alpha S)).comap (embedM S)).map M.subtype ∧
         ⁅Z₀.map a.toMonoidHom,T₀⁆ ≤ U₀ ∧
         ⁅Z₀,T₀.map a.toMonoidHom⁆ ≤ U₀.map a.toMonoidHom ∧
         ⁅⁅Z₀.map a.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ ∧
         ⁅⁅Z₀,Q₀.map a.toMonoidHom⁆,T₀.map a.toMonoidHom⁆ = ⊥) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  obtain ⟨a,hcrit⟩ := exists_original_critical_neighbor h d g hb
  have hpos : 0 < gs.b _ := by rw [hgs]; decide
  have hZ := star_graph_center_in_original_core_center h P Y hY hn gs hpos
  have htrip := star_original_graph_center_triples h d g hb P Y hY hn hnsyl gs hpos a
  refine ⟨P,Y,a,hY,hn,hmin,hmark,hcrit,hs,hquot,hsat,?_,⟨gs,hgs⟩,hZ.1,htrip⟩
  rw [star_core_eq_original_intersection h P Y hY hn,
    map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype,
    ←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
