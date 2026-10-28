module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.EdgeRadius

/-!
# Distance two on the original saturated star

The whole-core theorem for the supplied minimum replacement makes the
original component short. The intrinsic-core comparison then gives
[Q_alpha,Ltilde_alpha] = U_alpha in the ORIGINAL graph. If its critical
distance exceeded two, the span of Z over the neighbors of beta would lie
in Q_alpha. This span contains U_alpha, so Ltilde_alpha normalizes it.
The original radical and the whole holomorph at beta also normalize it.
Consequently it is normal at both ends of the base edge, contradicting MS3
and the nontriviality of Z_alpha. Positivity and evenness give distance two.

Shortness transports through the actual component equivalence to the
selected original star. Applying the same argument there supplies its own
distance-two geometry, together with the existing full intrinsic input,
saturation, original quotient marking and Sylow alternative. All fixed
attachments are retained. This proves the distance statement using the
whole core; it does not assume an inclusion or comparison of amalgam graphs.
It does not identify the minimum radical's marked image with the original
one or prove saturation of that minimum radical.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the common-normal exclusion (2.1)(iii), p.855, the full-core result
(3.6), pp.870--872, and the original-star reduction opening (3.7), p.872.
This supplies a saturated distance-two source pair for the remaining
kernel comparison and field restriction of (3.7), pp.873--877.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] in
/-- If the full original commutator core lies in its Z-layer, the critical
distance cannot exceed two: the neighboring Z-span would be normal at
both ends of the base edge. -/
theorem original_distance_le_two_of_core_le_Z
    (g : Geometry R) (hcore : core R (alpha R) ≤ Z R (alpha R)) : g.b R ≤ 2 := by
  by_contra hnot
  have hlarge : 2 < g.b R := by omega
  have hab : Adjacent R (alpha R) (beta R) :=
    (adjacent_iff_exists_common R _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  let W := V R (beta R)
  have hWQ : W ≤ Q R (alpha R) :=
    (DistanceFour.Flags.RankOne.edgeRadius_le_radius (alpha R) (beta R) rfl hab).trans
      (g.V_le_Q hlarge (alpha R) rfl)
  have hZW : Z R (alpha R) ≤ W := by
    apply le_iSup_of_le (alpha R)
    apply le_iSup_of_le (show (cosetGraph R).dist (alpha R) (beta R) ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)]
      decide
  have hKW : Ltilde R (alpha R) ≤ normalizer (W : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hWQ le_rfl).trans (hcore.trans hZW)
  have hBW : stabilizer R (beta R) ≤ normalizer (W : Set (FreeAmalgam R)) :=
    V_normalized (beta R)
  have hAW : stabilizer R (alpha R) ≤ normalizer (W : Set (FreeAmalgam R)) := by
    rw [show stabilizer R (alpha R) = Mbar R from stabilizer_m_base R]
    rintro x ⟨m,rfl⟩
    obtain ⟨k,hk,r,hr,rfl⟩ := h.product m
    rw [map_mul]
    apply mul_mem
    · apply hKW
      rw [Ltilde_alpha,h.residual_eq]
      exact mem_map_of_mem _ hk
    · apply hBW
      rw [show stabilizer R (beta R) = Hbar R from stabilizer_h_base R]
      have hh : embedM R r ∈ Sbar R :=
        ⟨⟨r,hr⟩,(DFunLike.congr_fun (embedM_comp_subtype R) ⟨r,hr⟩).symm⟩
      rw [←Mbar_inf_Hbar] at hh
      exact hh.2
  have hzero : W = ⊥ := no_common_normal_at_edge R h.characteristic
    (alpha R) (beta R) rfl hab W
    (le_inf (hWQ.trans (fun _ hx => hx.1))
      (hWQ.trans (fun _ hx => hx.2 _ hab)))
    (normal_subgroupOf_of_le_normalizer hAW)
    (normal_subgroupOf_of_le_normalizer hBW)
  exact Z_alpha_ne_bot R h.radical.isPGroup h.radical_ne_bot
    (bot_unique (hZW.trans_eq hzero))

/-- A short original component forces critical distance two in its actual
holomorph graph, with the original radical unchanged. -/
theorem original_distance_two_of_short (hs : IsShort K) (g : Geometry R) : g.b R = 2 := by
  let := h.component_normal
  have hblock : IsBlock K := ⟨inferInstance,hs,h.component.subnormal⟩
  have hcore : core R (alpha R) = U R (alpha R) := by
    rw [graphCore_eq_intrinsic K R h.radical.isPGroup h.radical.twoCore_le h.residual_eq]
    change ((blockU K).map K.subtype).map (embedM R) = _
    rw [←BlockOmega.omega_commutator hblock,←h.initialCore_eq]
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,h.residual_eq,←map_commutator]
  have hle := original_distance_le_two_of_core_le_Z h g (hcore.trans_le (U_le_Z _))
  obtain ⟨g',hpos,heven⟩ := h.positive_even_geometry
  have he : g.b R = g'.b R := rfl
  rw [←he] at hpos heven
  obtain ⟨k,hk⟩ := heven
  omega

/-- The supplied distance-two replacement establishes distance two for
the ORIGINAL radical through the already proved whole-core shortness. -/
theorem original_distance_two_of_replacement
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (original : Geometry R) : original.b R = 2 :=
  original_distance_two_of_short h
    (DistanceTwoRecognition.short_and_natural_of_distance_two h d g hb).1 original


/-- The selected original source star has its own distance-two geometry,
full intrinsic input, saturated radical and original quotient marking.
Shortness transports along the actual component equivalence; no comparison
of the two amalgams or saturation of the minimum cut is assumed. -/
theorem exists_source_star_intrinsic_distance_two
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       ∃ hs : Input (K.subgroupOf M) (T.subgroupOf M) n F,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         T.subgroupOf M = R.subgroupOf M ∧
         (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M ∧
         K.subgroupOf M ⊔ pCore 2 M = ⊤ ∧
         ((T.subgroupOf K).map (DistanceTwoRecognition.componentProjection h)) =
           (R.subgroupOf K).map (DistanceTwoRecognition.componentProjection h) ∧
         ((∃ S : Sylow 2 M, (S : Subgroup M) = T.subgroupOf M) ↔
           ∃ S : Sylow 2 H, (S : Subgroup H) = R) ∧
         ∃ gs : Geometry (T.subgroupOf M), gs.b (T.subgroupOf M) = 2) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl⟩ :=
    exists_source_star_intrinsic_reduction h d
  have hshort := (DistanceTwoRecognition.short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  obtain ⟨gs,_,_⟩ := hs.positive_even_geometry
  exact ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,
    original_distance_two_of_short hs hstarshort gs⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
