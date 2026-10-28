module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Decomposition
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# The exact fixed factor inside the moving radius layer

The source first-hat action modulo H has moving dimension at most six.
Its residual image is the literal Vcirc, so |Vcirc:H| is at most 64.
The marked first dual quotient has order eight. Comparing orders with the
known disjoint U and H identifies Vcirc intersected with Z as U joined H;
the residual fixed subgroup in Vcirc is therefore exactly H.

This is the first-layer part of the collection in (4.5)(iii)--(v).
Moving the whole core fixed factor into Vcirc remains a separate obligation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed p.895,
using the first-hat estimate in (4.5.3)(i), printed p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open PathCentrality Higher
open Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
open Escape.Initial.Natural.Splitting
open Representation Representation.BinaryOffender

private theorem card_commutatorAction_le_sixtyFour_of_finrank
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E)
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (Offenders.linearize ρ)) ≤ 6) :
    Nat.card (commutatorAction ρ.range E) ≤ 64 := by
  let space : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  have he : space (commutatorAction ρ.range E) = Coinvariants.ker (Offenders.linearize ρ) := by
    apply le_antisymm
    · change commutatorAction ρ.range E ≤
        (Coinvariants.ker (Offenders.linearize ρ)).toAddSubgroup.toSubgroup'
      rw [commutatorAction_eq_closure, Subgroup.closure_le]
      rintro _ ⟨⟨a,g,rfl⟩,v,rfl⟩
      change -Additive.ofMul v + Offenders.linearize ρ g (Additive.ofMul v) ∈
        Coinvariants.ker (Offenders.linearize ρ)
      simpa only [sub_eq_add_neg,add_comm] using
        Coinvariants.sub_mem_ker (ρ := Offenders.linearize ρ) g (Additive.ofMul v)
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      change ρ g v.toMul / v.toMul ∈ commutatorAction ρ.range E
      rw [div_eq_mul_inv,commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨ρ g,g,rfl⟩,v.toMul,mul_comm _ _⟩
  change Nat.card (space (commutatorAction ρ.range E)) ≤ 64
  rw [he,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem moving_H_relIndex_on_window (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t)
    (hbounds : ActionBounds common earlier w) :
    (H R b).relIndex (Vcirc R b) ≤ 64 := by
  let := quotient_elementary earlier w
  let G := stabilizer R b
  let J := pResidual 2 G
  let π := localProjection source b w.color_b
  have hgen : J ⊔ (Q R b).subgroupOf G = ⊤ := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Q R b ≤ G from fun _ hx => hx.1)]
    change Ltilde R b ⊔ Q R b = (⊤ : Subgroup G).map G.subtype
    rw [source.local_generation b w.color_b,← MonoidHom.range_eq_map,range_subtype]
  have hJ : J.map π = ⊤ := by
    have hh := congrArg (Subgroup.map π) hgen
    have hk : (Q R b).subgroupOf G = π.ker := (localProjection_kernel source b w.color_b).symm
    rw [Subgroup.map_sup,hk,map_ker_self,sup_bot_eq,
      map_top_of_surjective _ (localProjection_surjective source b w.color_b)] at hh
    exact hh
  have hmap : ((Ltilde R b).subgroupOf G).map π = ⊤ := by
    change ((J.map G.subtype).comap G.subtype).map π = ⊤
    rw [comap_map_eq_self_of_injective G.subtype_injective]
    exact hJ
  have hi := displacement_card common earlier w (Ltilde R b) (Ltilde_le_stabilizer b)
  rw [hmap,← MonoidHom.range_eq_map] at hi
  have hh := card_commutatorAction_le_sixtyFour_of_finrank (headAction common earlier w) hbounds.1
  rw [hi] at hh
  have hcomm : ⁅hatV R b a,Ltilde R b⁆ = Vcirc R b := by
    apply le_antisymm
    · exact commutator_mono (hatV_le_radius R (by rw [SimpleGraph.dist_comm,w.moving.1])) le_rfl
    · have hmove := Early.moving_le_hatV source earlier w.color_b w.moving
      exact commutator_mono hmove le_rfl |>.trans' (by
        let V₀ := (V R b).subgroupOf G
        let := finite_stabilizer R b
        let : V₀.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R b)
        let := V_elementary_of_four_lt R w.color_b (by rw [earlier.distance]; decide)
        let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.subgroupOf
          (geometry.V_local b w.color_b (by rw [geometry.distance_constant b w.color_b]; exact common.large_distance))
        have he := commutator_isPPerfect_idempotent J V₀ (isPPerfect_pResidual 2)
          (IsElementaryAbelian.isPGroup 2 V₀) le_normalizer_of_normal
        have hm := congrArg (fun X : Subgroup G => X.map G.subtype) he
        rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le
          (geometry.V_local b w.color_b (by rw [geometry.distance_constant b w.color_b]; exact common.large_distance))] at hm
        exact hm.ge)
  rwa [hcomm] at hh
theorem moving_H_relIndex_le_sixtyFour (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (H R (alpha R)).relIndex (Vcirc R (alpha R)) ≤ 64 := by
  have h := moving_H_relIndex_on_window common earlier
    (forwardWindow common earlier p (i := 6) (by decide) (by decide) (by decide))
    (actionBounds_forward common earlier p (i := 6) (by decide) (by decide) (by decide))
  simpa only [show 6-2=4 by decide,p.center_eq] using h

theorem moving_card_le_twoFiftySix (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nat.card (Vcirc R (alpha R)) ≤ 256 := by
  have hHV : H R (alpha R) ≤ Vcirc R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
        (Vcirc_normalized (alpha R)))
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) (H R (alpha R))
    (Vcirc R (alpha R)) bot_le hHV
  rw [relIndex_bot_left,relIndex_bot_left] at hh
  have hc : Nat.card (H R (alpha R)) = 4 := Nat.le_antisymm
    (Early.H_card_le_four common earlier rfl) (Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
  rw [hc] at hh
  have hi := moving_H_relIndex_le_sixtyFour common earlier p
  omega

private theorem first_relIndex_eight (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Z R (alpha R)).relIndex (hatV R (alpha R) (p.walk.getVert 6)) = 8 := by
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  have hi : s.quotient.ker.index = 8 := by
    rw [index_ker,s.quotient.range_eq_top_of_surjective s.onto,card_top]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; norm_num
  rwa [s.kernel] at hi

theorem moving_Z_relIndex_eight (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (Z R (alpha R)).relIndex (Vcirc R (alpha R)) = 8 := by
  let := finite_stabilizer R (alpha R)
  let : Finite (Z R (alpha R)) := Finite.of_injective (inclusion (Z_le_stabilizer R _))
    (inclusion_injective _)
  have hn : Z R (alpha R) ≤ normalizer (Vcirc R (alpha R)) :=
    (Z_le_stabilizer R _).trans (Vcirc_normalized _)
  rw [← relIndex_sup_of_normalizes _ _ hn,
    ← (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
  exact first_relIndex_eight common earlier p

theorem moving_inf_Z_card_le_thirtyTwo (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nat.card (Vcirc R (alpha R) ⊓ Z R (alpha R) : Subgroup (FreeAmalgam R)) ≤ 32 := by
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Vcirc R (alpha R) ⊓ Z R (alpha R)) (Vcirc R (alpha R)) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,
    moving_Z_relIndex_eight common earlier p] at hm
  have hc := moving_card_le_twoFiftySix common earlier p
  omega
theorem moving_inf_Z_eq_U_sup_H (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Vcirc R (alpha R) ⊓ Z R (alpha R) = U R (alpha R) ⊔ H R (alpha R) := by
  have hUV : U R (alpha R) ≤ Vcirc R (alpha R) := commutator_mono (Z_le_VBall R _ 2) le_rfl
  have hHV : H R (alpha R) ≤ Vcirc R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
        (Vcirc_normalized (alpha R)))
  have hHZ := H_le_Z_of_central common (a := alpha R) rfl (earlier.centrality (alpha R) rfl)
  have hle : U R (alpha R) ⊔ H R (alpha R) ≤ Vcirc R (alpha R) ⊓ Z R (alpha R) :=
    sup_le (le_inf hUV (U_le_Z R _)) (le_inf hHV hHZ)
  have hn : H R (alpha R) ≤ normalizer (U R (alpha R)) :=
    (hHZ.trans (Z_le_stabilizer R _)).trans (U_normalized _)
  have hcard : Nat.card (U R (alpha R) ⊔ H R (alpha R) : Subgroup (FreeAmalgam R)) = 32 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (earlier.factor_inclusions common).2.2,
      U_card R common.natural]
    have hc : Nat.card (H R (alpha R)) = 4 := Nat.le_antisymm
      (Early.H_card_le_four common earlier rfl) (Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
    rw [hc]
  let := finite_stabilizer R (alpha R)
  let : Finite (Vcirc R (alpha R) ⊓ Z R (alpha R) : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (inf_le_right.trans (Z_le_stabilizer R _))) (inclusion_injective _)
  exact (eq_of_le_of_card_ge hle (by rw [hcard]; exact moving_inf_Z_card_le_thirtyTwo common earlier p)).symm

theorem moving_fixedFactor_eq_H (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Vcirc R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) = H R (alpha R) := by
  have hHV : H R (alpha R) ≤ Vcirc R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
        (Vcirc_normalized (alpha R)))
  have hHc : H R (alpha R) ≤ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) :=
    (earlier.factor_inclusions common).1.trans inf_le_right
  apply le_antisymm ?_ (le_inf hHV hHc)
  rintro x ⟨hx,hc⟩
  have hz : x ∈ Z R (alpha R) := core_fixedFactor_le_Z common earlier
    ⟨Vcirc_le_core rfl common.large_distance hx,hc⟩
  have hjoin : x ∈ U R (alpha R) ⊔ H R (alpha R) :=
    moving_inf_Z_eq_U_sup_H common earlier p ▸ (show x ∈ Vcirc R (alpha R) ⊓ Z R (alpha R) from ⟨hx,hz⟩)
  have hn : H R (alpha R) ≤ normalizer (U R (alpha R)) :=
    ((H_le_Z_of_central common rfl (earlier.centrality _ rfl)).trans
      (Z_le_stabilizer R _)).trans (U_normalized _)
  have hprod : x ∈ (U R (alpha R) : Set (FreeAmalgam R)) * (H R (alpha R) : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hjoin
  obtain ⟨u,hu,h,hh,huh⟩ := hprod
  change u*h=x at huh
  have huc : u ∈ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
    apply (centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))).mul_mem_cancel_right (hHc hh) |>.mp
    rwa [huh]
  have hue : u = 1 := (disjoint_iff_inf_le.mp common.disjoint) ⟨hu,U_le_Z R _ hu,huc⟩
  rw [hue,one_mul] at huh
  exact huh ▸ hh
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
