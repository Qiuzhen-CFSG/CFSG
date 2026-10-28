module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels

/-!
# Central seed intersections in the original Borel geometry

A normal subgroup of the sixteen-element Borel outside its distinguished
Thompson mover fixes only the Borel's fixed line on the natural quotient.
A checked certificate on the sixteen Borel elements and fifteen duads proves
this without enumerating subgroups. The full-cover movement bounds then
show that it fixes index eight on either moving cover. Restoring the full
central attachment identifies its fixed subgroup in the whole seed with
the incident edge seed.

For distinct adjacent movers, central generation of omega at the opposite
vertex excludes containment of its two-core in the starting mover. Apply
the normal-actor calculation to that actual opposite core: the two whole
seeds intersect in exactly the common edge seed.

Failure of the distance-four kernel normalization already forces central
generation at every component vertex. Thus the intersection equality
applies there without a new central-generation premise. It puts the
critical line in the left edge seed when the left movers differ, and the
restricted-kernel failure line in the right edge seed when the right movers
differ. OriginalSylowExceptional applies these facts to the literal c.L,d.S.
The original projection kernel E, its odd quotient E/Q, both full moving
covers and their central attachments are retained.

These are the distinct-mover intersection and line placements in the proof
of MS93 (5.12)(1). The required stabilizer centrality, the equal-mover case,
the remaining critical-image cases and the terminal contradiction are not
asserted here. CoreExhaustion and the whole block reconstruction still
require those arguments.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(b,c) and (5.12)(1), printed pp.915--917,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open CFSG.Quasithin.ChapterB.Offenders.Six
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

private theorem normal_duad_certificate : ∀ (i : Fin 16) (d : Duad), d ≠ 0 →
    (∀ j : Fin 16, (duadSet d).image
      (BorelCalculation.words j * BorelCalculation.words i * (BorelCalculation.words j)⁻¹) = duadSet d) →
    ∃ k : Fin 8, dWords k = BorelCalculation.words i := by decide +kernel

private theorem normal_duad_fixer_le_plane (A : Subgroup S) (hA : A ≤ borel)
    (hN : borel ≤ normalizer (A : Set S)) (d : Duad) (hd : d ≠ 0)
    (hf : ∀ a ∈ A, a • d = d) : A ≤ D := by
  intro a ha
  obtain ⟨i,rfl⟩ := BorelCalculation.words_complete a (hA ha)
  obtain ⟨k,hk⟩ := normal_duad_certificate i d hd (fun j => by
    rw [←duadSet_smul]
    rw [hf _ ((mem_normalizer_iff.mp (hN (BorelCalculation.words_in_borel j)) _).mp ha)])
  rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
  exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨k,hk⟩

private theorem normal_small_codim_le_plane (A : Subgroup S) (hA : A ≤ borel)
    (hN : borel ≤ normalizer (A : Set S))
    (hf : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 2) : A ≤ D := by
  classical
  let F := fixedSpace (naturalRepresentation (Fin 6)) A
  have hd : 2 ≤ Module.finrank (ZMod 2) F := by
    have hh := fixedCodim_add_finrank (naturalRepresentation (Fin 6)) A
    rw [finrank_natural_even (Fin 6) (by decide)] at hh
    change fixedCodim (naturalRepresentation (Fin 6)) A + Module.finrank (ZMod 2) F = 4 at hh
    omega
  have hcard : 4 ≤ Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have hex : ∃ v : F, (v : natural (Fin 6)) ≠ 0 ∧ (v : natural (Fin 6)) ≠ naturalDuad 0 := by
    by_contra! hn
    let f : F → Bool := fun v => if (v : natural (Fin 6)) = 0 then false else true
    have hi : Function.Injective f := by
      intro v w he
      by_cases hv : (v : natural (Fin 6)) = 0 <;>
        by_cases hw : (w : natural (Fin 6)) = 0
      · exact Subtype.ext (hv.trans hw.symm)
      · simp only [f,hv,hw,ite_true,ite_false] at he
        cases he
      · simp only [f,hv,hw,ite_true,ite_false] at he
        cases he
      · exact Subtype.ext ((hn v hv).trans (hn w hw).symm)
    have hh := Nat.card_le_card_of_injective f hi
    have hb : Nat.card Bool = 2 := by simp
    omega
  obtain ⟨v,hv,hv0⟩ := hex
  obtain ⟨d,hde⟩ := natural_cases v hv
  have hdn : d ≠ 0 := by rintro rfl; exact hv0 hde.symm
  have hfix (a : S) (ha : a ∈ A) : a • d = d := by
    apply naturalDuad_injective
    rw [←naturalDuad_map,hde]
    exact v.property ⟨a,ha⟩
  exact normal_duad_fixer_le_plane A hA hN d hdn hfix

private theorem normal_small_codim_le_conjugate_plane (A : Subgroup S) (u : S)
    (hA : A ≤ borel.map (MulAut.conj u).toMonoidHom)
    (hN : borel.map (MulAut.conj u).toMonoidHom ≤ normalizer (A : Set S))
    (hf : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 2) :
    A ≤ D.map (MulAut.conj u).toMonoidHom := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have hB := conjBy_inv borel u
  have hback : A.map f ≤ borel := (map_mono hA).trans_eq hB
  have hnorm : borel ≤ normalizer (A.map f : Set S) := by
    rw [←hB]
    exact (map_mono hN).trans (A.le_normalizer_map f)
  have hh := normal_small_codim_le_plane (A.map f) hback hnorm (by
    simpa only [f,fixedCodim_map_conj] using hf)
  have hm := map_mono (f := (MulAut.conj u).toMonoidHom) hh
  exact (conjBy_inv' A u).symm.le.trans hm

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem borel_normal_actor_fixed_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (A : Subgroup (FreeAmalgam Rg)) (hAT : A ≤ Q Rg t)
    (hN : Q Rg t ≤ normalizer (A : Set (FreeAmalgam Rg)))
    (hnot : ¬ A ≤ edgeOffenderJoin a t) :
    (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg a) = 8 := by
  have hAG : A ≤ stabilizer Rg a := hAT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz ha hat
  let A₀ := A.comap i
  have hAm : A₀.map i = A := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hAR : A₀ ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hAm,hiR]
    exact hAT
  have hAN : Rg ≤ normalizer (A₀ : Set M) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    change i y ∈ A ↔ i (x*y*x⁻¹) ∈ A
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hN (hiR ▸ mem_map_of_mem i hx)) (i y)
  have hpiN : borel.map (MulAut.conj u).toMonoidHom ≤
      normalizer (A₀.map π : Set S) := by
    rw [←hR]
    exact (map_mono hAN).trans (A₀.le_normalizer_map π)
  have hlo : 3 ≤ fixedCodim (naturalRepresentation (Fin 6)) (A₀.map π) := by
    by_contra! hsmall
    have hplane := normal_small_codim_le_conjugate_plane (A₀.map π) u
      ((map_mono hAR).trans_eq hR) hpiN (by omega)
    have hle : A₀ ≤ borelPlane h e hz hk u :=
      le_inf hAR (map_le_iff_le_comap.mp hplane)
    apply hnot
    rw [remaining_join_in_chart h e hz hk u (Or.inr hR) ha hat i hi hiR hiQ hiU,←hAm]
    exact map_mono hle
  have hlow : 8 ≤ (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg a) := by
    have hh := (Nat.pow_le_pow_right (by decide : 0 < 2) hlo).trans
      (cubic_cover_movement_bounds h e hz hk A₀).1
    rw [←hAm,←hiU,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hi,
      relIndex_map_map_of_injective _ _ hi,inf_relIndex_left]
    exact hh
  have hhi : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg a) ≤ 8 := by
    rw [←borel_edge_fixed_index h e hz hk u hR ha hat]
    let := finite_Z Rg a
    let : Finite (U Rg a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
    exact relIndex_le_of_le_left (centralizer_le hAT) index_ne_zero_of_finite
  exact le_antisymm hhi hlow

include h e hz hk in
/-- A normal edge actor outside the proper Thompson mover fixes exactly
 the whole edge seed. The computation uses both full cubic covers. -/
theorem borel_normal_actor_seed_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (A : Subgroup (FreeAmalgam Rg)) (hAT : A ≤ Q Rg t)
    (hN : Q Rg t ≤ normalizer (A : Set (FreeAmalgam Rg)))
    (hnot : ¬ A ≤ edgeOffenderJoin a t) :
    Z Rg a ⊓ centralizer (A : Set (FreeAmalgam Rg)) = Z Rg t := by
  have he := borel_normal_actor_fixed_index h e hz hk u hR ha hat A hAT hN hnot
  have ht := borel_edge_fixed_index h e hz hk u hR ha hat
  let F := U Rg a ⊓ centralizer (A : Set (FreeAmalgam Rg))
  let E := U Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))
  have hEF : E ≤ F := inf_le_inf_left _ (centralizer_le hAT)
  have hmul := relIndex_mul_relIndex E F (U Rg a) hEF inf_le_left
  have hF : F.relIndex (U Rg a) = 8 := by
    simpa only [F,inf_relIndex_left] using he
  have hE : E.relIndex (U Rg a) = 8 := by
    simpa only [E,inf_relIndex_left] using ht
  rw [hF,hE] at hmul
  have hm : F = E := le_antisymm (relIndex_eq_one.mp (by omega : E.relIndex F = 1)) hEF
  have htc : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hseed := terminal_edge_seed_central htc
  have hseedN : Z Rg t ≤ normalizer (U Rg a : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg ha hat).trans (Z_le_stabilizer Rg a)).trans (U_normalized a)
  have hfixed : Z Rg a ⊓ centralizer (A : Set (FreeAmalgam Rg)) =
      Z Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    rw [vertex_seed_eq_moving_sup_edge h e hz ha hat,sup_comm (U Rg a),
      inf_centralizer_sup_of_centralizing _ _ _ hseedN (hseed.trans (centralizer_le hAT)),
      inf_centralizer_sup_of_centralizing _ _ _ hseedN hseed]
    exact congrArg (fun H => Z Rg t ⊔ H) hm
  rw [hfixed]
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    rw [Z,if_neg (by simp [htc])]
    have hZX := (sourceGeometry h).omega_bound a ha (by
      rw [(sourceGeometry h).distance_constant _ ha]; exact sourceDistance_pos h)
    exact mem_omegaCenter_iff.mpr ⟨
      (Q_le_adjacent_h Rg htc hat) (omegaCenter_le _ (hZX hx)),
      (mem_omegaCenter_iff.mp (hZX hx)).2.1,hxc⟩
  · exact le_inf (adjacent_Z_le Rg ha hat) hseed

include h e hz hk in
/-- Distinct adjacent movers and central generation at the opposite
 vertex force the full seed intersection to equal the common edge seed. -/
theorem borel_distinct_centrally_generated_seed_intersection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hgen : X Rg c = U Rg c ⊔
      (X Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)))) :
    Z Rg a ⊓ Z Rg c = Z Rg t := by
  have hnot : ¬ Q Rg c ≤ edgeOffenderJoin a t := fun hh =>
    borel_opposite_containing_core_nonsplit h e hz hk u hR hc ha hct hat
      (Ne.symm hne) hh hgen
  have htc : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hfixed := borel_normal_actor_seed_fixed h e hz hk u hR ha hat (Q Rg c)
    (Q_le_adjacent_h Rg htc hct)
    ((show Q Rg t ≤ stabilizer Rg c from fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans
      (Q_normalized Rg c)) hnot
  apply le_antisymm
  · rw [←hfixed]
    exact inf_le_inf_left _ (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c hc))
  · exact le_inf (adjacent_Z_le Rg ha hat) (adjacent_Z_le Rg hc hct)

include h e hz hk in
/-- In the distance-four failure branch, every distinct adjacent mover
 comparison has the full edge seed as intersection. Central generation is
 derived from failure of normalization, rather than assumed. -/
theorem borel_four_failure_seed_intersections
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    {v w t : Vertex Rg} (hv : color Rg v = false) (hw : color Rg w = false)
    (hvt : Adjacent Rg v t) (hwt : Adjacent Rg w t)
    (hne : edgeOffenderJoin v t ≠ edgeOffenderJoin w t) :
    Z Rg v ⊓ Z Rg w = Z Rg t := by
  have hgen := (borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2 hnorm
  exact borel_distinct_centrally_generated_seed_intersection h e hz hk u hR
    hv hw hvt hwt hne (hgen w hw).1

include h e hz hk in
/-- The two distinct-mover cases in MS93 (5.12)(1) put the original
 critical line in its left edge seed, and the failure line in the right
 edge seed. The actual overlapping paths and full central parts remain. -/
theorem borel_four_failure_edge_lines
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
    (edgeOffenderJoin a (p.walk.getVert 1) ≠ edgeOffenderJoin c (p.walk.getVert 1) →
      ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg (p.walk.getVert 1)) ∧
    (edgeOffenderJoin c (p.walk.getVert 3) ≠ edgeOffenderJoin z (p.walk.getVert 3) →
      H ≤ Z Rg (p.walk.getVert 3)) := by
  let c := p.walk.getVert 2
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 3) (by omega))
    change Adjacent Rg (p.walk.getVert 3) (p.walk.getVert 4) at hh
    rw [←hl,SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm Rg hh
  have hgen := (borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2 hnorm
  have hZaV : Z Rg a ≤ V Rg c :=
    (Z_le_localZSpan Rg a c).trans (localZSpan_le_V Rg (by
      rw [p.dist_start (by omega)]))
  have hZzV : Z Rg z ≤ V Rg c :=
    (Z_le_localZSpan Rg z c).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_end,hl]))
  have hRline : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg c := by
    rw [←(hgen c hc).2]
    exact (commutator_mono hZaV hZzV).trans
      (radius_bounds_at h e hz hk c hc a z).2.1
  constructor
  · intro hne
    rw [←borel_four_failure_seed_intersections h e hz hk u hR p q hqa hp hnorm
      p.start_color hc hab hcb hne]
    exact le_inf (critical_seed_commutator_le h p) hRline
  · intro hne
    rw [←borel_four_failure_seed_intersections h e hz hk u hR p q hqa hp hnorm
      hc p.end_color hct hzt hne]
    have hh := borel_four_kernel_failure_midpoint h e hz hk u hR p q hqa hp hnorm
    exact le_inf (hh.trans inf_le_left |>.trans inf_le_right) (hh.trans inf_le_right)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
