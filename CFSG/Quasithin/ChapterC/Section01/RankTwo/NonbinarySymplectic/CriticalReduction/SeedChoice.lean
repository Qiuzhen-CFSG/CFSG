module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SourceSylow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedTransport

/-!
# The literal full-Sylow seed on the replacement graph

A Sylow chosen using the original radical is transported to the base vertex
of the replacement's graph. Its fixed seed lies in the edge kernel and is
normalized by that kernel. Both its cardinal bound and the inner-containment
conclusion use the same actual component Sylow and retain the fixed cover
kernel. No odd-index witness is required of the replacement radical.

Source: MS93 (3.4) and Section 7, pp.868, 932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The source component Sylow is normalized by the actual replacement edge. -/
theorem Input.exists_replacement_vertex_sylow :
    ∃ P : Sylow 2 (Ltilde d.radical (alpha d.radical)),
      Q d.radical (beta d.radical) ≤ normalizer
        (Sp4Four.componentSylowActor d.radical (alpha d.radical) P : Set (FreeAmalgam d.radical)) ∧
      Sp4Four.componentSylowActor d.radical (alpha d.radical) P ≤
        normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨P,hTP,hPT⟩ := h.exists_replacement_component_sylow d
  let A := K.subgroupOf d.overgroup
  have hA : A.map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,h.replacement_residual d]
  let e : A ≃* Ltilde d.radical (alpha d.radical) :=
    (A.equivMapOfInjective (embedM d.radical) (embedM_injective d.radical)).trans
      (MulEquiv.subgroupCongr hA)
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  let P' := P.mapSurjective (f := e.toMonoidHom) hsurj
  have he : (Ltilde d.radical (alpha d.radical)).subtype.comp e.toMonoidHom =
      (embedM d.radical).comp A.subtype := by ext x; rfl
  have hactor : Sp4Four.componentSylowActor d.radical (alpha d.radical) P' =
      ((P : Subgroup A).map A.subtype).map (embedM d.radical) := by
    change (((P.mapSurjective (f := e.toMonoidHom) hsurj :
      Sylow 2 (Ltilde d.radical (alpha d.radical))) :
      Subgroup (Ltilde d.radical (alpha d.radical))).map
        (Ltilde d.radical (alpha d.radical)).subtype) = _
    rw [Sylow.coe_mapSurjective,map_map,he,←map_map]
  refine ⟨P',?_,?_⟩
  · rw [hactor,Q_beta]
    exact (map_mono hTP).trans (le_normalizer_map (embedM d.radical))
  · rw [hactor,Q_beta]
    exact (map_mono hPT).trans (le_normalizer_map (embedM d.radical))

variable [Finite F] [CharP F 2]

/-- The source seed, its edge normalization, size and inner centralizer are
constructed together on the actual minimum replacement. -/
theorem Input.exists_replacement_source_seed :
    ∃ P : Sylow 2 (Ltilde d.radical (alpha d.radical)), ∃ Y : Subgroup d.radical,
      Y.map (embedS d.radical) =
        Sp4Four.componentSylowSeed d.radical (alpha d.radical) P ∧
      Q d.radical (beta d.radical) ≤
        normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)) ∧
      Nat.card (Y.map (embedS d.radical)) ≤ Nat.card F ^ 2 ∧
      stabilizer d.radical (alpha d.radical) ⊓
        centralizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)) ≤
        Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (alpha d.radical) := by
  obtain ⟨P,hTP,_⟩ := h.exists_replacement_vertex_sylow d
  let B := Sp4Four.componentSylowSeed d.radical (alpha d.radical) P
  obtain ⟨g,hpos,_⟩ := h.replacement_positive_even_geometry d
  have hUQ : U d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) :=
    (DistanceEight.U_le_Z d.radical _).trans
      ((g.omega_bound _ rfl (by rwa [g.distance_constant _ rfl])).trans (omegaCenter_le _))
  have hBT : B ≤ Q d.radical (beta d.radical) :=
    (inf_le_left.trans hUQ).trans
      (Q_le_adjacent_h d.radical rfl (base_adjacent d.radical))
  have hnU : Q d.radical (beta d.radical) ≤
      normalizer (U d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical (beta d.radical) ≤ stabilizer d.radical (alpha d.radical)
      from fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _))).trans
        (U_normalized _)
  have hnC : normalizer
      (Sp4Four.componentSylowActor d.radical (alpha d.radical) P : Set (FreeAmalgam d.radical)) ≤
      normalizer (centralizer
        (Sp4Four.componentSylowActor d.radical (alpha d.radical) P : Set (FreeAmalgam d.radical)) : Set _) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hnB : Q d.radical (beta d.radical) ≤ normalizer (B : Set (FreeAmalgam d.radical)) :=
    (le_inf hnU (hTP.trans hnC)).trans inf_normalizer_le_normalizer_inf
  let Y := B.comap (embedS d.radical)
  have hY : Y.map (embedS d.radical) = B := by
    apply map_comap_eq_self
    rw [← embedM_comp_subtype, MonoidHom.range_comp, range_subtype]
    simpa only [Q_beta] using hBT
  refine ⟨P,Y,hY,?_,?_,?_⟩
  · rwa [hY]
  · rw [hY]
    exact h.replacement_componentSylowSeed_card_le d rfl P
  · rw [hY]
    exact h.replacement_componentSylowSeed_centralizer_le d rfl P

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
