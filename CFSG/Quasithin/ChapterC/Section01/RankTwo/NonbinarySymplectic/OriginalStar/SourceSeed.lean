module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SourceSylow
/-!
# The original source Sylow seed and its characteristic centralizer

An ambient Sylow from the original odd-index radical supplies a mutually
normalizing component Sylow on the original graph. Its full fixed seed is
pulled back through the literal edge embedding. The arbitrary-degree seed
bounds then put the centralizer of its entire characteristic star over
K O₂(H), with the complete fixed attachment retained.

This is the original source construction in MS93 (3.4), printed pp.868--869.
It neither chooses a minimum characteristic replacement nor assumes that
this star centralizer preserves the marked radical image in (3.7).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] in
/-- The original odd-index witness supplies a component Sylow normalized by
R in its own holomorph graph. No characteristic replacement is selected. -/
theorem exists_vertex_sylow :
    ∃ P : Sylow 2 (Ltilde R (alpha R)),
      Q R (beta R) ≤ normalizer
        (componentSylowActor R (alpha R) P : Set (FreeAmalgam R)) ∧
      componentSylowActor R (alpha R) P ≤
        normalizer (Q R (beta R) : Set (FreeAmalgam R)) := by
  let := h.component_normal
  obtain ⟨S,hRS,hSN⟩ := h.exists_normalizing_sylow
  let P := componentSylow K S
  have hA : K.map (embedM R) = Ltilde R (alpha R) := by
    rw [Ltilde_alpha,h.residual_eq]
  let e : K ≃* Ltilde R (alpha R) :=
    (K.equivMapOfInjective (embedM R) (embedM_injective R)).trans
      (MulEquiv.subgroupCongr hA)
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  let P' := P.mapSurjective (f := e.toMonoidHom) hsurj
  have he : (Ltilde R (alpha R)).subtype.comp e.toMonoidHom =
      (embedM R).comp K.subtype := by ext x; rfl
  have hactor : componentSylowActor R (alpha R) P' =
      (K ⊓ (S : Subgroup H)).map (embedM R) := by
    change (((P.mapSurjective (f := e.toMonoidHom) hsurj :
      Sylow 2 (Ltilde R (alpha R))) : Subgroup (Ltilde R (alpha R))).map
        (Ltilde R (alpha R)).subtype) = _
    rw [Sylow.coe_mapSurjective,map_map,he,←map_map,componentSylow_coe,
      subgroupOf_map_subtype,inf_comm]
  have hSP : (S : Subgroup H) ≤ normalizer (K ⊓ (S : Subgroup H) : Set H) :=
    (le_inf (by rw [normalizer_eq_top]; exact le_top) S.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  refine ⟨P',?_,?_⟩
  · rw [hactor,Q_beta]
    exact (map_mono (f := embedM R) (hRS.trans hSP)).trans
      (le_normalizer_map (H := K ⊓ (S : Subgroup H)) (embedM R))
  · rw [hactor,Q_beta]
    exact (map_mono (f := embedM R) (inf_le_right.trans hSN)).trans
      (le_normalizer_map (H := R) (embedM R))

/-- The actual original seed has bounded full order, its exact graph embedding,
and edge normalization. The fixed attachment is included in the order bound. -/
theorem exists_source_seed :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      Nat.card (Y.map (embedS R)) ≤ Nat.card F ^ 2 ∧
      stabilizer R (alpha R) ⊓
        centralizer (Y.map (embedS R) : Set (FreeAmalgam R)) ≤
        Ltilde R (alpha R) ⊔ Q R (alpha R) := by
  obtain ⟨P,hTP,_⟩ := exists_vertex_sylow h
  let B := componentSylowSeed R (alpha R) P
  obtain ⟨g,hpos,_⟩ := h.positive_even_geometry
  have hUQ : U R (alpha R) ≤ Q R (alpha R) :=
    (DistanceEight.U_le_Z R _).trans
      ((g.omega_bound _ rfl (by rwa [g.distance_constant _ rfl])).trans (omegaCenter_le _))
  have hBT : B ≤ Q R (beta R) :=
    (inf_le_left.trans hUQ).trans (Q_le_adjacent_h R rfl (base_adjacent R))
  have hnU : Q R (beta R) ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    (show Q R (beta R) ≤ stabilizer R (alpha R)
      from fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _))).trans (U_normalized _)
  have hnC : normalizer (componentSylowActor R (alpha R) P : Set (FreeAmalgam R)) ≤
      normalizer (centralizer
        (componentSylowActor R (alpha R) P : Set (FreeAmalgam R)) : Set _) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hnB : Q R (beta R) ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (le_inf hnU (hTP.trans hnC)).trans inf_normalizer_le_normalizer_inf
  let Y := B.comap (embedS R)
  have hY : Y.map (embedS R) = B := by
    apply map_comap_eq_self
    rw [←embedM_comp_subtype,MonoidHom.range_comp,range_subtype]
    simpa only [Q_beta] using hBT
  refine ⟨P,Y,hY,?_,?_,?_⟩
  · rwa [hY]
  · rw [hY]
    exact componentSylowSeed_card_le h rfl P
  · rw [hY]
    exact componentSylowSeed_centralizer_le h rfl P

/-- The centralizer of the full original characteristic star has inner action.
This is the actual source star, with the original R and original graph. -/
theorem starCentralizer_le_component_core
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P) :
    (starCentralizer R Y).map R.subtype ≤ K ⊔ pCore 2 H := by
  have hcent : (starCentralizer R Y).map R.subtype ≤
      centralizer (Y.map R.subtype : Set H) :=
    (starCentralizer_map R Y).le.trans inf_le_right |>.trans
      (centralizer_le (map_mono (le_starSpan R Y)))
  have hgraph : ((starCentralizer R Y).map R.subtype).map (embedM R) ≤
      stabilizer R (alpha R) ⊓
        centralizer ((Y.map R.subtype).map (embedM R) : Set (FreeAmalgam R)) := by
    rintro x ⟨r,hr,rfl⟩
    refine ⟨?_,?_⟩
    · rw [alpha,stabilizer_m_base]
      exact ⟨r,rfl⟩
    · rintro y ⟨s,hs,rfl⟩
      simpa only [map_mul] using congrArg (embedM R) (hcent hr s hs)
  have hgraphS : (starCentralizer R Y).map (embedS R) ≤
      stabilizer R (alpha R) ⊓ centralizer (Y.map (embedS R) : Set (FreeAmalgam R)) := by
    simpa only [map_map,embedM_comp_subtype] using hgraph
  have hinner : (starCentralizer R Y).map (embedS R) ≤
      Ltilde R (alpha R) ⊔ Q R (alpha R) := hgraphS.trans (by
    rw [hY]
    exact componentSylowSeed_centralizer_le h rfl P)
  apply (map_le_map_iff_of_injective (embedM_injective R)).mp
  rw [map_map,embedM_comp_subtype,Subgroup.map_sup]
  rwa [Ltilde_alpha,h.residual_eq,Q_alpha R h.radical.isPGroup h.radical.twoCore_le] at hinner

/-- A chosen original star seed supplies the source's inner characteristic
cut, together with its literal fixed-seed equation, normalization and order. -/
theorem exists_inner_source_star :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      Nat.card (Y.map (embedS R)) ≤ Nat.card F ^ 2 ∧
      (starCentralizer R Y).map R.subtype ≤ K ⊔ pCore 2 H := by
  obtain ⟨P,Y,hY,hn,hcard,_⟩ := exists_source_seed h
  exact ⟨P,Y,hY,hn,hcard,starCentralizer_le_component_core h P Y hY⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
