module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EscapeChoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IntersectionMovement

/-!
# The bad source star selects an actual escaping full-Sylow seed

The general q² section bound chooses a conjugate of the bad transported
seed. Transporting its actual component Sylow preserves the two incident
edges, edge normalization, and containment in the source star. The critical
radius puts it in the start core and endpoint stabilizer, so the proved
reciprocal comparison makes both critical indices equal the original q.

This discharges the escaping-seed selection in MS93 (3.4), printed p.868,
on the characteristic replacement of Section 7. The subsequent path
contradiction and the two final star bounds remain separate assertions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (input : Input K R n F)
variable (reduction : CharacteristicReduction K R)
include input

theorem Input.replacement_bad_star_critical_seed
    (geometry : Geometry reduction.radical) (hb : 0 < geometry.b reduction.radical)
    {z : Vertex reduction.radical} (path : CriticalPath reduction.radical geometry (alpha reduction.radical) z)
    (Y : Subgroup reduction.radical) (P : Sylow 2 (Ltilde reduction.radical (alpha reduction.radical)))
    (hY : Y.map (embedS reduction.radical)=componentSylowSeed reduction.radical (alpha reduction.radical) P)
    (hn : Q reduction.radical (beta reduction.radical) ≤ normalizer (Y.map (embedS reduction.radical) : Set (FreeAmalgam reduction.radical)))
    (hbad : ¬ ⁅sourceStarAlpha reduction.radical Y,Ltilde reduction.radical (alpha reduction.radical)⁆ ≤ Z reduction.radical (alpha reduction.radical)) :
    ∃ d t : Vertex reduction.radical, ∃ P' : Sylow 2 (Ltilde reduction.radical d),
      color reduction.radical d=false ∧ Adjacent reduction.radical (alpha reduction.radical) t ∧ Adjacent reduction.radical d t ∧
      Q reduction.radical t ≤ normalizer (componentSylowSeed reduction.radical d P' : Set (FreeAmalgam reduction.radical)) ∧
      componentSylowSeed reduction.radical d P' ≤ sourceStarAlpha reduction.radical Y ∧
      ¬ Z reduction.radical z ≤ normalizer ((componentSylowSeed reduction.radical d P' ⊔ Z reduction.radical (alpha reduction.radical) :
        Subgroup (FreeAmalgam reduction.radical)) : Set _) := by
  obtain ⟨g,h,hbadSeed⟩ := exists_bad_transported_seed reduction.radical Y hbad
  let A := ((Y.map (embedS reduction.radical)).map (MulAut.conj (h : FreeAmalgam reduction.radical)).toMonoidHom).map
    (MulAut.conj (g : FreeAmalgam reduction.radical)).toMonoidHom
  let d := act reduction.radical (g : FreeAmalgam reduction.radical)⁻¹ (act reduction.radical (h : FreeAmalgam reduction.radical)⁻¹ (alpha reduction.radical))
  let t := act reduction.radical (g : FreeAmalgam reduction.radical)⁻¹ (beta reduction.radical)
  obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed reduction.radical Y P hY hn g h
  have hA : A=componentSylowSeed reduction.radical d P' := hP'
  have hd : color reduction.radical d=false := by simp only [d,action_preserves_color]; rfl
  have hAU : A ≤ U reduction.radical d := hA.le.trans inf_le_left
  have hAn : Q reduction.radical t ≤ normalizer (A : Set (FreeAmalgam reduction.radical)) := by rw [hA]; exact hn'
  have hcard : Nat.card A ≤ Nat.card F ^ 2 := by
    rw [hA]
    exact input.replacement_componentSylowSeed_card_le reduction hd P'
  have hAstar : A ≤ sourceStarAlpha reduction.radical Y := by
    have hbeta : (starSpan reduction.radical Y).map (embedS reduction.radical) =
        (⨆ h : Hbar reduction.radical, (Y.map (embedS reduction.radical)).map (MulAut.conj (h : FreeAmalgam reduction.radical)).toMonoidHom) ⊔
          Z reduction.radical (beta reduction.radical) := by
      simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph reduction.radical Y
    have hYbeta : (Y.map (embedS reduction.radical)).map (MulAut.conj (h : FreeAmalgam reduction.radical)).toMonoidHom ≤
        (starSpan reduction.radical Y).map (embedS reduction.radical) := by
      rw [hbeta]
      exact (le_iSup (fun k : Hbar reduction.radical => (Y.map (embedS reduction.radical)).map
        (MulAut.conj (k : FreeAmalgam reduction.radical)).toMonoidHom) h).trans le_sup_left
    exact (map_mono hYbeta).trans ((sourceStarAlpha_le_iff reduction.radical Y _).mp le_rfl g)
  obtain ⟨hat,hdt⟩ := transported_seed_edges reduction.radical g h
  obtain ⟨k,hk,hnk⟩ := input.replacement_exists_critical_escape reduction geometry hb
    rfl hd hat hdt path.critical A hAU hcard hbadSeed hAn
  let A' := A.map (MulAut.conj k⁻¹).toMonoidHom
  have hkstar : (sourceStarAlpha reduction.radical Y).map (MulAut.conj k⁻¹).toMonoidHom =
      sourceStarAlpha reduction.radical Y := mem_normalizer_iff_map_conj_eq.mp
        (sourceStarAlpha_normalized reduction.radical Y ((stabilizer reduction.radical (alpha reduction.radical)).inv_mem hk))
  have hkZ : (Z reduction.radical (alpha reduction.radical)).map (MulAut.conj k⁻¹).toMonoidHom = Z reduction.radical (alpha reduction.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized reduction.radical (alpha reduction.radical)
      ((stabilizer reduction.radical (alpha reduction.radical)).inv_mem hk))
  have hA'star : A' ≤ sourceStarAlpha reduction.radical Y := (map_mono hAstar).trans_eq hkstar
  have hnjoin : ¬ Z reduction.radical z ≤ normalizer ((A' ⊔ Z reduction.radical (alpha reduction.radical) : Subgroup (FreeAmalgam reduction.radical)) : Set _) := by
    simpa only [Subgroup.map_sup,hkZ] using hnk
  obtain ⟨P'',hP''⟩ := exists_componentSylowSeed_act reduction.radical d P' k
  have hAA : A'=componentSylowSeed reduction.radical (act reduction.radical k d) P'' := by
    change A.map (MulAut.conj k⁻¹).toMonoidHom = _
    rw [hA]
    exact hP''.symm
  have hka : act reduction.radical k (alpha reduction.radical)=alpha reduction.radical := hk
  have hat' : Adjacent reduction.radical (alpha reduction.radical) (act reduction.radical k t) := by
    simpa only [hka] using (adjacent_act_iff reduction.radical k (alpha reduction.radical) t).mpr hat
  have hdt' : Adjacent reduction.radical (act reduction.radical k d) (act reduction.radical k t) :=
    (adjacent_act_iff reduction.radical k d t).mpr hdt
  have hn' := map_seed_normalized_at_act reduction.radical A hAn k
  change Q reduction.radical (act reduction.radical k t) ≤ normalizer (A' : Set (FreeAmalgam reduction.radical)) at hn'
  rw [hAA] at hn'
  refine ⟨act reduction.radical k d,act reduction.radical k t,P'',(action_preserves_color reduction.radical k d).trans hd,
    hat',hdt',hn',?_,?_⟩
  · exact hAA ▸ hA'star
  · exact hAA ▸ hnjoin

theorem Input.replacement_bad_star_critical_indices_eq_field
    (geometry : Geometry reduction.radical) (hb : 0 < geometry.b reduction.radical)
    {z : Vertex reduction.radical} (path : CriticalPath reduction.radical geometry (alpha reduction.radical) z)
    (Y : Subgroup reduction.radical) (P : Sylow 2 (Ltilde reduction.radical (alpha reduction.radical)))
    (hY : Y.map (embedS reduction.radical)=componentSylowSeed reduction.radical (alpha reduction.radical) P)
    (hn : Q reduction.radical (beta reduction.radical) ≤ normalizer (Y.map (embedS reduction.radical) : Set (FreeAmalgam reduction.radical)))
    (hbad : ¬ ⁅sourceStarAlpha reduction.radical Y,Ltilde reduction.radical (alpha reduction.radical)⁆ ≤ Z reduction.radical (alpha reduction.radical)) :
    (Q reduction.radical z).relIndex (Z reduction.radical (alpha reduction.radical))=Nat.card F ∧ (Q reduction.radical (alpha reduction.radical)).relIndex (Z reduction.radical z)=Nat.card F := by
  obtain ⟨d,t,P',hd,hat,hdt,hn',hseed,hnot⟩ :=
    input.replacement_bad_star_critical_seed reduction geometry hb path Y P hY hn hbad
  exact input.replacement_critical_indices_eq_field_of_seed_escape reduction path hb
    (componentSylowSeed reduction.radical d P')
    (hseed.trans (input.replacement_sourceStarAlpha_le_critical_endpoint_stabilizer
      reduction geometry hb path Y P hY hn))
    (hseed.trans (input.replacement_sourceStarAlpha_le_own_core
      reduction geometry hb Y P hY hn)) hnot


/-- Failure of the first star bound selects a full-Sylow seed which actually
moves the entire endpoint intersection, including its central attachment. -/
theorem Input.replacement_bad_star_moving_seed
    (geometry : Geometry reduction.radical) (hb : 0 < geometry.b reduction.radical)
    {z : Vertex reduction.radical}
    (path : CriticalPath reduction.radical geometry (alpha reduction.radical) z)
    (Y : Subgroup reduction.radical)
    (P : Sylow 2 (Ltilde reduction.radical (alpha reduction.radical)))
    (hY : Y.map (embedS reduction.radical) =
      componentSylowSeed reduction.radical (alpha reduction.radical) P)
    (hn : Q reduction.radical (beta reduction.radical) ≤
      normalizer (Y.map (embedS reduction.radical) : Set (FreeAmalgam reduction.radical)))
    (hbad : ¬ ⁅sourceStarAlpha reduction.radical Y,Ltilde reduction.radical (alpha reduction.radical)⁆ ≤
      Z reduction.radical (alpha reduction.radical)) :
    ∃ u t : Vertex reduction.radical, ∃ P' : Sylow 2 (Ltilde reduction.radical u),
      color reduction.radical u = false ∧ Adjacent reduction.radical (alpha reduction.radical) t ∧
      Adjacent reduction.radical u t ∧
      Q reduction.radical t ≤ normalizer
        (componentSylowSeed reduction.radical u P' : Set (FreeAmalgam reduction.radical)) ∧
      componentSylowSeed reduction.radical u P' ≤ sourceStarAlpha reduction.radical Y ∧
      ¬ Z reduction.radical z ≤ normalizer
        ((componentSylowSeed reduction.radical u P' ⊔ Z reduction.radical (alpha reduction.radical) :
          Subgroup (FreeAmalgam reduction.radical)) : Set _) ∧
      ¬ componentSylowSeed reduction.radical u P' ≤ centralizer
        ((Z reduction.radical z ⊓ Q reduction.radical (alpha reduction.radical) :
          Subgroup (FreeAmalgam reduction.radical)) : Set _) := by
  obtain ⟨u,t,P',hu,hat,hut,hn',hs,he⟩ :=
    input.replacement_bad_star_critical_seed reduction geometry hb path Y P hY hn hbad
  refine ⟨u,t,P',hu,hat,hut,hn',hs,he,?_⟩
  have hYZ := hs.trans (input.replacement_sourceStarAlpha_le_critical_endpoint_stabilizer
    reduction geometry hb path Y P hY hn)
  have hYQ := hs.trans (input.replacement_sourceStarAlpha_le_own_core
    reduction geometry hb Y P hY hn)
  have hindex := input.replacement_seed_actor_centralizer_index_ge_field reduction path hb
    (componentSylowSeed reduction.radical u P') hYZ hYQ he
    (componentSylowSeed reduction.radical u P') le_rfl hYZ
  intro hfix
  have hi := relIndex_eq_one.mpr (le_centralizer_iff.mp hfix)
  rw [hi,input.field_card] at hindex
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) input.nonbinary
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
