module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Saturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalCore

/-!
# The original marked-star contradiction branch

A Sylow image of the original radical in the marked component quotient makes
the original radical itself Sylow in the ambient group: quotient-kernel
containment lifts equality of the component intersections, and H = K R then
lifts equality of the full subgroups.

If the literal star cut loses marked image, one holomorph conjugate of the
actual source seed is moved by the original component--radical intersection.
Transport identifies it with a full Sylow seed at a neighbor of beta. Its
normalization, full order bound and original-core containment are retained.
The final source application either supplies the actual saturated star pair
or selects this moved seed together with the full-core premises from (3.6).

Source: Meierfrankenfeld--Stellmacher (1993), opening of (3.7), printed p.872.
The printed actor is L-tilde-alpha intersect S, and delta is a neighbor of
beta; delta is not asserted to be critical. The decomposition of the moved
seed into two normal factors of order at most q, and the subsequent dual
full-core argument, are not established here. In particular this reduction
does not assert marked preservation, n = 2 or the final block classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] in
/-- The Sylow alternative in the marked component is exactly the
Sylow alternative for the full original radical, including its outer action. -/
theorem original_sylow_iff_marked_sylow :
    (∃ S : Sylow 2 H, (S : Subgroup H) = R) ↔
      ∃ P : Sylow 2 (Matrix.symplecticGroup (Fin 2) F),
        (P : Subgroup _) = (R.subgroupOf K).map (componentProjection h) := by
  let := h.component_normal
  constructor
  · rintro ⟨S,hS⟩
    let P := componentSylow K S
    refine ⟨P.mapSurjective (componentProjection_surjective h),?_⟩
    rw [Sylow.coe_mapSurjective,componentSylow_coe,hS]
  · rintro ⟨P,hP⟩
    obtain ⟨S,hRS,_⟩ := h.exists_normalizing_sylow
    have hkR : (componentProjection h).ker ≤ R.subgroupOf K := by
      rw [componentProjection_kernel,pCore_subnormal_eq_comap 2 h.component_normal.isSubnormal]
      exact fun x hx => h.radical.twoCore_le hx
    have he : (S : Subgroup H).subgroupOf K = R.subgroupOf K := by
      have hmap : ((S : Subgroup H).subgroupOf K).map (componentProjection h) =
          (R.subgroupOf K).map (componentProjection h) := by
        rw [←hP]
        apply P.is_maximal'
        · exact (S.isPGroup'.comap_subtype).map _
        · rw [hP]
          exact map_mono (comap_mono hRS)
      have hkS : (componentProjection h).ker ≤ (S : Subgroup H).subgroupOf K :=
        fun x hx => hRS (hkR hx)
      have he := congrArg (fun A => A.comap (componentProjection h)) hmap
      rwa [comap_map_eq_self hkS,comap_map_eq_self hkR] at he
    refine ⟨S,le_antisymm ?_ hRS⟩
    intro x hx
    obtain ⟨k,hk,r,hr,hkr⟩ := h.product x
    have hkS : k ∈ (S : Subgroup H) := by
      have hh := S.mul_mem hx (S.inv_mem (hRS hr))
      rwa [←hkr,mul_inv_cancel_right] at hh
    have hkR' : k ∈ R := he.le (show (⟨k,hk⟩ : K) ∈ (S : Subgroup H).subgroupOf K from hkS)
    rw [←hkr]
    exact R.mul_mem hkR' hr

omit [Finite F] [CharP F 2] in
private theorem marked_image_eq_of_graph_centralizes
    (Y : Subgroup R)
    (hc : (starSpan R Y).map (embedS R) ≤ centralizer
      (Ltilde R (alpha R) ⊓ Q R (beta R) : Set (FreeAmalgam R))) :
    (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) = (R.subgroupOf K).map (componentProjection h) := by
  suffices he : ((starCentralizer R Y).map R.subtype).subgroupOf K = R.subgroupOf K by
    rw [he]
  apply le_antisymm (comap_mono (map_subtype_le _))
  intro x hx
  change (x : H) ∈ (starCentralizer R Y).map R.subtype
  rw [starCentralizer_map]
  refine ⟨hx,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  apply embedM_injective R
  have hxL : embedM R (x : H) ∈ Ltilde R (alpha R) := by
    rw [Ltilde_alpha,h.residual_eq]
    exact mem_map_of_mem _ x.property
  have hxQ : embedM R (x : H) ∈ Q R (beta R) := by
    rw [Q_beta]
    exact mem_map_of_mem _ hx
  have he := hc (mem_map_of_mem (embedS R) hy) _ ⟨hxL,hxQ⟩
  have hval : embedM R (y : H) = embedS R y :=
    DFunLike.congr_fun (embedM_comp_subtype R) y
  change embedM R ((y : H) * (x : H)) = embedM R ((x : H) * (y : H))
  rw [map_mul,map_mul,hval]
  exact he.symm

omit [Finite F] [CharP F 2] in
/-- A lost marked image is witnessed on one actual holomorph conjugate of
the seed; the attached central omega layer cannot witness it. -/
theorem exists_moved_holomorph_seed_of_marked_image_ne
    (Y : Subgroup R)
    (hbad : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) ≠ (R.subgroupOf K).map (componentProjection h)) :
    ∃ k : Hbar R, ⁅(Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom,
      Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ := by
  classical
  by_contra! hall
  apply hbad
  apply marked_image_eq_of_graph_centralizes h Y
  have hs : (starSpan R Y).map (embedS R) =
      (⨆ k : Hbar R, (Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⊔ Z R (beta R) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
  rw [hs]
  apply sup_le
  · exact iSup_le fun k => commutator_eq_bot_iff_le_centralizer.mp (hall k)
  · apply (show Z R (beta R) ≤ centralizer (Q R (beta R) : Set (FreeAmalgam R)) from ?_).trans
      (centralizer_le inf_le_right)
    intro z hz
    rw [Z,if_neg (by change ¬ true = false; decide)] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2

/-- Failure of literal marked preservation selects a moved full Sylow seed
at a neighbor of the original holomorph vertex. -/
theorem exists_moved_neighbor_seed_of_marked_image_ne
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hbad : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) ≠ (R.subgroupOf K).map (componentProjection h)) :
    ∃ δ : Vertex R, ∃ Pδ : Sylow 2 (Ltilde R δ),
      color R δ = false ∧ Adjacent R δ (beta R) ∧
      componentSylowSeed R δ Pδ ≤ (starSpan R Y).map (embedS R) ∧
      componentSylowSeed R δ Pδ ≤ Q R (alpha R) ∧
      Q R (beta R) ≤ normalizer (componentSylowSeed R δ Pδ : Set (FreeAmalgam R)) ∧
      Nat.card (componentSylowSeed R δ Pδ) ≤ Nat.card F ^ 2 ∧
      ⁅componentSylowSeed R δ Pδ,Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ := by
  obtain ⟨k,hk⟩ := exists_moved_holomorph_seed_of_marked_image_ne h Y hbad
  obtain ⟨Pδ,hPδ⟩ := exists_componentSylowSeed_act R (alpha R) P (k : FreeAmalgam R)⁻¹
  simp only [inv_inv] at hPδ
  have hkb : (k : FreeAmalgam R) ∈ stabilizer R (beta R) := by
    simpa only [beta,stabilizer_h_base] using k.property
  have hfix : act R (k : FreeAmalgam R)⁻¹ (beta R) = beta R :=
    (stabilizer R (beta R)).inv_mem hkb
  have hnδ := map_seed_normalized_at_act R _ hn (k : FreeAmalgam R)⁻¹
  simp only [hfix,inv_inv,hY,←hPδ] at hnδ
  have hs' : componentSylowSeed R _ Pδ ≤ (starSpan R Y).map (embedS R) := by
    have hs : (starSpan R Y).map (embedS R) =
        (⨆ k : Hbar R, (Y.map (embedS R)).map
          (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⊔ Z R (beta R) := by
      simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
    rw [hs,hPδ,←hY]
    exact (le_iSup (fun k : Hbar R => (Y.map (embedS R)).map
      (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) k).trans le_sup_left
  have hδ : color R (act R (k : FreeAmalgam R)⁻¹ (alpha R)) = false := by
    rw [action_preserves_color]
    rfl
  obtain ⟨_,hadj⟩ := transported_seed_edges R (1 : Mbar R) k
  simp only [OneMemClass.coe_one,inv_one,act_one] at hadj
  refine ⟨_,Pδ,hδ,hadj,hs',?_,hnδ,componentSylowSeed_card_le h hδ Pδ,?_⟩
  · apply hs'.trans
    apply h.original_starSpan_le_core_of_distance geometry hb Y P hY hn rfl
    have hd : (cosetGraph R).dist (beta R) (alpha R) = 1 := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (base_adjacent R))
    have heven := geometry.even (alpha R) rfl
    rw [geometry.distance_constant _ rfl] at heven
    change Even (geometry.b R) at heven
    obtain ⟨m,hm⟩ := heven
    omega
  · rwa [hPδ,←hY]

/-- Apply the source seed construction and the full original-core comparison.
The remaining branch is an actual moved neighbor seed, with no replacement
of the original radical and no assumption on the original critical distance. -/
theorem exists_source_star_saturation_or_moved_seed
    (d : CharacteristicReduction K R) (g : Geometry d.radical)
    (hb : g.b d.radical = 2) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      ((let Tstar := (starCentralizer R Y).map R.subtype
        let Mstar := K ⊔ Tstar
        Tstar.subgroupOf Mstar = R.subgroupOf Mstar ∧
          (normalizer (Tstar.subgroupOf Mstar : Set Mstar)).pCoreIn 2 =
            Tstar.subgroupOf Mstar) ∨
        ∃ δ : Vertex R, ∃ Pδ : Sylow 2 (Ltilde R δ),
          color R δ = false ∧ Adjacent R δ (beta R) ∧
          componentSylowSeed R δ Pδ ≤ (starSpan R Y).map (embedS R) ∧
          componentSylowSeed R δ Pδ ≤ Q R (alpha R) ∧
          Q R (beta R) ≤ normalizer (componentSylowSeed R δ Pδ : Set (FreeAmalgam R)) ∧
          Nat.card (componentSylowSeed R δ Pδ) ≤ Nat.card F ^ 2 ∧
          ⁅componentSylowSeed R δ Pδ,Ltilde R (alpha R) ⊓ Q R (beta R)⁆ ≠ ⊥ ∧
          ⁅componentSylowSeed R δ Pδ,Q R (alpha R)⁆ ≤ fixedCore R (alpha R) ∧
          (∀ a : Vertex R, color R a = false →
            ⁅Q R a,Ltilde R a⁆ = U R a ∧
              (frattini (Q R a)).map (Q R a).subtype ≤ fixedCore R a) ∧
          ((∃ S : Sylow 2 (Matrix.symplecticGroup (Fin 2) F),
            (S : Subgroup _) = (R.subgroupOf K).map (componentProjection h)) →
            ∃ S : Sylow 2 H, (S : Subgroup H) = R)) := by
  classical
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  obtain ⟨P,Y,hY,hn,_⟩ := exists_source_star_reduction h
  refine ⟨P,Y,hY,hn,?_⟩
  by_cases hm : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) = (R.subgroupOf K).map (componentProjection h)
  · exact Or.inl (star_radical_saturated_of_marked_image_eq h geometry hpos P Y hY hn hm)
  · obtain ⟨δ,Pδ,hδ,hadj,hs,hQ,hnδ,hcard,hmove⟩ :=
      exists_moved_neighbor_seed_of_marked_image_ne h geometry hpos P Y hY hn hm
    refine Or.inr ⟨δ,Pδ,hδ,hadj,hs,hQ,hnδ,hcard,hmove,?_,
      fun a ha => original_core_source_of_distance_two_replacement h d g hb ha,
      (original_sylow_iff_marked_sylow h).mpr⟩
    obtain ⟨z,path,hfirst⟩ := exists_original_critical_path_through_beta geometry hpos
    have hstar : (starSpan R Y).map (embedS R) ≤ sourceStarAlpha R Y := by
      have hh := (sourceStarAlpha_le_iff R Y (sourceStarAlpha R Y)).mp le_rfl (1 : Mbar R)
      have hid : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        change 1*x*1⁻¹=x
        simp
      simpa only [OneMemClass.coe_one,hid,Subgroup.map_id] using hh
    exact (commutator_mono (hs.trans hstar) le_rfl).trans
      (h.original_sourceStarAlpha_core_displacement geometry hpos path hfirst Y P hY hn)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
