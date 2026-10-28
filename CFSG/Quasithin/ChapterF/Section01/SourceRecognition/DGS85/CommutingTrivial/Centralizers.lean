module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity

/-!
# Neighborhood centralizers and the source core intersections

Rank-one Borel maximality lifts through the starred supplement. If an
adjacent endpoint normalizes the nonzero center span beyond the edge
group, both endpoints normalize it, contradicting faithfulness. Thus the
centralizer of the whole neighboring span lies in the edge group. Relative
normality puts it in the full local permutation kernel U, proving 9.1(d).

For any two-subgroup of that stabilizer, the earlier 6.2(d) Sylow property
places its span centralizer in Q. The Chapter 9 trivial-displacement
hypothesis gives the reverse containment. This proves the precise
centralizer intersection used in 9.3, without identifying Q with U or
assuming generation for the later central quotient module.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 3.2(c), 6.2(d), 9.1(d), 9.3, printed pp.74,119,141--142.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- An adjacent endpoint normalizes the nonzero base center exactly through the whole Borel. -/
theorem base_neighbor_normalizer (h : LocallyRankOneTriple P B) (i : Bool) :
    family P (!i) ⊓ normalizer (Z (family P) (base (family P) i) : Set G) = B := by
  let := finite_endpoints h
  let F := family P
  have hi : stabilizer F (base F i) = F i := Subgroup.CosetGeometry.stabilizer_base F i
  have hinf : F i ⊓ F (!i) = B := by
    cases i
    · exact h.intersection
    · exact (inf_comm _ _).trans h.intersection
  have hgen : F i ⊔ F (!i) = ⊤ := by
    cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  have hn : F i ≤ normalizer (Z F (base F i) : Set G) := by
    rw [← hi]
    exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F _)).mp (Z_normal F _)
  have hB : B ≤ F (!i) ⊓ normalizer (Z F (base F i) : Set G) := by
    rw [← hinf]
    exact le_inf inf_le_right (inf_le_left.trans hn)
  have hd : Nonempty (LocalRankOneData (F (!i)) B) := by
    cases i
    · exact h.local_data 1
    · exact h.local_data 0
  rcases source_borel_maximal (Classical.choice hd) _ hB inf_le_left with he | he
  · exact he
  have hn' : F (!i) ≤ normalizer (Z F (base F i) : Set G) := by
    rw [← he]
    exact inf_le_right
  have hnormal : (Z F (base F i)).Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp (hgen ▸ sup_le hn hn'))
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZB : Z F (base F i) ≤ B := by
    have hs := source_Z_Q_U h (base F i)
    have hZU : Z F (base F i) ≤ U F (base F i) := by
      intro x hx
      exact hs.2 ((mem_omegaCenterIn_iff _ _).mp (hs.1 hx)).1
    have hh := hZU.trans (ballKernel_one_le_edge F hadj)
    simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base, hinf] using hh
  exact (base_Z_ne_bot h i (h.faithful _ hnormal hZB)).elim

private theorem base_neighborhood_centralizer_le_U (h : LocallyRankOneTriple P B) (i : Bool) :
    family P i ⊓ centralizer (V (family P) (base (family P) i) 1 : Set G) ≤
      U (family P) (base (family P) i) := by
  let := finite_endpoints h
  let F := family P
  let C := F i ⊓ centralizer (V F (base F i) 1 : Set G)
  have hi : stabilizer F (base F i) = F i := Subgroup.CosetGeometry.stabilizer_base F i
  have hn : F i ≤ normalizer (C : Set G) :=
    (le_inf (F i).le_normalizer
      ((hi ▸ stabilizer_normalizes_V F (base F i) 1).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf (F i)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZV : Z F (base F (!i)) ≤ V F (base F i) 1 :=
    le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hadj)) le_rfl)
  have hCB : C ≤ B := by
    have he := base_neighbor_normalizer h (!i)
    simp only [Bool.not_not] at he
    rw [← he]
    exact le_inf inf_le_left (inf_le_right.trans
      ((centralizer_le hZV).trans (Subgroup.centralizer_le_normalizer _)))
  have hcore : C.subgroupOf (F i) ≤ (B.subgroupOf (F i)).normalCore :=
    normal_le_normalCore.mpr (fun _ hx => hCB hx)
  have hU : (U F (base F i)).subgroupOf (F i) =
      (B.subgroupOf (F i)).normalCore := by
    rw [U, base_ballKernel_one]
    change ((P 0 ⊓ P 1).subgroupOf (F i)).normalCore = _
    rw [h.intersection]
  rw [← hU] at hcore
  intro x hx
  exact hcore (show (⟨x, hx.1⟩ : F i) ∈ C.subgroupOf (F i) from hx)

/-- DGS 9.1(d): the neighborhood centralizer fixes every neighbor in the original graph. -/
theorem neighborhood_centralizer_le_U (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    stabilizer (family P) v ⊓ centralizer (V (family P) v 1 : Set G) ≤ U (family P) v := by
  let := finite_endpoints h
  let F := family P
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have hinv : g⁻¹ • v = base F v.type := by rw [← hg, inv_smul_smul]; rfl
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hm : (stabilizer F v ⊓ centralizer (V F v 1 : Set G)).map f ≤
      stabilizer F (base F v.type) ⊓ centralizer (V F (base F v.type) 1 : Set G) := by
    apply le_inf
    · rw [← hinv, stabilizer_translate]
      exact map_mono inf_le_left
    · have hc := (map_mono (f := f) (show stabilizer F v ⊓ centralizer (V F v 1 : Set G) ≤
          centralizer (V F v 1 : Set G) from inf_le_right)).trans
          (map_centralizer_le_centralizer_image _ f)
      change _ ≤ centralizer ((V F v 1).map f : Set G) at hc
      rw [← V_translate, hinv] at hc
      exact hc
  have hb : stabilizer F (base F v.type) ⊓ centralizer (V F (base F v.type) 1 : Set G) ≤
      U F (base F v.type) := by
    simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base] using
      base_neighborhood_centralizer_le_U h v.type
  have hh := hm.trans hb
  rw [← hinv, U_translate] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh


/-- For a two-actor, 6.2(d) and the trivial-displacement hypothesis identify the centralizer with the core intersection. -/
theorem two_actor_centralizer_eq_core_inter (h : LocallyRankOneTriple P B)
    (v : Vertex (family P))
    (hS : ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAv : A ≤ stabilizer (family P) v)
    (hc : ⁅A ⊓ Q (family P) v, V (family P) v 1⁆ = ⊥) :
    A ⊓ centralizer (V (family P) v 1 : Set G) = A ⊓ Q (family P) v := by
  let := finite_endpoints h
  apply le_antisymm
  · apply le_inf inf_le_left
    apply two_subgroup_le_Q (family P) v hS (hA.to_le inf_le_left)
    exact (inf_le_inf_right _ hAv).trans (neighborhood_centralizer_le_U h v)
  · exact le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The literal neighboring-span centralizer identity used in the first case of 9.3. -/
theorem neighbor_span_centralizer_eq_core_inter (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v w : Vertex (family P)) (hb : 1 < b (family P))
    (hd : (graph (family P)).dist v w + 1 ≤ b (family P))
    (hc : ⁅V (family P) v 1 ⊓ Q (family P) w, V (family P) w 1⁆ = ⊥) :
    V (family P) v 1 ⊓ centralizer (V (family P) w 1 : Set G) =
      V (family P) v 1 ⊓ Q (family P) w := by
  let := finite_endpoints h
  have hp : IsPGroup 2 (V (family P) v 1) :=
    (isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le
      (V_le_Q (family P) h.generate (fun x => (source_Z_Q_U h x).1) hS v hb)
  exact two_actor_centralizer_eq_core_inter h w (hS w) _ hp
    (V_le_stabilizer (family P) h.generate v w hd) hc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
