module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcIndexBounds
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.WeissEven
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths

/-!
# Radius-two kernels at a short singularity

The closed-star fixer is the embedded two-core of the original vertex
stabilizer: an incident edge stabilizer is a Sylow two-subgroup, and its
normal core is the two-core. A symmetric-three local quotient therefore
makes each one-edge arc regular.

For first singular length three, orient the center in the initial vertex
orbit of a singular arc. Conjugate three-arcs force the intersection of the
adjacent closed-star fixers to fix every neighboring closed star. This is
exactly the radius-two kernel at the chosen center. Two- and three-edge
path fixers give index at most two in each adjacent two-core, using the
same radius-two kernel for both indices.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.4),
printed p.393. The involution-selection and finite local-group argument
consume these identities separately; no finite ambient group is assumed.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupTheory
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The local two-core is the pointwise closed-star fixer in the original action. -/
theorem CubicTreeAction.ballKernel_one_eq_twoCore (h : CubicTreeAction F)
    (v : RankTwo.Vertex F) :
    RankTwo.ballKernel F v 1 =
      (pCore 2 (RankTwo.stabilizer F v)).map (RankTwo.stabilizer F v).subtype := by
  let : ∀ i, Finite (F i) := h.finite
  have hne : Nonempty ((RankTwo.graph F).neighborSet v) :=
    (Nat.card_pos_iff.mp (by rw [h.card_neighbor v]; decide)).1
  obtain ⟨⟨w, hvw⟩⟩ := hne
  let H := RankTwo.stabilizer F v
  let B := (RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w).subgroupOf H
  have hp : IsPGroup 2 B := (h.edgeStabilizer_isPGroup hvw).comap_subtype
  have hi : B.index = 3 := by
    change (RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w).relIndex
      (RankTwo.stabilizer F v) = 3
    rw [inf_comm]
    exact h.edge_vertex_relIndex hvw.symm
  let P : Sylow 2 H := hp.toSylow (by rw [hi]; decide)
  have he : B.normalCore = pCore 2 H := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hp.to_le B.normalCore_le⟩
    · exact normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal P)
  rw [RankTwo.ballKernel_one_eq_map_normalCore F hvw]
  exact congrArg (fun K : Subgroup H => K.map H.subtype) he

private theorem exists_neighbor_ne (h : CubicTreeAction F) (a b : RankTwo.Vertex F) :
    ∃ c, (RankTwo.graph F).Adj a c ∧ c ≠ b := by
  apply Set.exists_ne_of_one_lt_ncard
  change 1 < Nat.card ((RankTwo.graph F).neighborSet a)
  rw [h.card_neighbor a]
  decide

/-- For the first singular length three, the radius-two kernel at the
initial vertex orbit is the intersection of the adjacent local kernels. -/
theorem CubicTreeAction.ballKernel_two_eq_inf_of_singular_three
    (h : CubicTreeAction F)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < 3 → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 3 v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (ht : a.type = v.type) :
    RankTwo.ballKernel F a 2 = RankTwo.ballKernel F a 1 ⊓ RankTwo.ballKernel F b 1 := by
  apply le_antisymm
  · exact le_inf (RankTwo.ballKernel_antitone F a (by decide))
      (RankTwo.ballKernel_succ_le F hab 1)
  · intro g hg
    have hga : g • a = a := RankTwo.ballKernel_le_stabilizer F a 1 hg.1
    have hstar : ∀ c, (RankTwo.graph F).Adj a c → g ∈ RankTwo.ballKernel F c 1 := by
      intro c hac
      by_cases hcb : c = b
      · subst c
        exact hg.2
      obtain ⟨d, hbd, hda⟩ := exists_neighbor_ne h b a
      let q : BasedWalk (RankTwo.graph F) 3 d :=
        ⟨⟨b, hbd.symm⟩, ⟨⟨a, hab.symm⟩, ⟨⟨c, hac⟩, PUnit.unit⟩⟩⟩
      have hq : q.Nonbacktracking := ⟨hda.symm, hcb, trivial⟩
      have hdtype : d.type = v.type := by
        have h1 := hbd.1
        have h2 := hab.1
        have hdaType : d.type = a.type := by
          cases ha : a.type <;> cases hb : b.type <;> cases hd : d.type <;> simp_all
        exact hdaType.trans ht
      have hqn : ¬ RightRegular (A := G) q := by
        intro hr
        obtain ⟨u, hu⟩ := h.congruent_arcs 3 hshort le_rfl q p hq hp hdtype
        exact hn (rightRegular_of_conjugate trackGraphAction q p u hu hr)
      have hfix : ∀ y ∈ q.vertices, g • y = y := by
        change ∀ y ∈ [d, b, a, c], g • y = y
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        exact ⟨hg.2 d ((RankTwo.mem_ball_one F b d).2 (Or.inl hbd)),
          RankTwo.ballKernel_le_stabilizer F b 1 hg.2, hga,
          hg.1 c ((RankTwo.mem_ball_one F a c).2 (Or.inl hac))⟩
      intro z hz
      rcases (RankTwo.mem_ball_one F c z).1 hz with hcz | rfl
      · by_cases hza : z = a
        · simpa only [hza] using hga
        · exact fixes_forward_of_not_rightRegular trackGraphAction q
            (h.card_neighbor c) hqn g hfix ⟨hcz, hza⟩
      · exact hg.1 c ((RankTwo.mem_ball_one F a c).2 (Or.inl hac))
    intro z hz
    by_cases haz : a = z
    · simpa only [← haz] using hga
    obtain ⟨c, hac, hdist⟩ := RankTwo.exists_predecessor F h.generated z a (Ne.symm haz)
    have hcz : z ∈ RankTwo.ball F c 1 := by
      apply (RankTwo.mem_ball_iff F h.generated c z 1).2
      have hz' := (RankTwo.mem_ball_iff F h.generated a z 2).1 hz
      rw [SimpleGraph.dist_comm (u := z) (v := a),
        SimpleGraph.dist_comm (u := z) (v := c)] at hdist
      omega
    exact hstar c hac z hcz

/-- A symmetric-three local quotient makes every incident one-arc regular. -/
theorem CubicTreeAction.one_arc_regular_of_symmetricThree (h : CubicTreeAction F)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 1 v)
    (he : Nonempty (((RankTwo.stabilizer F p.endpoint) ⧸
      pCore 2 (RankTwo.stabilizer F p.endpoint)) ≃* Equiv.Perm (Fin 3))) :
    RightRegular (A := G) p := by
  obtain ⟨e⟩ := he
  by_contra hn
  let b : RankTwo.Vertex F := p.1
  have hvb : (RankTwo.graph F).Adj v b := p.1.property
  have hb : p.endpoint = b := by cases p with | mk b q => cases q; rfl
  have hpen : p.penultimate = v := rfl
  have hvert : p.vertices = [v, b] := by cases p with | mk b q => cases q; rfl
  have hK : RankTwo.ballKernel F b 1 =
      RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F b := by
    apply le_antisymm
    · simpa only [inf_comm] using RankTwo.ballKernel_one_le_edge F hvb.symm
    · intro g hg z hz
      change g • v = v ∧ g • b = b at hg
      rcases (RankTwo.mem_ball_one F b z).1 hz with hbz | rfl
      · by_cases hzv : z = v
        · simpa only [hzv] using hg.1
        · apply fixes_forward_of_not_rightRegular trackGraphAction p
            (h.card_neighbor p.endpoint) hn g
          · simpa only [hvert, List.mem_cons, List.not_mem_nil, or_false,
              forall_eq_or_imp, forall_eq] using hg
          · simpa only [Forward, hb, hpen] using And.intro hbz hzv
      · exact hg.2
  have hcore : (RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F b).subgroupOf
      (RankTwo.stabilizer F b) = pCore 2 (RankTwo.stabilizer F b) := by
    rw [← hK, h.ballKernel_one_eq_twoCore]
    exact Subgroup.comap_map_eq_self_of_injective (RankTwo.stabilizer F b).subtype_injective _
  have hi := h.edge_vertex_relIndex hvb
  change ((RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F b).subgroupOf
    (RankTwo.stabilizer F b)).index = 3 at hi
  rw [hcore] at hi
  have hi6 : (pCore 2 (RankTwo.stabilizer F b)).index = 6 := by
    have hi := SymmetricThreeTwoCore.core_index e
    change (pCore 2 (RankTwo.stabilizer F p.endpoint)).index = 6 at hi
    rw [hb] at hi
    exact hi
  omega

/-- Adjacent closed-star fixers meet with index at most two in each. -/
theorem CubicTreeAction.ballKernel_one_inf_relIndex_le_two (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) :
    (RankTwo.ballKernel F a 1 ⊓ RankTwo.ballKernel F b 1).relIndex
      (RankTwo.ballKernel F a 1) ≤ 2 := by
  obtain ⟨c, hac, hcb⟩ := exists_neighbor_ne h a b
  obtain ⟨d, hbd, hda⟩ := exists_neighbor_ne h b a
  let p : BasedWalk (RankTwo.graph F) 2 c :=
    ⟨⟨a, hac.symm⟩, ⟨⟨b, hab⟩, PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hcb.symm, trivial⟩
  have hd : Forward p d := ⟨hbd, hda⟩
  have hi := h.pathStabilizer_snoc_index_le_two p hd
  have h2 := RankTwo.pathStabilizer_two_eq_ballKernel_one F p hp (h.card_neighbor a)
  have h3 := RankTwo.pathStabilizer_three_eq_ballKernel_one_inf F
    (p.snoc (forward_adj p hd)) ((forward_iff_snoc_nonbacktracking p hp _).1 hd)
    (h.card_neighbor a) (h.card_neighbor b)
  change RankTwo.pathStabilizer F p = RankTwo.ballKernel F a 1 at h2
  change RankTwo.pathStabilizer F (p.snoc (forward_adj p hd)) =
    RankTwo.ballKernel F a 1 ⊓ RankTwo.ballKernel F b 1 at h3
  rwa [h2, h3] at hi

/-- Goldschmidt (4.4)'s two indices use the same radius-two kernel. The
center is in the initial vertex orbit of the singular three-arc. -/
theorem CubicTreeAction.short_singularity_core_kernels (h : CubicTreeAction F)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < 3 → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 3 v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (ht : a.type = v.type) :
    RankTwo.ballKernel F a 2 =
        (pCore 2 (RankTwo.stabilizer F a)).map (RankTwo.stabilizer F a).subtype ⊓
          (pCore 2 (RankTwo.stabilizer F b)).map (RankTwo.stabilizer F b).subtype ∧
      (RankTwo.ballKernel F a 2).relIndex
        ((pCore 2 (RankTwo.stabilizer F a)).map (RankTwo.stabilizer F a).subtype) ≤ 2 ∧
      (RankTwo.ballKernel F a 2).relIndex
        ((pCore 2 (RankTwo.stabilizer F b)).map (RankTwo.stabilizer F b).subtype) ≤ 2 := by
  have he := h.ballKernel_two_eq_inf_of_singular_three hshort p hp hn hab ht
  rw [← h.ballKernel_one_eq_twoCore a, ← h.ballKernel_one_eq_twoCore b]
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact h.ballKernel_one_inf_relIndex_le_two hab
  · rw [he, inf_comm]
    exact h.ballKernel_one_inf_relIndex_le_two hab.symm

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
