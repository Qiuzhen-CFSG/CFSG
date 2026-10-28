module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SingularKernel
public import Theory.GroupAction.CubicTree.WeissEven
public import Theory.GroupTheory.Amalgam.ParabolicRecognition

/-!
# Weiss's even bound in the original primitive cubic action

The source Sylow hypothesis makes every edge stabilizer a finite two-group.
Together with the actual translation track this discharges the geometric and
group-theoretic hypotheses of Weiss's even bound. The regular arc action is
the literal action in the rank-two coset graph; its pointwise freeness is the
conclusion of Goldschmidt's even singularity branch.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.3), p.393;
Weiss, *Über lokal s-reguläre Graphen* (1976), pp.124--125.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.finite_edgeStabilizer (h : CubicTreeAction F)
    (v w : RankTwo.Vertex F) : Finite (WeissEven.edgeStabilizer G v w) := by
  let : ∀ i, Finite (F i) := h.finite
  exact Finite.of_injective
    (Subgroup.inclusion (show WeissEven.edgeStabilizer G v w ≤ RankTwo.stabilizer F v from
      inf_le_left)) (Subgroup.inclusion_injective _)

theorem CubicTreeAction.edgeStabilizer_isPGroup (h : CubicTreeAction F)
    {v w : RankTwo.Vertex F} (hvw : (RankTwo.graph F).Adj v w) :
    IsPGroup 2 (WeissEven.edgeStabilizer G v w) := by
  have hbase : WeissEven.edgeStabilizer G (RankTwo.base F false)
      (RankTwo.base F true) = F false ⊓ F true := by
    ext a
    simp only [WeissEven.edgeStabilizer, RankTwo.base, stabilizer_base, mem_inf]
  have htwo : IsPGroup 2 (WeissEven.edgeStabilizer G
      (RankTwo.base F false) (RankTwo.base F true)) := by
    rw [hbase]
    exact h.primitive.sylow.isPGroup
  obtain ⟨g,hg⟩ := RankTwo.edge_transitive F hvw
  change IsPGroup 2 (WeissEven.edgeStabilizer G v w)
  have he0 : v = g • RankTwo.base F false ∨ v = g • RankTwo.base F true := by
    have hv := (Set.ext_iff.mp hg v).mp (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv
  have he1 : w = g • RankTwo.base F false ∨ w = g • RankTwo.base F true := by
    have hw := (Set.ext_iff.mp hg w).mp (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
  rcases he0 with h0 | h0 <;> rcases he1 with h1 | h1
  · exfalso; subst v; subst w; exact hvw.1 rfl
  · subst v; subst w
    rw [WeissEven.edgeStabilizer, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← Subgroup.map_inf _ _ _ (fun x y hxy => (MulAut.conj g).injective hxy)]
    exact htwo.map _
  · subst v; subst w
    rw [WeissEven.edgeStabilizer, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj, inf_comm,
      ← Subgroup.map_inf _ _ _ (fun x y hxy => (MulAut.conj g).injective hxy)]
    exact htwo.map _
  · exfalso; subst v; subst w; exact hvw.1 rfl

/-- The even locally regular case has length at most four. All finite-group,
tree and cubic hypotheses are inherited from the original source action. -/
theorem CubicTreeAction.even_arc_length_le_four (h : CubicTreeAction F)
    (s : ℕ) (heven : Even s)
    (hfree : WeissEven.ArcFree (Γ := RankTwo.graph F) (G := G) s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p) : s ≤ 4 := by
  obtain ⟨t,_,_⟩ := h.exists_track
  exact WeissEven.even_arc_length_le_four h.tree trackGraphAction (h.card_neighbor)
    t.toLine s heven hfree hshort (fun v w _ => h.finite_edgeStabilizer v w)
    (fun _ _ hvw => h.edgeStabilizer_isPGroup hvw)

/-- Local arc regularity counts the original vertex stabilizer, using the
actual nonbacktracking action and the already proved cubic path count. -/
theorem CubicTreeAction.card_stabilizer_of_local_arc_regular (h : CubicTreeAction F)
    {s : ℕ} (hs : 0 < s)
    (hfree : WeissEven.ArcFree (Γ := RankTwo.graph F) (G := G) s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F)
      (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    (v : RankTwo.Vertex F) : Nat.card (RankTwo.stabilizer F v) = 3*2^(s-1) := by
  classical
  let H := RankTwo.stabilizer F v
  let P := {p : BasedWalk (RankTwo.graph F) s v // p.Nonbacktracking}
  let : MulAction H P := RankTwo.nonbacktrackingAction F s v
  have hcard : Nat.card P = 3*2^(s-1) := by
    have he : (s-1)+1 = s := by omega
    have hc := h.card_nonbacktracking (s-1) v
    rw [he] at hc
    exact hc
  have hne : Nonempty P := (Nat.card_pos_iff.mp (by rw [hcard]; positivity)).1
  obtain ⟨p⟩ := hne
  have htrans := (RankTwo.rootPathTransitive_iff F s v).1
    (rootPathTransitive_of_short_rightRegular trackGraphAction s hshort v s le_rfl)
  have hsur : Function.Surjective (fun a : H => a • p) := by
    intro q
    exact htrans.exists_smul_eq p q
  have hinj : Function.Injective (fun a : H => a • p) := by
    intro a b he
    change a • p = b • p at he
    have hfixed : (b⁻¹*a) • p = p := by rw [mul_smul,he,inv_smul_smul]
    have hfixed' : (b⁻¹*a) • p.val = p.val := congrArg Subtype.val hfixed
    have hmem := (RankTwo.mem_pathStabilizer_iff F p.val (b⁻¹*a)).2 hfixed'
    have hab : ((b⁻¹*a:H):G) = 1 := hfree v p.val p.property _ hmem
    exact (inv_mul_eq_one.mp (Subtype.ext hab)).symm
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,hsur⟩)).trans hcard

private theorem arcFree_of_even
    (h : CubicTreeAction F) {s : ℕ} (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F)
      (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) :
    WeissEven.ArcFree (Γ := RankTwo.graph F) (G := G) s := by
  intro w q hq a ha
  have hbot := h.pathStabilizer_eq_bot_of_even hs heven hshort p hp hn le_rfl q hq
  apply Subgroup.mem_bot.mp
  rw [← hbot]
  exact ha

/-- The first even singularity length is at most four. Pointwise freeness is
discharged by the literal singular-kernel theorem, so this is the terminal
source bound rather than a conditional Weiss wrapper. -/
theorem CubicTreeAction.even_singularityIndex_le_four
    (h : CubicTreeAction F) {s : ℕ} (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F)
      (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) : s ≤ 4 := by
  have hfree := arcFree_of_even h hs heven hshort p hp hn
  exact h.even_arc_length_le_four s heven hfree hshort

/-- The original even singularity branch has vertex stabilizer order at most
24, exactly the numerical input used in Goldschmidt (4.3). -/
theorem CubicTreeAction.card_stabilizer_le_twentyFour_of_even
    (h : CubicTreeAction F) {s : ℕ} (hs : 0 < s) (heven : Even s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F)
      (q : BasedWalk (RankTwo.graph F) k v),
      k < s → q.Nonbacktracking → RightRegular (A := G) q)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (w : RankTwo.Vertex F) : Nat.card (RankTwo.stabilizer F w) ≤ 24 := by
  have hs4 := h.even_singularityIndex_le_four hs heven hshort p hp hn
  have hfree := arcFree_of_even h hs heven hshort p hp hn
  rw [h.card_stabilizer_of_local_arc_regular hs hfree hshort w]
  have hpow : 2^(s-1) ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- In the large-stabilizer branch of Goldschmidt (4.3), the first singularity
index is odd. Existence, minimality and the parity bound all come from the
original cubic tree action. -/
theorem CubicTreeAction.exists_odd_singularityIndex_of_large
    (h : CubicTreeAction F) (w : RankTwo.Vertex F)
    (hlarge : 24 < Nat.card (RankTwo.stabilizer F w)) :
    ∃ s : ℕ, 0 < s ∧ Odd s ∧
      (∀ (k : ℕ) (v : RankTwo.Vertex F) (q : BasedWalk (RankTwo.graph F) k v),
        k < s → q.Nonbacktracking → RightRegular (A := G) q) ∧
      ∃ (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) s v),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  obtain ⟨s,hs,hshort,v,p,hp,hn⟩ := h.exists_singularityIndex
  have hodd : Odd s := by
    rcases Nat.even_or_odd s with heven | hodd
    · have hbound := h.card_stabilizer_le_twentyFour_of_even hs heven hshort p hp hn w
      omega
    · exact hodd
  exact ⟨s,hs,hodd,hshort,v,p,hp,hn⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
