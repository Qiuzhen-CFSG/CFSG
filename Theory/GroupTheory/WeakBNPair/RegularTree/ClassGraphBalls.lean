module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraph
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Ball fixation on the actual graph quotient

Neighbor lifting supplies representatives in any chosen ball. Thus fixation
of a ball descends to the raw quotient. Conversely, separation at distance
two lifts fixation along walks for an element already fixing the center.
The exact subgroup identity retains this original stabilizer image; it does
not identify the full class stabilizer with that image.

Source: DGS, Groups and Graphs (1985), (3.6), pp.77--78. Used for the
midpoint symmetries of the natural b=1 source branch.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {X V : Type*} [Group X] [MulAction X V]
variable (Γ : SimpleGraph V) (r : Setoid V) (hr : Invariant (X := X) r)

/-- Pointwise fixation of a finite-radius ball in the original action. -/
def graphBallFixer (a : V) (k : ℕ) : Subgroup X :=
  fixingSubgroup X {b | Γ.edist a b ≤ (k : ℕ∞)}

/-- Pointwise fixation in the faithful permutation action of the same group quotient. -/
def classBallFixer (a : Quotient r) (k : ℕ) : Subgroup (X ⧸ quotientKernel r hr) :=
  (fixingSubgroup (Equiv.Perm (Quotient r))
    {b | (classGraph Γ r).edist a b ≤ (k : ℕ∞)}).comap
      (QuotientGroup.kerLift (quotientAction r hr))

@[simp] theorem mem_graphBallFixer (a : V) (k : ℕ) (g : X) :
    g ∈ graphBallFixer Γ a k ↔ ∀ b, Γ.edist a b ≤ (k : ℕ∞) → g • b=b :=
  mem_fixingSubgroup_iff X

@[simp] theorem mk_mem_classBallFixer (a : Quotient r) (k : ℕ) (g : X) :
    QuotientGroup.mk' (quotientKernel r hr) g ∈ classBallFixer Γ r hr a k ↔
      ∀ b, (classGraph Γ r).edist a b ≤ (k : ℕ∞) → quotientAction r hr g b=b := by
  change (QuotientGroup.kerLift (quotientAction r hr))
    (QuotientGroup.mk' (quotientKernel r hr) g) ∈ fixingSubgroup _ _ ↔ _
  rw [mem_fixingSubgroup_iff]
  rfl

variable {Γ r}

/-- Every class in a quotient ball has a representative in the ball about
any chosen representative of its center. -/
theorem classGraph_ball_representative (hlift : NeighborLifting Γ r)
    (a : V) (b : Quotient r) (k : ℕ)
    (hb : (classGraph Γ r).edist (Quotient.mk r a) b ≤ (k : ℕ∞)) :
    ∃ c, Quotient.mk r c=b ∧ Γ.edist a c ≤ (k : ℕ∞) := by
  obtain ⟨p,hp⟩ := exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hb)
  obtain ⟨c,q,hc,hlen,_⟩ := classGraph_walk_lift hlift p a rfl
  refine ⟨c,hc,q.edist_le.trans ?_⟩
  rw [hlen,hp]
  exact hb

/-- Ball fixation descends through the actual quotient, including all
representatives of the midpoint class. -/
theorem graphBallFixer_map_le (hlift : NeighborLifting Γ r) (a : V) (k : ℕ) :
    (graphBallFixer Γ a k).map (QuotientGroup.mk' (quotientKernel r hr)) ≤
      classBallFixer Γ r hr (Quotient.mk r a) k := by
  rintro _ ⟨g,hg,rfl⟩
  rw [mk_mem_classBallFixer]
  intro b hb
  obtain ⟨c,rfl,hc⟩ := classGraph_ball_representative hlift a b k hb
  rw [quotientAction_mk,(mem_graphBallFixer Γ a k g).mp hg c hc]

/-- Fixation of classes in a ball lifts when the acting element fixes its
actual center. Separation supplies uniqueness at each neighbor. -/
theorem classBallFixer_lift (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2<m)
    (a : V) (k : ℕ) (g : X) (ha : g • a=a)
    (hg : QuotientGroup.mk' (quotientKernel r hr) g ∈
      classBallFixer Γ r hr (Quotient.mk r a) k) :
    g ∈ graphBallFixer Γ a k := by
  rw [mem_graphBallFixer]
  intro b hb
  obtain ⟨p,hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hb)
  have hlen : p.length≤k := by exact_mod_cast hp.symm ▸ hb
  have hfix : ∀ i≤p.length, g • p.getVert i=p.getVert i := by
    intro i
    induction i with
    | zero => intro _; simpa only [getVert_zero] using ha
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hadj := p.adj_getVert_succ (by omega : i<p.length)
      have himg := hact g hadj
      rw [hprev] at himg
      have hrel : r (g • p.getVert (i+1)) (p.getVert (i+1)) := by
        apply Quotient.exact
        apply (mk_mem_classBallFixer Γ r hr (Quotient.mk r a) k g).mp hg
          (Quotient.mk r (p.getVert (i+1)))
        have hd := ((p.take (i+1)).map (classGraphMap hsep (by omega))).edist_le
        exact hd.trans (by
          rw [length_map,take_length]
          exact_mod_cast (min_le_right (i+1) p.length).trans hlen)
      apply hsep hrel
      have hd := hconn.dist_triangle (u := g • p.getVert (i+1))
        (v := p.getVert i) (w := p.getVert (i+1))
      rw [dist_eq_one_iff_adj.mpr himg.symm,dist_eq_one_iff_adj.mpr hadj] at hd
      omega
  simpa only [getVert_length] using hfix p.length le_rfl

/-- The ball fixer has exactly its original image inside the image of the
original center stabilizer. The full class stabilizer remains distinct. -/
theorem graphBallFixer_map_eq (hlift : NeighborLifting Γ r) (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2<m) (a : V) (k : ℕ) :
    (graphBallFixer Γ a k).map (QuotientGroup.mk' (quotientKernel r hr)) =
      classBallFixer Γ r hr (Quotient.mk r a) k ⊓
        (MulAction.stabilizer X a).map (QuotientGroup.mk' (quotientKernel r hr)) := by
  apply le_antisymm
  · refine le_inf (graphBallFixer_map_le hr hlift a k) (Subgroup.map_mono ?_)
    intro g hg
    exact (mem_graphBallFixer Γ a k g).mp hg a (by simp)
  · rintro _ ⟨hg,g,ha,rfl⟩
    exact Subgroup.mem_map_of_mem _ (classBallFixer_lift hr hconn hact hsep hm a k g ha hg)

end Theory.GroupTheory.WeakBNPair.RegularTree
