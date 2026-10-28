module
public import Theory.GroupAction.SymplecticRankThree.Parameters
public import Theory.GroupAction.SymplecticRankThree.Kernel
public import Theory.GroupAction.SwappedOrbital.Connected

/-!
# The elementary geometric conclusion of Higman's condition (i)

Starting with a faithful primitive action, its actual three suborbits, and
a self-paired neighbor orbit of length q(q+1), this module constructs the
closed-neighborhood polarity design and proves that every line has q+1
points. The degree is q³+q²+q+1 and the pointwise neighbor-block kernel
has at least q elements. Connectivity proves the positive intersection
parameter; double counting and the kernel argument supply the rest.

All statements include q=2. The remaining step from this design to a
coordinatized projective three-space, and then to symplectic recognition,
is not supplied or assumed here.

Source: D. G. Higman, *Finite permutation groups of rank 3*, Math. Z. 86
(1964), Lemmas 5,8,10 and Theorem 2(i), printed pp.148,153–154.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree
open MulAction
variable {G Ω : Type*} [Group G] [Fintype Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] [IsPreprimitive G Ω]

/-- The elementary condition-(i) chain, from the actual rank-three orbits to
incidence and all line sizes. Projective reconstruction is not a premise or
conclusion of this theorem. -/
theorem condition_i_lines {q : ℕ} (hq : 2 ≤ q)
    (a b c : Ω) (hab : a ≠ b) (t : G) (hta : t • a = b) (htb : t • b = a)
    (hc : orbit (stabilizer G a) c = (insert a (orbit (stabilizer G a) b))ᶜ)
    (hdegree : Nat.card Ω = q^3+q^2+q+1)
    (hsubdegree : Nat.card (orbit (stabilizer G a) b) = q*(q+1))
    (hk : q ≤ Nat.card (fixingSubgroup G (insert a (orbit (stabilizer G a) b)))) :
    ∃ D : PolarityDesign Ω q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (SwappedOrbital.graph a b hab t hta htb).Adj x y) ∧
      D.block a = insert a (orbit (stabilizer G a) b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) := by
  classical
  let Γ := SwappedOrbital.graph a b hab t hta htb
  have hc' : orbit (stabilizer G a) c =
      (({a} : Set Ω) ∪ orbit (stabilizer G a) b)ᶜ := by
    simpa only [Set.singleton_union] using hc
  have hsr := SwappedOrbital.stronglyRegular a b hab t hta htb c hc'
  rw [hdegree, hsubdegree] at hsr
  have hcC : c ∈ (insert a (orbit (stabilizer G a) b))ᶜ :=
    hc ▸ mem_orbit_self c
  have hac : a ≠ c := fun h => hcC (Or.inl h.symm)
  have hna : ¬ Γ.Adj a c := fun h => hcC (Or.inr
    ((SwappedOrbital.adj_base a b hab t hta htb c).mp h))
  have hm := hsr.mu_pos_of_connected Γ (SwappedOrbital.connected a b hab t hta htb) hac hna
  let D := SimpleGraph.polarityDesign Γ hq hsr hm
  have hD : ∀ x y, D.incident x y ↔ y = x ∨ Γ.Adj x y := fun _ _ => Iff.rfl
  have hblock : D.block a = insert a (orbit (stabilizer G a) b) := by
    change insert a (Γ.neighborSet a) = _
    rw [SwappedOrbital.neighbor_base]
  have hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y := by
    intro g x y
    rw [hD, hD, SwappedOrbital.adj_smul_iff]
    exact or_congr (MulAction.injective g).eq_iff Iff.rfl
  refine ⟨D, hD, hblock, ?_⟩
  exact D.all_lines_card_of_kernel hact hq a (hblock.symm ▸ hk)

end Theory.GroupAction.SymplecticRankThree
