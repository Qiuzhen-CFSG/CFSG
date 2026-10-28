module
public import Theory.GroupAction.IrreducibleNormalIntersection
public import Theory.GroupAction.PerfectFrattiniAction

/-!
# Perfect normal subgroups and irreducible Frattini quotients

Let Q be a finite normal p-subgroup whose Frattini quotient is irreducible
under its full normalizer. A normal perfect subgroup N acting nontrivially
on Q contains Q. Indeed, irreducibility places Q ∩ N inside Φ(Q) or makes
it all of Q. In the former case N acts trivially on Q/Φ(Q), hence on Q by
the Burnside basis kernel theorem and perfectness, a contradiction.

When Q contains its centralizer, every nontrivial normal perfect subgroup
acts nontrivially, so the same containment follows without an action premise.

Source application: DGS85, Groups and Graphs, Part II, (10.10)(d), p.164,
followed by original-factor core containment in Aschbacher--Smith F.1.12,
p.264. This implication does not assert the DGS irreducibility hypothesis.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial perfect normal action on an irreducible Frattini quotient
forces the whole normal p-subgroup into the actor. -/
theorem IsNormalizerFrattiniIrreducible.le_perfect_normal_of_noncentral {p : ℕ} [Fact p.Prime]
    (Q N : Subgroup G) [Q.Normal] [N.Normal] [Group.IsPerfect N]
    (hp : IsPGroup p Q) (hirr : IsNormalizerFrattiniIrreducible Q)
    (hn : ¬ N ≤ centralizer (Q : Set G)) : Q ≤ N := by
  rcases hirr.inf_normal_le_frattini_or_le N with hf | hfull
  · let a : N →* MulAut Q := (MulAut.conjNormal : G →* MulAut Q).comp N.subtype
    have ha : a ≠ 1 := by
      intro he
      apply hn
      intro n hn q hq
      have hh := congrArg (fun f : N →* MulAut Q => (f ⟨n, hn⟩ ⟨q, hq⟩ : G)) he
      change n * q * n⁻¹ = q at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply (a.frattini_comp_ne_one_of_isPerfect hp ha).elim
    apply MonoidHom.ext
    intro n
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H q =>
      change quotientAut (frattini Q) (a n) (QuotientGroup.mk' (frattini Q) q) =
        QuotientGroup.mk' (frattini Q) q
      rw [quotientAut_apply_mk]
      apply Eq.symm
      apply QuotientGroup.eq.mpr
      have hc : ⁅(q : G)⁻¹, (n : G)⁆ ∈ Q ⊓ N :=
        (commutator_le_inf Q N) (commutator_mem_commutator (Q.inv_mem q.property) n.property)
      have hphi : Q.subtype (q⁻¹ * a n q) ∈ (frattini Q).map Q.subtype := by
        change (q : G)⁻¹ * ((n : G) * (q : G) * (n : G)⁻¹) ∈ _
        simpa only [commutatorElement_def, inv_inv, mul_assoc] using hf hc
      exact (mem_map_iff_mem Q.subtype_injective).mp hphi
  · exact hfull

/-- A self-centralizing normal p-subgroup with irreducible Frattini quotient
lies in every nontrivial perfect normal subgroup. -/
theorem IsNormalizerFrattiniIrreducible.le_perfect_normal_of_selfCentralizing {p : ℕ} [Fact p.Prime]
    (Q N : Subgroup G) [Q.Normal] [N.Normal] [Group.IsPerfect N] [Nontrivial N]
    (hp : IsPGroup p Q) (hirr : IsNormalizerFrattiniIrreducible Q)
    (hc : centralizer (Q : Set G) ≤ Q) : Q ≤ N := by
  apply IsNormalizerFrattiniIrreducible.le_perfect_normal_of_noncentral Q N hp hirr
  intro hn
  have hN : IsPGroup p N := hp.to_le (hn.trans hc)
  exact Group.IsPerfect.not_isNilpotent N hN.isNilpotent
end Subgroup
