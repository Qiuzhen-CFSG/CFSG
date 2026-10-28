module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Identifying rank-two Lie-type groups

The source's Theorem 5.3.4 identifies a simple completion of a Lie amalgam:
once recognition gives an extension of the defining group, simplicity removes
the proper extension. Lemma 5.3.6 uses the two maximal elementary abelian
subgroups of the Sylow subgroup to establish weak closure. The elementary
group-theoretic steps are recorded here independently of the still-developing
amalgam and rank-two recognition interfaces.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Section 5.3, pp. 659--660.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter5.Section03

/-- Conjugacy transport of the centralizer bound used in Lemma 5.3.3. -/
theorem centralizer_le_of_conjugate
    {G : Type*} [Group G] (M : Subgroup G) {z z' : G}
    (g : G) (hg : g ∈ M) (hz' : z' = g * z * g⁻¹)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ M) :
    Subgroup.centralizer ({z'} : Set G) ≤ M := by
  intro x hx
  have hcomm : x * z' = z' * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hconj : g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [hz'] at hcomm
    have h := congrArg (fun y : G => g⁻¹ * y * g) hcomm
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_inv_cancel, one_mul, mul_one] using h
  have hm := M.mul_mem (M.mul_mem hg (hcz hconj)) (M.inv_mem hg)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hm

/-- A transitive local action propagates one centralizer bound to the whole
orbit, as in the verification of F.4.31(b,c) in Lemma 5.3.3. -/
theorem centralizer_le_of_transitive_action
    {G : Type*} [Group G] (M : Subgroup G) (Z : Set G) (z : G)
    (htrans : ∀ z' ∈ Z, ∃ g ∈ M, z' = g * z * g⁻¹)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ M) :
    ∀ z' ∈ Z, Subgroup.centralizer ({z'} : Set G) ≤ M := by
  intro z' hz'
  obtain ⟨g, hg, rfl⟩ := htrans z' hz'
  exact centralizer_le_of_conjugate M g hg rfl hcz

/-- The extension-collapse step in the proof of Theorem 5.3.4: a nontrivial
normal defining subgroup fills a completion isomorphic to a simple group. -/
theorem simple_completion_eq_defining_group
    {G M : Type*} [Group G] [Group M] [IsSimpleGroup G]
    (e : G ≃* M) (L : Subgroup M) [L.Normal] (hL : L ≠ ⊥) :
    Nonempty (G ≃* L) := by
  have hsimple : IsSimpleGroup M := e.symm.isSimpleGroup
  have htop : L = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal L inferInstance).resolve_left hL
  exact ⟨e.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))⟩

/-- The two-candidate fusion argument of Lemma 5.3.6(1). If every conjugate
of `V₁` returning to `T` is one of `V₁,V₂`, and the two are not conjugate,
then `V₁` is weakly closed in `T`. -/
theorem weakly_closed_of_two_candidates
    {G : Type*} [Group G] (T V₁ V₂ : Subgroup G)
    (hreturn : ∀ g : G,
      V₁.map (MulAut.conj g).toMonoidHom ≤ T →
        V₁.map (MulAut.conj g).toMonoidHom = V₁ ∨
        V₁.map (MulAut.conj g).toMonoidHom = V₂)
    (hnotconj : ∀ g : G, V₁.map (MulAut.conj g).toMonoidHom ≠ V₂) :
    ∀ g : G, V₁.map (MulAut.conj g).toMonoidHom ≤ T →
      V₁.map (MulAut.conj g).toMonoidHom = V₁ := by
  intro g hg
  exact (hreturn g hg).resolve_right (hnotconj g)

end CFSG.Quasithin.Chapter5.Section03
