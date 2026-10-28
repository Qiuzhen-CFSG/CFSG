module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A Sylow normalizer obstruction to conjugacy inside a subgroup

Suppose `S ≤ T`, where `T` is a p-group, and `N_S(Q)` is Sylow in
`N_G(Q)`. An element of `T` outside `S` cannot carry `Q` into its `S`-orbit:
otherwise adjusting it by an element of `S` gives an element of `N_T(Q)`
outside `N_S(Q)`, contradicting Sylow maximality.

This is the Frattini-argument obstruction used repeatedly in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 2.5.21 and 2.5.24, pp.565 and 568.
Conjugation here is the left action `g Q g⁻¹`; the orbit assertion is
independent of choosing left or right conjugation conventions.
-/

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ} {S T Q : Subgroup G}

/-- A Sylow normalizer prevents an outside p-element from giving conjugacy
already realized in `S`. The equality of ambient subgroup images specifies
relative Sylow membership, without imposing ambient normality on `Q`. -/
public theorem conjugate_ne_of_sylow_normalizer
    (hT : IsPGroup p T) (hST : S ≤ T)
    (P : Sylow p (normalizer (Q : Set G)))
    (hP : (P : Subgroup (normalizer (Q : Set G))).map
      (normalizer (Q : Set G)).subtype = S ⊓ normalizer (Q : Set G))
    {x : G} (hx : x ∈ T) (hxS : x ∉ S) {s : G} (hs : s ∈ S) :
    ConjAct.toConjAct x • Q ≠ ConjAct.toConjAct s • Q := by
  intro he
  have hn : s⁻¹ * x ∈ normalizer (Q : Set G) := by
    apply conjAct_pointwise_smul_iff.mp
    rw [ConjAct.toConjAct_mul, mul_smul, he, ConjAct.toConjAct_inv, inv_smul_smul]
  have heq : T ⊓ normalizer (Q : Set G) = S ⊓ normalizer (Q : Set G) := by
    rw [← hP]
    exact inf_eq_sylow_map P hT (hP ▸ inf_le_left.trans hST)
  have hmem : s⁻¹ * x ∈ S :=
    (heq ▸ (show s⁻¹ * x ∈ T ⊓ normalizer (Q : Set G) from
      ⟨T.mul_mem (T.inv_mem (hST hs)) hx, hn⟩)).1
  exact hxS ((S.mul_mem_cancel_left (S.inv_mem hs)).mp hmem)

/-- If `S` is transitive on a family containing the image of `Q` under an
outside element of `T`, then `N_S(Q)` cannot be Sylow in `N_G(Q)`.
The family may, for example, be the maximal elementary abelian subgroups. -/
public theorem false_of_transitive_family_of_sylow_normalizer
    (hT : IsPGroup p T) (hST : S ≤ T)
    (P : Sylow p (normalizer (Q : Set G)))
    (hP : (P : Subgroup (normalizer (Q : Set G))).map
      (normalizer (Q : Set G)).subtype = S ⊓ normalizer (Q : Set G))
    (F : Set (Subgroup G))
    (htrans : ∀ R ∈ F, ∃ s ∈ S, ConjAct.toConjAct s • Q = R)
    {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    (hxF : ConjAct.toConjAct x • Q ∈ F) : False := by
  obtain ⟨s, hs, he⟩ := htrans _ hxF
  exact conjugate_ne_of_sylow_normalizer hT hST P hP hx hxS hs he.symm

end Subgroup
