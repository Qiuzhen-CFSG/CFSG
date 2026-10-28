module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Normalizer control for trivial-intersection subgroups

If distinct `M`-conjugates of `V` have trivial intersection, an element of `M`
normalizing a nontrivial subgroup of `V` must normalize `V`. When the full
normalizer of `V` lies in `M`, this identifies `H ∩ M` with `N_H(V)` for any
`H` normalizing that subgroup. No finiteness assumption is needed.

We also record the elementary fusion obstruction: if `C_G(x) ≤ M`, a
conjugator outside `M` cannot have the same effect on `x` as an element of `M`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 12.2.6 and the beginning of Lemma 12.2.16,
printed pp. 797 and 799--800. The representation-theoretic verification of the
TI and fusion hypotheses is separate from these general group arguments.
-/

namespace Subgroup

variable {G : Type*} [Group G] {M V U H : Subgroup G}

/-- Inside `M`, a nontrivial subgroup of a TI subgroup controls its normalizer. -/
public theorem inf_normalizer_le_of_trivial_intersections
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ normalizer (U : Set G) ≤ normalizer (V : Set G) := by
  intro g hg
  rcases hTI g hg.1 with hd | he
  · have hfix := mem_normalizer_iff_map_conj_eq.mp hg.2
    have hmap : U ≤ V.map (MulAut.conj g).toMonoidHom := by
      rw [← hfix]
      exact map_mono hUV
    exact False.elim (hU (le_bot_iff.mp (hd ▸ le_inf hUV hmap)))
  · exact mem_normalizer_iff_map_conj_eq.mpr he

/-- The ambient-subgroup form of `H ∩ M = N_H(V)`. -/
public theorem inf_eq_inf_normalizer_of_trivial_intersections
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hN : normalizer (V : Set G) ≤ M)
    (hU : U ≠ ⊥) (hUV : U ≤ V) (hH : H ≤ normalizer (U : Set G)) :
    H ⊓ M = H ⊓ normalizer (V : Set G) := by
  apply le_antisymm
  · intro g hg
    exact ⟨hg.1, inf_normalizer_le_of_trivial_intersections hTI hU hUV
      ⟨hg.2, hH hg.1⟩⟩
  · exact inf_le_inf_left H hN

/-- Centralizing a nontrivial subgroup of a TI subgroup forces normalization. -/
public theorem inf_centralizer_le_normalizer_of_trivial_intersections
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G) :=
  (inf_le_inf_left M (centralizer_le_normalizer (U : Set G))).trans
    (inf_normalizer_le_of_trivial_intersections hTI hU hUV)

/-- In particular, `C_M(x) ≤ N_G(V)` for every nonidentity element of `V`. -/
public theorem inf_elementCentralizer_le_normalizer_of_trivial_intersections
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    {x : G} (hx : x ∈ V) (hne : x ≠ 1) :
    M ⊓ centralizer ({x} : Set G) ≤ normalizer (V : Set G) := by
  have hU : closure ({x} : Set G) ≠ ⊥ := by
    intro he
    have hxU : x ∈ closure ({x} : Set G) := subset_closure (Set.mem_singleton x)
    rw [he] at hxU
    exact hne hxU
  have hUV : closure ({x} : Set G) ≤ V :=
    (closure_le V).mpr (Set.singleton_subset_iff.mpr hx)
  simpa only [centralizer_closure] using
    inf_centralizer_le_normalizer_of_trivial_intersections hTI hU hUV

/-- With its centralizer in `M`, an element detects conjugators outside `M`. -/
public theorem conjugator_mem_of_centralizer_le {x g : G}
    (hC : centralizer ({x} : Set G) ≤ M)
    (hf : ∃ m ∈ M, m * x * m⁻¹ = g * x * g⁻¹) : g ∈ M := by
  obtain ⟨m, hm, he⟩ := hf
  have hc : m⁻¹ * g ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    symm
    calc
      x * (m⁻¹ * g) = m⁻¹ * (m * x * m⁻¹) * g := by group
      _ = m⁻¹ * (g * x * g⁻¹) * g := by rw [he]
      _ = (m⁻¹ * g) * x := by group
  have := M.mul_mem hm (hC hc)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using this

end Subgroup
