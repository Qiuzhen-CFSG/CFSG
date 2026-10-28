module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The hyperplane commutator argument for §8.3

If a hyperplane B of a corank-i subgroup A of a conjugate Vᵍ has corank
below r(G,V), then C_V(B) normalizes Vᵍ. Consequently [C_V(B),A] lies
in V ∩ Vᵍ. A fusion condition on that intersection now forces Vᵍ to
centralize V. Applying this to every generator proves the corresponding
weak-closure bound.

The relative indices, global parameter and weak-closure subgroup here are
the actual constructions of E.3. The hyperplane witness and intersection
fusion are explicit inputs, not asserted tensor or FSU theorems. In §8.3
they come from the S₁ × S₂ action and Lemma 8.3.13, respectively; Lemma
8.3.11 supplies r > 3. Final source assembly must establish those inputs.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 8.3.14, printed p.727, PDF p.744.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section03

open Subgroup ChapterE

variable {G : Type*} [Group G]

/-- The tensor geometry needed in 8.3.14: an actual hyperplane of A and
a commutator element in the ambient conjugacy class of z. No normalization
of Vᵍ or intersection with Vᵍ is part of this input. -/
def HasFusedHyperplane (V A : Subgroup G) (z : G) : Prop :=
  ∃ B : Subgroup G, B ≤ A ∧ B.relIndex A = 2 ∧
    ∃ x ∈ ⁅V ⊓ centralizer (B : Set G), A⁆, IsConj x z

/-- An index-two step raises the actual binary corank by one. -/
theorem corank_hyperplane_of_relIndex {W A B : Subgroup G} {i : ℕ}
    (hBA : B ≤ A) (hAW : A ≤ W)
    (hB : B.relIndex A = 2) (hA : A.relIndex W = 2 ^ i) :
    subgroupCorank W B = i + 1 := by
  unfold subgroupCorank
  rw [← relIndex_mul_relIndex B A W hBA hAW, hB, hA,
    ← pow_succ', Nat.log_pow (by decide)]

/-- The small-corank bound gives both containments of the commutator.
Normalization is relative to V and Vᵍ; neither subgroup is assumed normal
in the ambient group. -/
theorem commutator_le_intersection_of_corank_lt_globalR
    {V A B : Subgroup G} (g : G)
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAN : A ≤ normalizer (V : Set G))
    (hB : B ≤ V.map (MulAut.conj g).toMonoidHom)
    (hr : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) < globalR V) :
    ⁅V ⊓ centralizer (B : Set G), A⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have hBN : centralizer (B : Set G) ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    apply centralizer_le_normalizer_of_corank_lt_globalR hB
    rwa [globalR_map_equiv]
  refine le_inf ?_ ?_
  · exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAN)
  · exact (commutator_mono le_rfl hA).trans
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hBN))

/-- A fused commutator obtained from a hyperplane gives a genuine fused
element in V ∩ Vᵍ. This is the normalization step in 8.3.14. -/
theorem exists_fused_intersection_of_hyperplane
    {V A : Subgroup G} {z : G} {i : ℕ} (g : G)
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAN : A ≤ normalizer (V : Set G))
    (hi : A.relIndex (V.map (MulAut.conj g).toMonoidHom) = 2 ^ i)
    (hr : ((i + 1 : ℕ) : ℕ∞) < globalR V)
    (hw : HasFusedHyperplane V A z) :
    ∃ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom, IsConj x z := by
  obtain ⟨B, hBA, hB, x, hx, hxz⟩ := hw
  have hcorank := corank_hyperplane_of_relIndex hBA hA hB hi
  have hcomm := commutator_le_intersection_of_corank_lt_globalR g hA hAN
    (hBA.trans hA) (by rwa [hcorank])
  exact ⟨x, hcomm hx, hxz⟩

/-- The group-theoretic weak-closure deduction from hyperplane geometry and
fusion control, using the literal generators Γᵢ(S,V). -/
theorem weakClosure_le_centralizer_of_fused_hyperplanes
    {V S : Subgroup G} {z : G} {i : ℕ}
    (hSN : S ≤ normalizer (V : Set G))
    (hr : ((i + 1 : ℕ) : ℕ∞) < globalR V)
    (hgeometry : ∀ A ∈ gamma V S i, ¬ A ≤ centralizer (V : Set G) →
      HasFusedHyperplane V A z)
    (hfusion : ∀ (g x : G), x ∈ V →
      x ∈ V.map (MulAut.conj g).toMonoidHom → IsConj x z →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    indexedWeakClosure V S i ≤ centralizer (V : Set G) := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  by_contra hnoncentral
  obtain ⟨⟨g, hAV, hi⟩, hAS⟩ := hA
  obtain ⟨x, hx, hxz⟩ := exists_fused_intersection_of_hyperplane g hAV
    (hAS.trans hSN) hi hr (hgeometry A ⟨⟨g, hAV, hi⟩, hAS⟩ hnoncentral)
  exact hnoncentral (hAV.trans (hfusion g x hx.1 hx.2 hxz))

end CFSG.Quasithin.Chapter8.Section03
