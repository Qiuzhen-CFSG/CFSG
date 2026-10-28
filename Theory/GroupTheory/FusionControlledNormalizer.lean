module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Normalizer control from fusion of a distinguished element

Suppose E contains C_G(d) and controls fusion of d into E. A conjugator
carrying d into E already belongs to E, by correcting it into C_G(d).
Consequently E contains the normalizer of every subgroup U≤E containing d.
For a characteristic-p group H, this applies to Oₚ(H) whenever E contains
a Sylow subgroup S of H and d lies in the center of S.

Source application: the unique-fixed-point argument in Aschbacher–Smith
13.4.9, printed p.906. The proof here uses conjugators directly.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Correcting a conjugator into C_G(d) puts the original conjugator in E. -/
theorem conjugator_mem_of_element_fusion (E : Subgroup G) (d : G)
    (hf : ∀ b ∈ E, IsConj d b → ∃ c ∈ E, MulAut.conj c d = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    {g : G} (hg : MulAut.conj g d ∈ E) : g ∈ E := by
  obtain ⟨c, hcE, he⟩ := hf _ hg (isConj_iff.mpr ⟨g, rfl⟩)
  have hfix : MulAut.conj (c⁻¹ * g) d = d := by
    have hh := congrArg (MulAut.conj c⁻¹) he
    simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh.symm
  have hmem := hc (mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hfix))
  simpa only [mul_inv_cancel_left] using E.mul_mem hcE hmem

/-- A subgroup through d that lies in E has its whole normalizer in E. -/
theorem normalizer_le_of_element_fusion (E U : Subgroup G) (d : G)
    (hf : ∀ b ∈ E, IsConj d b → ∃ c ∈ E, MulAut.conj c d = b)
    (hc : centralizer ({d} : Set G) ≤ E) (hdU : d ∈ U) (hUE : U ≤ E) :
    normalizer (U : Set G) ≤ E := by
  intro g hg
  apply conjugator_mem_of_element_fusion E d hf hc
  exact hUE ((hg d).mp hdU)

/-- Characteristic p puts a central Sylow element into the actual p-core;
fusion then controls the normalizer of that core and hence H. -/
theorem le_of_characteristic_p_of_element_fusion [Finite G]
    {p : ℕ} [Fact p.Prime] (E H : Subgroup G) (S : Sylow p H) (d : G)
    (hf : ∀ b ∈ E, IsConj d b → ∃ c ∈ E, MulAut.conj c d = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    (hchar : centralizer (pCore p H : Set H) ≤ pCore p H)
    (hSE : (S : Subgroup H).map H.subtype ≤ E)
    (hdH : d ∈ H)
    (hdC : d ∈ centralizer ((S : Subgroup H).map H.subtype : Set G)) : H ≤ E := by
  have hdcore : (⟨d, hdH⟩ : H) ∈ pCore p H := by
    apply hchar
    intro q hq
    apply Subtype.ext
    exact hdC q.val (mem_map_of_mem H.subtype (pCore_isPGroup.le_sylow_of_normal S hq))
  have hcoreE : H.pCoreIn p ≤ E :=
    (H.pCoreIn_le_sylow S).trans hSE
  apply le_trans ?_ (normalizer_le_of_element_fusion E (H.pCoreIn p) d
    hf hc (mem_map_of_mem H.subtype hdcore) hcoreE)
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
    range_subtype] using (pCore p H).le_normalizer_map H.subtype

end Subgroup
