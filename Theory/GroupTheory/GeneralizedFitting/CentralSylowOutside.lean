module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerLayerContainment
public import Theory.GroupTheory.SylowCentralizerCore
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.SylowFixedSpanReduced
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# A central Sylow element outside the two-core moves a component

When the odd core vanishes, the Fitting subgroup is O₂. An element
centralizing a Sylow two-subgroup centralizes O₂; if it also centralized
every component, generalized-Fitting self-centralization would put it
in O₂. A moved component is normalized by the same element, since its
simple quotient has even order, so the component commutator is the whole
component. Solvability is excluded by Fitting self-centralization.

In the complementary core branch, the conjugate span of a central Sylow
involution is an elementary abelian reduced module on its literal
conjugation quotient.

Source application: Aschbacher--Smith 13.2.12, printed p.883, at the
original complementary point involution.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]

/-- The literal conjugate span in the core branch is a reduced elementary module. -/
theorem central_sylow_core_span_reduced
    (S : Sylow 2 D) (x : D) (hc : x ∈ centralizer (S : Set D))
    (hx : x ∈ pCore 2 D) (h2 : x^2=1) :
    IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤) := by
  let W := conjugateSpanBy (zpowers x) ⊤
  have hW : W ≤ pCore 2 D := conjugateSpanBy_le (zpowers_le.mpr hx)
    (by rw [normalizer_eq_top])
  let : W.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_conjugateSpanBy (zpowers x) ⊤))
  have hcW : x ∈ centralizer (W : Set D) :=
    centralizer_le (hW.trans (pCore_isPGroup.le_sylow_of_normal S)) hc
  let : IsMulCommutative W := (conjugateSpanBy_commutative_iff (zpowers x) ⊤).mpr
    (zpowers_le.mpr hcW)
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one h2
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative (zpowers x) ⊤
  exact ⟨inferInstance,inferInstance,
    centralizer_quotient_pCore_eq_bot_of_sylow_fixed_span W (zpowers x) S
      (le_conjugateSpanBy _ _) (zpowers_le.mpr hc) le_rfl⟩

/-- The actual central Sylow actor moves and normalizes an ordinary component. -/
theorem exists_component_commutator_of_central_sylow_outside_core
    (S : Sylow 2 D) (ho : pPrimeCore 2 D = ⊥) (x : D)
    (hc : x ∈ centralizer (S : Set D)) (hn : x ∉ pCore 2 D) :
    ∃ K : Subgroup D, IsComponent D K ∧ ⁅K,zpowers x⁆ = K ∧ K ≠ ⊥ := by
  have hf := Fitting_eq_pcore D 2 ho
  have hxF : x ∈ centralizer (fittingSubgroup D : Set D) := by
    rw [hf]
    exact centralizer_le (pCore_isPGroup.le_sylow_of_normal S) hc
  have hex : ∃ K : Subgroup D, IsComponent D K ∧ ⁅K,zpowers x⁆ ≠ ⊥ := by
    by_contra! hh
    have hE : componentLayer D ≤ centralizer (zpowers x : Set D) :=
      sSup_le fun K hK => commutator_eq_bot_iff_le_centralizer.mp (hh K hK)
    have hx : x ∈ centralizer (generalizedFitting D : Set D) := by
      exact (le_centralizer_iff.mp (sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hxF)) hE)) (mem_zpowers x)
    exact hn (hf ▸ centralizer_generalizedFitting_le_fitting hx)
  obtain ⟨K,hK,hm⟩ := hex
  have he := hK.commutator_eq_self_of_normalizes
    (hK.normalized_of_centralizes_sylow S (zpowers_le.mpr hc)) hm
  exact ⟨K,hK,he,fun hb => hm (he.trans hb)⟩

/-- The same actor rules out solvability, independently of any model catalogue. -/
theorem not_solvable_of_central_sylow_outside_core
    (S : Sylow 2 D) (ho : pPrimeCore 2 D = ⊥) (x : D)
    (hc : x ∈ centralizer (S : Set D)) (hn : x ∉ pCore 2 D) :
    ¬ Group.IsSolvable D := fun hs =>
  hn (centralizer_sylow_le_pCore_of_pPrimeCore_eq_bot hs ho S hc)

end Theory.GroupTheory
