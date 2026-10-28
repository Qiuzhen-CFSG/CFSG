module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FixedSpace
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Source

/-!
# The fixed-involution fusion consumer at the original G,T

The original guarded Section 12.2 inputs now produce the literal 12.4.7
fixed involution and weak closure in V. The fixed-space contradiction takes
only the independent pointwise commutator output on that same chosen module.
Its symmetry puts the conjugate of the fixed involution back in V, where
weak closure forces the conjugator to normalize V, a contradiction.

The universal fusion and fixed-space interfaces remain unchanged. The
independent commutator branch and the earlier source inputs retain their
existing source producers and final assembly owners.
Source: Aschbacher–Smith, 12.4.5–9, pp.813–816.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04 Chapter12.Section04.SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal pointwise 12.4.7 input, with all local fusion premises proved. -/
theorem slThreeFusion1247_of_source_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      ∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z := by
  obtain ⟨z, hz, hfix, hc, hf, _⟩ :=
    SLThreeSource.At.fusion_of_source h D hmany structural modules hmodel hne
  exact ⟨z, hz, hfix, hc, hf⟩

/-- Apply local fusion to the original fixed-space contradiction. Only the
independently owned pointwise commutator output remains explicit. -/
theorem slThreeFixedSpace1242_of_source_fusion_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (geometry : fixedSubgroup L V ≠ ⊥ → ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    fixedSubgroup L V = ⊥ := by
  by_contra hne
  let := D.elementary
  obtain ⟨z, _, hz, hc, hf⟩ :=
    slThreeFusion1247_of_source_at h D hmany structural modules hmodel hne
  obtain ⟨g, hn, hfix, hsymm, hcomm⟩ := geometry hne
  have hzf : z ∈ fixedSubgroup L V := hz ▸ mem_zpowers z
  have hL : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hzf.2 l hl)
  apply hcomm
  apply commutator_eq_bot_of_fusion_and_symmetry hL ?_ hc hn (hfix hzf) hsymm
  intro a ha
  exact ⟨1, L.one_mem, by simpa using hf a ha⟩

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
