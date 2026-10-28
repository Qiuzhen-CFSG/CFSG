module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SourceOmega
public import Stellmacher.OmegaOneCenterMap

/-!
# The omega-center contradiction in the four-dimensional orthogonal branch

For U ≤ T, every central involution of N_T(U) lies in C_T(U). Thus its
omega-center is exactly the N_T(U)-fixed part of Ω₁Z(C_T(U)). When this
last omega-center is the original module V, the literal fixed-space bound
C_V(N_T(U)) ≤ U contradicts the proved source E.6.10(4) for an obstruction
hyperplane.

This supplies the displayed group-theoretic identity and its weak-closure
application in the proof of 6.1.4. The orthogonal module geometry producing
the two stated equalities and the central-point condition remains separate.
Source: Aschbacher–Smith, 6.1.4, printed p.665 (PDF p.682), and E.6.10(4).
-/

public section

open Subgroup Stellmacher Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source

variable {G : Type*} [Group G]

/-- The literal omega-center identity for a subgroup of the source Sylow. -/
theorem omega_normalizer_eq_centralizer_fixed {T U : Subgroup G} (hUT : U ≤ T) :
    omegaOneCenterAmbient (T ⊓ normalizer (U : Set G)) =
      omegaOneCenterAmbient (T ⊓ centralizer (U : Set G)) ⊓
        centralizer (T ⊓ normalizer (U : Set G) : Set G) := by
  have hUS : U ≤ T ⊓ normalizer (U : Set G) := le_inf hUT U.le_normalizer
  have hQS : T ⊓ centralizer (U : Set G) ≤ T ⊓ normalizer (U : Set G) :=
    inf_le_inf_left T (Subgroup.centralizer_le_normalizer _)
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
    refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr ⟨?_, hx2, ?_⟩, hxc⟩
    · exact ⟨hxS.1, fun u hu => hxc u (hUS hu)⟩
    · intro q hq
      exact hxc q (hQS hq)
  · rintro ⟨hxQ, hxc⟩
    obtain ⟨hxQ, hx2, _⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hxQ
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hQS hxQ, hx2, hxc⟩

open ChapterE ChapterE.Section06

/-- An actual source hyperplane with the orthogonal fixed-space geometry
has centralizer inside the original maximal two-local subgroup. -/
theorem four_hyperplane_centralizer_le_of_fixed_space [Finite G]
    {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hodd : oddCentralizerCondition M V U) (hc : subgroupCorank V U = 1)
    (hfit : U ⊓ sylowFixedSpace (T : Subgroup G) V ≠ ⊥ ∨
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (hV : V = omegaOneCenterAmbient ((T : Subgroup G) ⊓ centralizer (U : Set G)))
    (hfixed : V ⊓ centralizer
      ((T : Subgroup G) ⊓ normalizer (U : Set G) : Set G) ≤ U) :
    centralizer (U : Set G) ≤ M := by
  by_contra hescape
  apply h.source_omega_center_not_le ⟨hUV, hU, hescape, hodd⟩ hc hfit
  rw [omega_normalizer_eq_centralizer_fixed (hUV.trans h.le_sylow), ← hV]
  exact hfixed

end CFSG.Quasithin.Chapter6.Source
