module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Quotient
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Orbit

/-!
# Assembly steps for intrinsic Ξ component containment

These deductions connect the supercritical/Fitting stage to actual lifted
C-components and justify the commutator identity for a relatively normal
component orbit. The normality and containment arguments using the model
outer automorphism groups remain separate mathematical obligations; no
full Proposition 1.3.4 or component-containment theorem is asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed pp.509–510.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Connect the normal-or-Fitting alternative to the intrinsic lifted-component witness. -/
theorem LocalInput.normal_or_component_of_fitting_alternative
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hf : (quotientImage H P).Normal ∨ FittingConditions p P H) :
    (X.subgroupOf H).Normal ∨ ∃ L : Subgroup G, ComponentDetection P H L := by
  rcases hf with hn | hf
  · exact Or.inl (h.normal_of_complement_quotient_normal hn)
  · exact Or.inr (h.exists_component_of_fitting hf)

/-- The actual [K,P] = K identity, once relative orbit normality is proved.
A.3.3(7) is supplied in its full universal form; the normal-or-index-two
alternative is the precise structural clause used from 1.2.1(3). -/
theorem LocalInput.detected_component_orbit_commutator
    (hA337 : ∀ (Y : Type u) [Group Y] [Finite Y] (B D : Subgroup Y),
      B.IsCComponent → ⁅B, D⁆ ≤ solvableRadical Y ∨ ⁅B, D⁆ = componentOrbit B D)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hL : ComponentDetection P H L)
    (hindex : (L.subgroupOf H).Normal ∨ (normalizer (L.subgroupOf H : Set H)).index = 2)
    (hn : ((componentOrbit L T).subgroupOf H).Normal) :
    ⁅componentOrbit L T, P⁆ = componentOrbit L T := by
  have hQL : X.pCoreIn 2 ≤ normalizer L := by
    rcases hindex with hnormal | hi
    · exact (pCoreIn_le 2 X).trans ((le_sup_left.trans h.overgroup).trans
        ((normal_subgroupOf_iff_le_normalizer hL.mem.1).mp hnormal))
    · exact h.core_le_normalizer_of_index_two hL.mem.1 hi
  have hKH : componentOrbit L T ≤ H := (componentOrbit_le_sup L T).trans
    (sup_le hL.mem.1 (le_sup_right.trans h.overgroup))
  exact h.commutator_componentOrbit_eq hQL
    (hL.le_commutator_of_A_3_3_7 hA337 h.complement_le_overgroup)
    (h.complement_le_overgroup.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))

end CFSG.Quasithin.Chapter1.XiEmbedding
