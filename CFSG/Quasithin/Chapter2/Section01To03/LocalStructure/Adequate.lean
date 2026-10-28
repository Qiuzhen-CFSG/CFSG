module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Source
public import CFSG.Quasithin.Chapter1.Section02.Adequate

/-!
# Connecting the adequate Section 1.2 boundary

The canonical local-family transport converts the adequate boundary's
literal 1.2.4 containment into the common ambient embedding input used by
2.3.9(6). This uses the full known-simple class and preserves the earlier
universal A.3 inputs. It neither uses the unresolved center–Frattini equality
nor adds a homocyclic exponent restriction.

Source: Aschbacher–Smith 1.2.4 and 2.3.9(6), printed pp.505 and 526.
The existing producer of the adequate boundary is qt-1-02-adequate-assembly.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Supply the component-embedding input from the actual adequate
Section 1.2 theorem, retaining precisely its genuine A.3 inputs. -/
theorem embedding124Input_of_adequate
    (earlier : Chapter1.Section02.Adequate.A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) : Embedding124Input G := by
  intro N hN P B hBN hB
  have hb : B.subgroupOf N ∈ Chapter1.L N (P : Subgroup N) := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf (map_subtype_le (P : Subgroup N)) hBN).mp
      (show B ∈ Chapter1.LIn N ((P : Subgroup N).map N.subtype) from ⟨hBN, hB⟩)
    change B.subgroupOf N ∈ Chapter1.L N (((P : Subgroup N).map N.subtype).comap N.subtype) at hh
    rwa [comap_map_eq_self_of_injective N.subtype_injective] at hh
  obtain ⟨D, hD, hBD, _⟩ := Chapter1.Section02.Adequate.local_embeddings_of_A3 earlier hG hN P hb
  refine ⟨D, hD, ?_⟩
  have hm := map_mono hBD (f := N.subtype)
  rwa [map_subgroupOf_eq_of_le hBN] at hm

/-- Apply the adequate embedding boundary to the actual component and
core normalizer of 2.3.9(6); no separate 1.2.4 premise remains. -/
theorem lemma_2_3_9_6_of_adequate
    (earlier : Chapter1.Section02.Adequate.A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (source115 : Structural115Input G)
    {M H U L : Subgroup G}
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x)
    (B : Subgroup H) (hB : Theory.GroupTheory.IsComponent H B) :
    B.map H.subtype = ⁅B.map H.subtype, zpowers z⁆ ∧ ¬ B.map H.subtype ≤ M ∧
      ∃ D : Subgroup (normalizer (twoCore H : Set G)),
        Theory.GroupTheory.IsComponent (normalizer (twoCore H : Set G)) D ∧
        B.map H.subtype ≤ D.map (normalizer (twoCore H : Set G)).subtype :=
  lemma_2_3_9_6_of_115_124 hG source115 (embedding124Input_of_adequate earlier hG)
    T hM hTM hunique hH hpair S hUS hz hzS hcentral hMcentral B hB

end CFSG.Quasithin.Chapter2
