module

public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!+# F.7: local cores and algebraic faithfulness

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.7.3(8), F.7.4 and F.7.7, printed pp.311--312
(PDF pp.322--323).

The edge subgroup is literally B ∩ C. Its local kernel in B is the image in
G of the normal core of (B ∩ C).subgroupOf B. Every equality below compares
subgroups of this same ambient G; no ambient normality of a vertex is assumed.

The F.7.3(8) algebraic step uses the proved generalized-Fitting centralizer
theorem to derive self-centralization from F*(B) = O₂(B). The geometry owner
must identify a stabilized ball kernel as a common normal subgroup before
applying this criterion. The containment chain and core identities need no
geometry once F.7.3(7) identifies the local kernels. F.7.7(1) uses genuine
reducedness and C_T(V) = O₂(C_B(V)); its residual is O^{2′}, the intersection
of normal subgroups of odd index, as confirmed in the source PDF.
-/

public section
namespace CFSG.Quasithin.ChapterF.LocalCores

open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamLocalCores

variable {G : Type*} [Group G]

/-- The algebraic faithfulness criterion in F.7.3(8), with the source's
generalized-Fitting hypothesis and relative normality in both vertices. -/
theorem lemma_F_7_3_eight_algebra (B C K : Subgroup G) [Finite B]
    (hKB : K ≤ B) (hKC : K ≤ C)
    (hnB : (K.subgroupOf B).Normal) (hnC : (K.subgroupOf C).Normal)
    (hF : generalizedFitting B = pCore 2 B)
    (hzero : pCore 2 (B ⊔ C : Subgroup G) = ⊥) : K = ⊥ := by
  have hc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B := by
    simpa only [hF] using centralizer_generalizedFitting_le B
  exact common_normal_eq_bot B C K (le_inf hKB hKC)
    ((normal_subgroupOf_iff_le_normalizer hKB).mp hnB)
    ((normal_subgroupOf_iff_le_normalizer hKC).mp hnC) hzero hc

/-- F.7.4 for two adjacent vertex groups, with their literal intersection
as edge stabilizer and the normal core as the local kernel at C. -/
theorem lemma_F_7_4 (B C : Subgroup G) :
    B.pCoreIn 2 ⊓ localKernel C (B ⊓ C) ≤
        (B ⊓ C).pCoreIn 2 ⊓ localKernel C (B ⊓ C) ∧
      (B ⊓ C).pCoreIn 2 ⊓ localKernel C (B ⊓ C) ≤
        (localKernel C (B ⊓ C)).pCoreIn 2 :=
  core_containment_chain 2 B C (B ⊓ C) inf_le_left

/-- F.7.7(2). The edge contains the supplied Sylow subgroup of B, so
O₂(B) is exactly the edge core intersected with the local kernel at B. -/
theorem lemma_F_7_7_two (B C : Subgroup G) (T : Sylow 2 B)
    (hTC : (T : Subgroup B).map B.subtype ≤ C) :
    B.pCoreIn 2 = (B ⊓ C).pCoreIn 2 ⊓ localKernel B (B ⊓ C) :=
  vertex_core_eq_edge_inf_kernel B (B ⊓ C) inf_le_left T
    (le_inf (map_subtype_le _) hTC)

/-- The kernel-core equality used in F.7.7(1), already valid under F.7.1's
Sylow containment. This also applies at every conjugate vertex. -/
theorem kernel_core_eq_vertex_core (B C : Subgroup G) (T : Sylow 2 B)
    (hTC : (T : Subgroup B).map B.subtype ≤ C) :
    (localKernel B (B ⊓ C)).pCoreIn 2 = B.pCoreIn 2 :=
  vertex_core_eq_kernel_core B (B ⊓ C) T (le_inf (map_subtype_le _) hTC)

/-- F.7.7(1), including the prime-to-two residual equality. `IsPReduced`
means that V is normal elementary abelian and B/C_B(V) has trivial two-core;
the remaining F.7.6 centralizer equality is supplied separately. -/
theorem lemma_F_7_7_one (B C : Subgroup G) [Finite B]
    (V : Subgroup B) (hV : IsPReduced 2 V) (T : Sylow 2 B)
    (hTC : (T : Subgroup B).map B.subtype ≤ C)
    (hCT : (T : Subgroup B) ⊓ centralizer (V : Set B) =
      (centralizer (V : Set B)).pCoreIn 2) :
    (primeToResidual 2 (centralizer (V : Set B))).map
        (B.subtype.comp (centralizer (V : Set B)).subtype) =
        (localKernel B (B ⊓ C)).pCoreIn 2 ∧
      (localKernel B (B ⊓ C)).pCoreIn 2 = B.pCoreIn 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := kernel_core_eq_vertex_core B C T hTC
  refine ⟨?_, hk⟩
  rw [hk, ← map_map, reduced_centralizer_residual V hV T hCT]
  rfl

end CFSG.Quasithin.ChapterF.LocalCores
