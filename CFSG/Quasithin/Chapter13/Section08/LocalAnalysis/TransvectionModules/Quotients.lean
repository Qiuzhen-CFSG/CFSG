module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Irreducible
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets

/-!
# Quotient-map constructions for 13.8.6

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948, Lemma 13.8.6(4)–(5).

The five-dimensional branch has U₁ = C_{U_H}(K) and U₀ = ⟨U₁^L⟩.
From the local seed index, commutator bounds and the marked parabolic,
we construct an equivariant surjection from the actual coset permutation
module onto U₀/V. The conjugation action descends through the specified
normal actor kernel. An equivariant coset identification with the fifteen
unordered pairs of six letters proves that the source module has rank 15.
The containment V ≤ U₀ ≤ U_L is included explicitly.

These are conditional local-data constructions. The natural/cover model
calculations establishing the seed index and commutator bound remain to be
proved for the source setup. The irreducible-quotient helper retains the
two local actions needed in the four-dimensional branch; their source
identifications and the genuine Steinberg recognition are not asserted by
this module. In particular this is not yet a proof of both source clauses.
-/

@[expose] public section

open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients
open BinaryPermutation.SixPairsQuadratic
variable {A : Type*} [Group A]

/-- There are fifteen unordered pairs of six letters. -/
theorem pair_card : Fintype.card Pair = 15 := by decide

/-- The actual pair-stabilizer coset module has dimension fifteen. -/
theorem coset_finrank_fifteen (f : A →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val)
    (S : Subgroup A) [Fintype (A ⧸ S)] (s : Pair)
    (hS : ∀ a, a ∈ S ↔ pairPerm (f a) s = s) :
    Module.finrank (ZMod 2) (BinaryPermutation.Full (A ⧸ S)) = 15 := by
  rw [Module.finrank_pi]
  exact (Fintype.card_congr (pairCosets f hf S s hS)).trans pair_card

variable {G : Type*} [Group G]

/-- Construct the literal U₀/V permutation quotient with its conjugation
formula and the equivariant fifteen-point coset identification. The local
seed and marking premises must be supplied by the source module analysis. -/
theorem U0_permutation_surjection_of_local_data
    (L H K T L₁ V₃ V V₁ : Subgroup G)
    [(V.subgroupOf (Source.U0 L H K V₃)).Normal]
    [IsElementaryAbelian 2 (Source.U0section L H K V₃ V)]
    (N : Subgroup ↥(L ⊔ T)) [N.Normal]
    [Fintype ((↥(L ⊔ T) ⧸ N) ⧸
      ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N))]
    (hV : V = conjugateSpanBy V₁ L) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hcentral : V₁ ≤ centralizer (K : Set G))
    (hU0norm : L ⊔ T ≤ normalizer (Source.U0 L H K V₃ : Set G))
    (hVnorm : L ⊔ T ≤ normalizer (V : Set G))
    (hkill : ⁅Source.U0 L H K V₃, N.map (L ⊔ T).subtype⁆ ≤ V)
    (hindex : V.relIndex (Source.U1 H K V₃) = 2)
    (hcomm : ⁅L₁ ⊔ T, Source.U1 H K V₃⁆ ≤ V₁)
    (f : (↥(L ⊔ T) ⧸ N) →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val)
    (s : Pair)
    (hstab : ∀ a, a ∈ ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N) ↔
      pairPerm (f a) s = s) :
    V ≤ Source.U0 L H K V₃ ∧ Source.U0 L H K V₃ ≤ Source.UL L H V₃ ∧
      ∃ ρ : Representation (ZMod 2) (↥(L ⊔ T) ⧸ N) (Additive (Source.U0section L H K V₃ V)),
        SectionConjugationAlong (L ⊔ T) (Source.U0 L H K V₃) V
          (QuotientGroup.mk' N) hU0norm ρ ∧
        ∃ e : ((↥(L ⊔ T) ⧸ N) ⧸
          ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N)) ≃ Pair,
          (∀ a c, e (a • c) = pairPerm (f a) (e c)) ∧
          Module.finrank (ZMod 2) (BinaryPermutation.Full ((↥(L ⊔ T) ⧸ N) ⧸
            ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N))) = 15 ∧
          ∃ q : Representation.IntertwiningMap
            ((BinaryPermutation.representation ((↥(L ⊔ T) ⧸ N) ⧸
              ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N))).comp
              (MulAction.toPermHom (↥(L ⊔ T) ⧸ N) ((↥(L ⊔ T) ⧸ N) ⧸
                ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (QuotientGroup.mk' N)))) ρ,
            Function.Surjective q := by
  have hV₁V : V₁ ≤ V := hV.symm ▸ le_conjugateSpanBy V₁ L
  obtain ⟨ρ, hρ⟩ := exists_section_representation (L ⊔ T)
    (Source.U0 L H K V₃) V N hU0norm hVnorm hkill
  refine ⟨Source.V_le_U0 L H K V₃ V V₁ hV hV₁ hcentral,
    Source.U0_le_UL L H K V₃, ρ, hρ,
    pairCosets f hf _ s hstab, pairCosets_equivariant f hf _ s hstab,
    coset_finrank_fifteen f hf _ s hstab, ?_⟩
  exact permutation_surjection_of_conjugate_span (L ⊔ T)
    (Source.U0 L H K V₃) (Source.U1 H K V₃) L (L₁ ⊔ T) V
    (QuotientGroup.mk' N) hU0norm le_sup_left rfl hindex (hcomm.trans hV₁V) ρ hρ

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients

end
