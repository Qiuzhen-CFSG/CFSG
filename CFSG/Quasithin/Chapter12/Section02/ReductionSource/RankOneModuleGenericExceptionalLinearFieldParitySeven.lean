module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementSeven
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddQuotient

/-!
# The order-seven displacement calculation on the chosen module

The completed residual producer supplies the literal product H/O₂(H) × A.
On a homogeneous invariant section with a faithful constituent irreducible
under F*(H/O₂(H)), the order-seven Cartan forces three independent copies.
H.4.7 contributes three dimensions on each copy, giving displacement at
least nine on the original U/Z₁.

The section is an explicit input, not a consequence asserted by this file.
Its selection (including passage to a constituent stabilizer when required),
source 5.1.16(2), and global TI/F.8 geometry remain with the final parity
owner qt-d-1222-linear-field-parity. Thus this is a checked conditional
calculation, not the unconditional source parity theorem.
Source: Aschbacher–Smith 5.1.17, printed p.641, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G}
  {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  (D : ChosenModule T L V)
include D

/-- The actual source quotient product supports the three-copy calculation. -/
theorem rankOne_degree_three_homogeneous_section_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (s : Seed T L H A 3) :
    ∃ e : ((H ⧸ pCore 2 H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)),
      (∀ (x : H) (a : A),
        e (QuotientGroup.mk' (pCore 2 H) x, a) =
          QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
            ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩) ∧
      ∀ (ρ : Representation (ZMod 2)
          ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X),
        BinaryConjugationSection (H ⊔ A) (setup T L s.V H A).U
          (setup T L s.V H A).V₁
          (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))) →
        ∀ (P : Subrepresentation ρ)
          (I : Subrepresentation (residualFactorAction e P.toRepresentation)),
          IsIrreducible I.toRepresentation →
          Homogeneous.homogeneousPart I ⊤ = ⊤ →
          Function.Injective I.toRepresentation →
          IsIrreducible (I.toRepresentation.comp
            (generalizedFitting (H ⧸ pCore 2 H)).subtype) →
          ∀ y, y ∈ H → y ^ 2 ∈ H.pCoreIn 2 → y ∉ H.pCoreIn 2 →
            9 ≤ displacement (setup T L s.V H A) y := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide) hpsl
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  obtain ⟨e,he⟩ := odd_join_quotient_product hi hH c (by decide) hm hnf hlinear
  refine ⟨e,he,?_⟩
  intro ρ coordinates P I hI hh hf hir y hy hy2 hne
  exact degree_three_homogeneous_section_displacement s D.sylow_normalizes_component
    hpsl hH.1.1.2 hlinear c e he ρ coordinates P I hI hh hf hir hy hy2 hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
