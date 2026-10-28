module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import CFSG.Quasithin.Chapter13.Section07.PlusOffenders

/-!
# Kernel control on the original plus-module offender action

The representation and both best offenders are the literal ones constructed
in 13.7.12. Its full lifted kernel C has C_C(U0)=QH. Every nontrivial
subnormal two-perfect subgroup of that same kernel moves U0, with the
source commutator lying in its own two-core; its kernel on U0 is exactly
that two-core. This applies the calculations (!) and (*) of 13.7.4 to
the actual source module and quotient maps.

These constraints do not assert C=QH. The remaining component and odd-core
exclusions in printed pp.937--938 are needed for full plus faithfulness.
Source: Aschbacher--Smith 13.7.4(1), 13.7.9(3), 13.7.12(3), pp.936--942.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

/-- Original-source application of (!) and (*) to any one of the actual
section actions constructed by central duality or the plus offender theorem. -/
theorem source_plus_kernel_structure
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W}
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    let U := Section08.Source.UH H V₃
    let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
    let C := (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype
    C ⊓ centralizer (U₀ : Set G) = H.pCoreIn 2 ∧
    ∀ K : Subgroup G, K ≤ C → (K.subgroupOf H).IsSubnormal →
      K ⊓ centralizer (U₀ : Set G) = K.pCoreIn 2 ∧
      (IsPPerfect 2 K → K ≠ ⊥ →
        ⁅U, K⁆ = ⁅U₀, K⁆ ∧ ⁅U₀, K⁆ ≠ ⊥ ∧
        ⁅U₀, K⁆ ≤ K.pCoreIn 2 ∧ K.pCoreIn 2 ≤ H.pCoreIn 2 ∧
        K.pCoreIn 2 ≤ centralizer (U₀ : Set G)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have he := PlusAction.section_action_kernel (D := F) s
  change (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype =
    PlusAction.kernel F at he
  dsimp only
  rw [he]
  exact ⟨PlusAction.kernel_fixedLayer_centralizer h, fun K hK hn =>
    ⟨PlusAction.subnormal_fixedLayer_centralizer h hK hn, fun hp hne =>
      PlusAction.subnormal_kernel_structure h hK hn hp hne⟩⟩

include d in
/-- The actual13.7.12(3) plus action and best offenders, with the two
kernel calculations of13.7.4 proved on those same source coordinates. -/
theorem exists_source_plus_FF_kernel_control
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g)) ^ 2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃ ∧
      let U := Section08.Source.UH H V₃
      let QH := H.pCoreIn 2
      let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
      let U₀ := U ⊓ centralizer (QH : Set G)
      let HC := Section08.Source.HC H V₃
      let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
      let Ug := conjugate U (g : G)
      let π := QuotientGroup.mk' (pCore 2 H)
      ∃ hE : IsElementaryAbelian 2 U, letI := hE;
        ∃ (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ U₀.subgroupOf U)))
          (sU : Representation.BinaryConjugationSection H U U₀ (σ.comp π))
          (sQ : Representation.BinaryConjugationSection H QH HC (Representation.dual (σ.comp π))),
          (∀ (q : QH) (u : U),
            (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔ ⁅(q : G), (u : G)⁆ = 1) ∧
          (∀ u : U, (sU.coordinates u).toAdd =
            Additive.ofMul (QuotientGroup.mk' (U₀.subgroupOf U) u)) ∧
          IsFFModule σ ∧
          (∃ B ≤ (A.subgroupOf H).map π, IsBestOffender σ B) ∧
          (∃ B ≤ (Ug.subgroupOf H).map π, IsBestOffender σ B) ∧
          let C := (σ.comp π).ker.map H.subtype
          C ⊓ centralizer (U₀ : Set G) = QH ∧
          ∀ K : Subgroup G, K ≤ C → (K.subgroupOf H).IsSubnormal →
            K ⊓ centralizer (U₀ : Set G) = K.pCoreIn 2 ∧
            (IsPPerfect 2 K → K ≠ ⊥ →
              ⁅U, K⁆ = ⁅U₀, K⁆ ∧ ⁅U₀, K⁆ ≠ ⊥ ∧
              ⁅U₀, K⁆ ≤ K.pCoreIn 2 ∧ K.pCoreIn 2 ≤ QH ∧
              K.pCoreIn 2 ≤ centralizer (U₀ : Set G)) := by
  obtain ⟨g, hs, hspan, hout, hE, σ, sU, sQ, hpair, hcoord, hff, hA, hUg⟩ :=
    exists_source_plus_FF d h hU hV
  let := hE
  exact ⟨g, hs, hspan, hout, hE, σ, sU, sQ, hpair, hcoord, hff, hA, hUg,
    source_plus_kernel_structure h sU⟩

end CFSG.Quasithin.Chapter13.Section07
