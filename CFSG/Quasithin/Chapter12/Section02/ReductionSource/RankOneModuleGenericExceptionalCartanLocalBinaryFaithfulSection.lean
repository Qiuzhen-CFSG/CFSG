module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryFaithfulSection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# A faithful triality section for the original chosen-module configuration

The actual component conjugation on the retained span's Frattini quotient
has an irreducible subquotient with faithful binary-triality action. The
quotient marking agrees on every original component element. Thus the
same Frattini layer has order at least 2^24. These applications retain the
original chosen module, both Hall conditions and the full kernels.

The large-span exclusion and exceptional-component construction remain
open; the dimension bound alone is not a contradiction.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.635--638,795,
with the G.9.3 degree bound, printed p.356, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The same component has a faithful irreducible section with its literal quotient marking. -/
theorem rankOne_local_cartan_binary_triality_kernel_faithful_section
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    ∃ (hN : IsPGroup 2 N) (a : C →* MulAut N)
      (e : (C ⧸ pCore 2 C) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one),
      (∀ (c : C) (v : N), ((a c v : N) : G) =
        (c.val : G) * (v : G) * (c.val : G)⁻¹) ∧
      letI : Fact (IsPGroup 2 N) := ⟨hN⟩
      letI : IsElementaryAbelian 2 (N ⧸ frattini N) := isElementaryAbelian_quotient_frattini
      let ρ := MulAut.binaryRepresentation ((quotientAut (frattini N)).comp a)
      ∃ V : Subrepresentation ρ, ∃ D : Subrepresentation V.toRepresentation,
        ∃ σ : Representation (ZMod 2) (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)
          (V ⧸ D.toSubmodule),
        D.quotientRepresentation.IsIrreducible ∧ σ.IsIrreducible ∧
        Function.Injective σ ∧
        (∀ c, σ (e (QuotientGroup.mk' (pCore 2 C) c)) = D.quotientRepresentation c) ∧
        24 ≤ Module.finrank (ZMod 2) (V ⧸ D.toSubmodule) :=
  BinaryOmega.original_binary_triality_kernel_faithful_section
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The original retained Frattini layer has at least 2^24 elements. -/
theorem rankOne_local_cartan_binary_triality_kernel_frattini_twentyfour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    2^24 ≤ Nat.card (N ⧸ frattini N) :=
  BinaryOmega.original_binary_triality_kernel_frattini_twentyfour
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
