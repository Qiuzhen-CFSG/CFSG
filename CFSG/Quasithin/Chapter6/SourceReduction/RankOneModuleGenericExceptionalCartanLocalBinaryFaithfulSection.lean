module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryFrattini
public import Theory.Representation.Triality.PerfectCoreQuotientDegree

/-!
# A faithful triality section of the retained binary kernel

Write X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, E = U intersect O₂(X), and N = ⟨Eˣ⟩.
The existing nontrivial component action on N/Φ(N) has a nontrivial
irreducible section, since C is perfect. The two-core acts trivially on
this section and simplicity makes its quotient action faithful. The
actual section, component conjugation and quotient marking are retained.

The genuine binary-triality seven-plane calculation gives dimension at
least twenty-four on this section. Hence the SAME N/Φ(N) has order at
least 2^24, sharpening the previous thirteen-element bound. This neither
identifies N with U nor assumes a splitting or core-free original action.
The large-span exclusion and exceptional-component witness remain open.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and G.9.3,
printed p.356, refs/quasithin.pdf. Irreducible section extraction and
Burnside's Frattini kernel are implemented in PerfectCoreQuotientDegree.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

/-- The actual Frattini action has a faithful irreducible binary-triality section. -/
theorem original_binary_triality_kernel_faithful_section
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
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
        24 ≤ Module.finrank (ZMod 2) (V ⧸ D.toSubmodule) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨_,_,hNQ,_,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 X).to_le hNQ
  let : Fact (IsPGroup 2 N) := ⟨hN⟩
  let : IsElementaryAbelian 2 (N ⧸ frattini N) := isElementaryAbelian_quotient_frattini
  let := hC.perfect
  obtain ⟨a,ha,_,hd,_⟩ := original_binary_triality_kernel_frattini_action
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  refine ⟨hN,a,e,ha,?_⟩
  exact Triality.SevenPlaneDegree.exists_faithful_core_quotient_section e
    (MulAut.binaryRepresentation ((quotientAut (frattini N)).comp a))
    (MulAut.binaryRepresentation_nontrivial _ hd)

/-- The same retained Frattini quotient has at least 2^24 elements. -/
theorem original_binary_triality_kernel_frattini_twentyfour
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
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
    2^24 ≤ Nat.card (N ⧸ frattini N) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨_,_,hNQ,_,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 X).to_le hNQ
  obtain ⟨a,_,ha,_,_⟩ := original_binary_triality_kernel_frattini_action
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  let := hC.perfect
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  exact MulAut.triality_frattini_card_ge e hN a ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
