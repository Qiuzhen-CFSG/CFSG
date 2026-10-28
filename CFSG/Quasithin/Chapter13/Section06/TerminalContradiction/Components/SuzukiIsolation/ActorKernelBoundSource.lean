module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ExceptionalKernelBound
/-!
# The actual exceptional-actor kernel bound in the original A₅ context

Before component uniqueness, the actual quotient H* = C_G(V₁)/O₂(C_G(V₁))
has its exceptional and Suzuki component images as generalized Fitting
factors. The kernel of the full original actor A on the Suzuki factor injects
into the exceptional automorphism group. The intrinsic component marking
transports through its literal ambient two-core image and gives the bounds
128 in the M₂₃ case and 256 in the PSL₃(4) case.

The original prime-core results discharge the Fitting hypotheses; no faithful
summand, kernel injection, component uniqueness or 5.2.3 input remains here.
The root-coordinate owner identifies this kernel with the original root
projection kernel in the ensuing Steinberg action.
Source: Aschbacher–Smith 13.6.26–27, printed pp.934–935.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K D : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent)
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K)
    [K.Normal] [D.Normal]
    (A : Subgroup ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))))
    (hA : IsPGroup 2 A)
include d hCv houtside hcounter hK hc hD hne hA

/-- The M₂₃ component bounds the literal Suzuki-conjugation kernel by128. -/
theorem kernel_card_le_128_of_context_mathieu
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) :
    let H := centralizer (V₁ : Set G)
    let Db := D.map (QuotientGroup.mk' (pCore 2 H))
    Nat.card ((MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut Db).comp A.subtype).ker ≤ 128 := by
  let H := centralizer (V₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  exact Sporadic.Mathieu.m23_twoGroup_card_le_128_of_equiv
    ((cComponentTwoCoreQuotientEquiv hK).symm.trans e)
    (hA.to_subgroup _) (action (K.map q) (D.map q) A)
    (kernel_injective_of_context d hCv houtside hcounter hK hc hD hne A)

/-- The PSL₃(4) component bounds the same literal actor kernel by256. -/
theorem kernel_card_le_256_of_context_linear
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer (V₁ : Set G)
    let Db := D.map (QuotientGroup.mk' (pCore 2 H))
    Nat.card ((MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut Db).comp A.subtype).ker ≤ 256 := by
  let H := centralizer (V₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  exact Matrix.PSL3Four.twoGroup_card_le_256_of_equiv
    ((cComponentTwoCoreQuotientEquiv hK).symm.trans e)
    (hA.to_subgroup _) (action (K.map q) (D.map q) A)
    (kernel_injective_of_context d hCv houtside hcounter hK hc hD hne A)

/-- The two remaining source rows have a uniform kernel bound on the original
actor. Their exact intrinsic quotient markings are retained. -/
theorem kernel_card_le_256_of_context
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) :
    let H := centralizer (V₁ : Set G)
    let Db := D.map (QuotientGroup.mk' (pCore 2 H))
    Nat.card ((MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut Db).comp A.subtype).ker ≤ 256 := by
  rcases hmodel with h | h
  · obtain ⟨e⟩ := h
    exact kernel_card_le_256_of_context_linear d hCv houtside hcounter hK hc hD hne A hA e
  · obtain ⟨e⟩ := h
    exact (kernel_card_le_128_of_context_mathieu d hCv houtside hcounter hK hc hD hne A hA e).trans
      (by decide)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
