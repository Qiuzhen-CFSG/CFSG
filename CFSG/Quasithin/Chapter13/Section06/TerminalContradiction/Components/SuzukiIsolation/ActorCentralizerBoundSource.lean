module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelBoundSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelJankoFour
public import Theory.Representation.Suzuki.JankoFourActorBound
/-!
# Centralizer bounds on the same original elementary actor

Conjugation on the Suzuki image has kernel C_B(D), literally the centralizer
restricted to B. Thus the original actor's exceptional automorphism injection
gives the exact subgroup-cardinality bound used by the Steinberg coordinate
theorem: 256 for PSL₃(4)/M₂₃, and 2048 for J₄. The J₄ bound uses elementary
abelianness, not the order of a general two-subgroup.

The source adapters construct the injection from the original A₅ context and
two actual components before uniqueness. No kernel/image premise remains.
Source: Aschbacher–Smith 13.6.26–27, printed pp.934–935.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
variable {X : Type*} [Group X]

/-- This is an equality of subgroups of the original actor B. -/
theorem kernel_eq_centralizer_subgroupOf (D B : Subgroup X) [D.Normal] :
    ((MulAut.conjNormal : X →* MulAut D).comp B.subtype).ker =
      (centralizer (D : Set X)).subgroupOf B := by
  rw [← MonoidHom.comap_ker, MulAut.conjNormal_ker_eq_centralizer]
  rfl

/-- The same actor centralizer has order at most 256 from its faithful
exceptional action and an actual PSL₃(4) or M₂₃ marking. -/
theorem centralizer_card_le_256_of_injective {K : Type*} [Group K]
    (D B : Subgroup X) [D.Normal] (hB : IsPGroup 2 B)
    (f : ((MulAut.conjNormal : X →* MulAut D).comp B.subtype).ker →* MulAut K)
    (hf : Function.Injective f)
    (hmodel : Nonempty (K ≃* Matrix.PSL3Four.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M23)) :
    Nat.card ((centralizer (D : Set X)).subgroupOf B) ≤ 256 := by
  rw [← kernel_eq_centralizer_subgroupOf]
  exact root_kernel_card_le_256_of_exceptional_action hB _ f hf hmodel

/-- In the J₄ row the elementary kernel has at most 2048 elements. -/
theorem centralizer_card_le_2048_of_jankoFour_injective {K : Type*} [Group K]
    [IsSimpleGroup K] [Group.IsPerfect K]
    (D B : Subgroup X) [D.Normal] [IsElementaryAbelian 2 B]
    (f : ((MulAut.conjNormal : X →* MulAut D).comp B.subtype).ker →* MulAut K)
    (hf : Function.Injective f) (e : K ≃* Janko4.Model) :
    Nat.card ((centralizer (D : Set X)).subgroupOf B) ≤ 2048 := by
  rw [← kernel_eq_centralizer_subgroupOf]
  let φ := (MulAut.conjNormal : X →* MulAut D).comp B.subtype
  let : IsElementaryAbelian 2 φ.ker :=
    IsElementaryAbelian.of_injective φ.ker.subtype φ.ker.subtype_injective
  exact Representation.SuzukiSmallDegree.elementary_jankoFour_automorphism_card_le e f hf

open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K D : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) (hD : D.IsCComponent) (hne : D ≠ K)
    [K.Normal] [D.Normal]
    (B : Subgroup ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))))
include d hCv houtside hcounter hK hD hne

/-- The literal source kernel bound for the two ordinary exceptional rows. -/
theorem centralizer_card_le_256_of_context
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hB : IsPGroup 2 B)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) :
    let H := centralizer (V₁ : Set G)
    let Db := D.map (QuotientGroup.mk' (pCore 2 H))
    Nat.card ((centralizer (Db : Set (H ⧸ pCore 2 H))).subgroupOf B) ≤ 256 := by
  let := d.elementary
  dsimp only
  rw [← kernel_eq_centralizer_subgroupOf]
  exact kernel_card_le_256_of_context d hCv houtside hcounter hK hc hD hne B hB hmodel

/-- The original J₄ source row gives the 2048 bound required by the common
Steinberg-fixation theorem on the same elementary subgroup B of H*. -/
theorem centralizer_card_le_2048_of_context_jankoFour
    [IsQuasisimple (K ⧸ pCore 2 K)] [IsElementaryAbelian 2 B]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) :
    let H := centralizer (V₁ : Set G)
    let Db := D.map (QuotientGroup.mk' (pCore 2 H))
    Nat.card ((centralizer (Db : Set (H ⧸ pCore 2 H))).subgroupOf B) ≤ 2048 := by
  let H := centralizer (V₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kb := K.map q
  let Db := D.map q
  let := pCore_isNilpotent (p := 2) (G := H)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := jankoFour_quotient_isSimple e
  let : IsSimpleGroup Kb := (cComponentTwoCoreQuotientEquiv hK).symm.isSimpleGroup
  let : Group.IsPerfect Kb := (hK.map_quotient (pCore 2 H)).perfect
  exact centralizer_card_le_2048_of_jankoFour_injective Db B (action Kb Db B)
    (jankoFour_kernel_injective_of_context d hCv houtside hcounter hK e hD hne B)
    ((cComponentTwoCoreQuotientEquiv hK).symm.trans e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
