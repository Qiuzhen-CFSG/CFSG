module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FixedSeed
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.Representation.BinaryGroupAction

/-!
# Excluding the A7 four-space using the original fixed seed

A faithful binary four-space has no nonzero vector fixed by a subgroup
whose order is divisible by five. Restrict to an order-five subgroup and
use the orbit-counting theorem on sixteen elements. In the B.5.1 A7
four-space row, the proved cohomology theorem splits off the component
fixed space. Projecting the repaired L1-fixed vector to that row now
contradicts the order-five calculation.

The seed-order premise records a separate earlier subgroup-marking fact;
it is not a representation exclusion. The final theorem applies the
calculation to the actual chosen flag and the literal action quotient.
Source: Aschbacher--Smith, 11.4.2, printed p.777, using B.5.1 and I.1.6(8).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven

section Linear
variable {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

/-- Order five is already sufficient for the fixed-point comparison; no
classification of the embedding of A5 in A7 is needed here. -/
theorem fixedSpace_eq_bot_of_four (ρ : Representation (ZMod 2) Q W)
    (hfaith : Function.Injective ρ) (hd : Module.finrank (ZMod 2) W = 4)
    (B : Subgroup Q) (hfive : 5 ∣ Nat.card B) : fixedSpace ρ B = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hfive
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers,ha]
  let τ := (ρ.comp B.subtype).comp P.subtype
  have ht : Function.Injective τ :=
    hfaith.comp (B.subtype_injective.comp P.subtype_injective)
  let := BinaryGroupAction.action τ
  let := BinaryGroupAction.faithful τ ht
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (Multiplicative W) = 16 := by
    change Nat.card W = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    rfl
  have hmove : FixedPoints.subgroup P (Multiplicative W) ≠ ⊤ := by
    intro he
    have hp : ∀ p : P, p = 1 := by
      intro p
      apply FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative W)
      intro w
      have hw : w ∈ FixedPoints.subgroup P (Multiplicative W) := he.symm ▸ mem_top w
      exact (hw p).trans (one_smul P w).symm
    let : Subsingleton P := ⟨fun p q => (hp p).trans (hp q).symm⟩
    have hc : Nat.card P = 1 := Nat.card_unique
    omega
  have hzero := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hP hcard hmove
  apply bot_unique
  intro w hw
  have hw' : Multiplicative.ofAdd w ∈ FixedPoints.subgroup P (Multiplicative W) := by
    intro p
    exact congrArg Multiplicative.ofAdd (hw (p : B))
  have hz : Multiplicative.ofAdd w = 1 := Subgroup.mem_bot.mp (hzero ▸ hw')
  exact congrArg Multiplicative.toAdd hz

omit [Finite Q] [FiniteDimensional (ZMod 2) W] in
/-- In a split moved section, an original B-fixed vector outside the K-fixed
space supplies a nonzero B-fixed vector on the literal central quotient. -/
theorem exists_section_fixed_ne_zero
    (ρ : Representation (ZMod 2) Q W) (K B : Subgroup Q) (hBK : B ≤ K)
    (s : MovedSection ρ K) (hc : IsCompl s.space.toSubmodule (fixedSpace ρ K))
    (hv : ∃ v, v ∈ fixedSpace ρ B ∧ v ∉ fixedSpace ρ K) :
    ∃ w : s.space.toSubmodule ⧸ s.central.toSubmodule,
      w ≠ 0 ∧ w ∈ fixedSpace s.action B := by
  obtain ⟨v,hvB,hvK⟩ := hv
  have hvspan : v ∈ s.space.toSubmodule ⊔ fixedSpace ρ K := by
    rw [hc.codisjoint.eq_top]
    trivial
  obtain ⟨u,hu,c,hcK,rfl⟩ := Submodule.mem_sup.mp hvspan
  have huB : u ∈ fixedSpace ρ B := by
    intro b
    have hb := hvB b
    change ρ b (u + c) = u + c at hb
    have hbc : ρ (b : Q) c = c := hcK ⟨b,hBK b.property⟩
    rw [map_add, hbc] at hb
    exact add_right_cancel hb
  let w : s.space.toSubmodule := ⟨u,hu⟩
  refine ⟨s.central.toSubmodule.mkQ w,?_,?_⟩
  · intro hz
    have hw : w ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hw
    apply hvK
    exact (fixedSpace ρ K).add_mem (fun k => congrArg Subtype.val (hw k)) hcK
  · intro b
    change s.central.toSubmodule.mkQ (s.space.toRepresentation b w) =
      s.central.toSubmodule.mkQ w
    exact congrArg s.central.toSubmodule.mkQ (Subtype.ext (huB b))

/-- The actual A7 four-dimensional B.5.1 row contradicts a moving fixed seed.
Splitting is proved by A7 cohomology, rather than included as an extra premise. -/
theorem no_four_section_of_fixed_seed
    (ρ : Representation (ZMod 2) Q W) (K B : Subgroup Q) (hBK : B ≤ K)
    (hfive : 5 ∣ Nat.card B) (e : K ≃* alternatingGroup (Fin 7))
    (s : MovedSection ρ K) (hi : ExtensionConsequences.IrreducibleAlternative K s)
    (hv : ∃ v, v ∈ fixedSpace ρ B ∧ v ∉ fixedSpace ρ K) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 4 := by
  intro hd
  have hc := ExtensionConsequences.alternatingSeven_isCompl s hi e hd
  obtain ⟨w,hw,hfix⟩ := exists_section_fixed_ne_zero ρ K B hBK s hc hv
  rw [fixedSpace_eq_bot_of_four s.action hi.faithful hd B hfive] at hfix
  exact hw hfix

end Linear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The four-space exclusion on the original reduced conjugation action. -/
theorem no_four_section
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E) (hfive : 5 ∣ Nat.card (seedImage E))
    (s : MovedSection (action E) (componentImage E))
    (hi : ExtensionConsequences.IrreducibleAlternative (componentImage E) s) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 4 := by
  obtain ⟨e⟩ := hmodel.2
  exact no_four_section_of_fixed_seed (action E) (componentImage E) (seedImage E)
    (seedImage_le_componentImage E) hfive e s hi
    (exists_fixed_not_component_fixed E h hf hne hstar hcent)

/-- The chosen-flag consumer discharges 11.4.1's fixed-space assertion.
The seed order is retained for the earlier marked L1 quotient producer. -/
theorem ofFlag_no_four_section
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (hfive : 5 ∣ Nat.card (seedImage (ofFlag S f X z H)))
    (s : MovedSection (action (ofFlag S f X z H)) (componentImage (ofFlag S f X z H)))
    (hi : ExtensionConsequences.IrreducibleAlternative (componentImage (ofFlag S f X z H)) s) :
    Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 4 :=
  no_four_section _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hmodel hfive s hi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven
