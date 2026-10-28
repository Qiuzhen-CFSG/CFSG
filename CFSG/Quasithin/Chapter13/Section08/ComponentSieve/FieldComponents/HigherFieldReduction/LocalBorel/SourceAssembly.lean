module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.SourceAlternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Placement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization

/-!
# Source placement and complete Borel alternatives

The legitimate H = KL₁T reduction uses `Placement.Setup.reduced_mem_Hz`
and its setwise product theorem. Here the two actual component quotient
maps through K/O₂(K) construct the changed star equivalence, so model
transport needs no extra isomorphism hypothesis.

The source input below contains standing data and exact earlier results:
the higher-field component model, 13.8.16's generation, universal 13.8.13,
and the two assertions of 13.7.3(9). It contains no Borel conclusion.
The ordinary/covered natural actions give the order-three/order-nine
quotients of L₁ by O₂(L₁). These prove L₁T solvable; the model theorem
proves the intrinsic Borel solvable. Once L₁T normalizes the actual Borel,
13.8.13 places B in M and the full-product dichotomy applies, retaining
the actual Sylow inverter and the original exceptional outer actor.

The separate normalization module proves L₁T ≤ N_G(B) for all seven
higher-field models with n > 1. The new ordinary and covered source
contexts discharge this premise and give the full dichotomy with the
actual Sylow-centralizer inverter. Existing conditional contexts and
source assemblies remain unchanged. No stronger residual identity,
C ≤ K, or trivial O₂(H)-action is used.

Source: Aschbacher–Smith 13.2.1–2, 13.7.3(9), 13.8.13 and 13.8.16;
proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
open TorusModels.Assembly CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The change of ambient star quotient is constructed through K/O₂(K). -/
noncomputable def Placement.Setup.reducedStarEquiv {H K D T G₁ M : Subgroup G}
    [(Source.starImage H K).Normal] (s : Placement.Setup H K D T G₁ M) :
    Source.starImage H K ≃* Source.starImage s.reduced K :=
  (Components.componentStarEquiv H K s.component_le s.component_isComponent).symm.trans
    (Components.componentStarEquiv s.reduced K le_sup_left s.reduced_component)

/-- The reduced model needs no additional quotient-isomorphism premise. -/
theorem Placement.Setup.reduced_model_from_component {H K D T G₁ M : Subgroup G}
    [(Source.starImage H K).Normal] (s : Placement.Setup H K D T G₁ M)
    {n : ℕ} {unitary four : Bool}
    (model : Model.{u,v} (Source.starImage H K) n unitary four) :
    Model.{u,v} (Source.starImage s.reduced K) n unitary four :=
  s.reduced_model model s.reducedStarEquiv

private theorem solvable_of_three_power_core_quotient (D : Subgroup G)
    (r : ℕ) (hcard : Nat.card (D ⧸ pCore 2 D) = 3 ^ r) : Group.IsSolvable D := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (D ⧸ pCore 2 D) := IsPGroup.of_card hcard
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 D)).mpr
    ⟨@IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent,
      @IsNilpotent.to_isSolvable _ _ hp.isNilpotent⟩

private theorem solvable_base (D : Subgroup G) (T : Sylow 2 G)
    (hD : Group.IsSolvable D) (hn : (T : Subgroup G) ≤ normalizer (D : Set G)) :
    Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := D ⊔ (T : Subgroup G)
  let A := D.subgroupOf J
  let B := (T : Subgroup G).subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  let : Group.IsSolvable D := hD
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).injective
  let : Group.IsSolvable T := @IsNilpotent.to_isSolvable T _ T.isPGroup'.isNilpotent
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ J from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  rw [← subgroupOf_sup (show D ≤ J from le_sup_left) (show (T : Subgroup G) ≤ J from le_sup_right)]
  exact subgroupOf_self _

/-- Earlier source inputs after 13.8.16; no Borel conclusion is a field. -/
structure SourceInput (T : Sylow 2 G) (H K L V V₁ V₂ V₃ M G₁ : Subgroup G)
    [(Source.starImage H K).Normal] (n : ℕ) (unitary four : Bool) where
  standing : TransvectionRecognition.Component.ModelExtension.LocalSetup T L V V₁ V₂ V₃ M G₁
  member : H ∈ Source.Hz (one L (T : Subgroup G) V₁) (T : Subgroup G) G₁ M
  component_le : K ≤ H
  model : Model.{u,v} (Source.starImage H K) n unitary four
  degree : 1 < n
  generated : H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)
  universal : ∀ J : Subgroup G, one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤ J →
    J ≤ G₁ → Group.IsSolvable J → J ≤ M
  intersection : H ⊓ M = H ⊓ normalizer (V : Set G)
  theta : one L (T : Subgroup G) V₁ = closure {g : G | g ∈ H ⊓ M ∧ orderOf g = 3}

namespace SourceInput
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceInput.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
local notation "D" => one L (T : Subgroup G) V₁
local notation "X" => plus L (T : Subgroup G) V₁

include d in
theorem sylow_H : Chapter1.IsSylowIn 2 (T : Subgroup G) H := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.member.1.2
  refine ⟨T.subtype hTH, ?_⟩
  exact map_subgroupOf_eq_of_le hTH

noncomputable abbrev B : Subgroup G := borel H K (T : Subgroup G) d.component_le d.sylow_H

/-- Normalization is the remaining source geometry. All solvability and placement
inputs are discharged by the actual model and natural-action cardinality. -/
def context_of_normalizes (r : ℕ) (hcard : Nat.card (D ⧸ pCore 2 D) = 3 ^ r)
    (hn : D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G)) :
    SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four where
  standing := d.standing
  member := d.member
  component_le := d.component_le
  sylow_H := d.sylow_H
  model := d.model
  degree := d.degree
  generated := d.generated
  borel_in_M := by
    exact borel_le_M_of_normalizes H K (T : Subgroup G) D G₁ M
      d.component_le d.sylow_H d.member d.universal
      (Placement.model_normalizer_isSolvable d.model d.degree
        (sourceSylow H K (T : Subgroup G) d.sylow_H))
      (solvable_base D T (solvable_of_three_power_core_quotient D r hcard)
        (T_normalizes_one L (T : Subgroup G) V₁ d.standing.line_stable)) hn
  borel_normalized := hn
  intersection := d.intersection
  theta := d.theta

/-- The ordinary source context requires only the outstanding normalization. -/
def ordinaryContext (a : NaturalSetup L (T : Subgroup G) V V₁)
    (hn : D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G)) :
    SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four :=
  d.context_of_normalizes 1 (by simpa using source_residual_quotient_card a D rfl) hn

/-- The covered context uses full L₁ and its order-nine two-core quotient. -/
def coveredContext (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L)
    (hn : D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G)) :
    SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four :=
  d.context_of_normalizes 2 (by
    simpa using LocalAction.one_quotient_card L (T : Subgroup G) V₁
      a.normalizes_L a.line_stable hfactor a.zero_core_card (a.plus_core_card hfactor)) hn

variable [(K.subgroupOf H).Normal]

/-- The ordinary source assembly, with only Borel normalization left open. -/
theorem sylowBorelAlternative_ordinary_of_normalizes (a : NaturalSetup L (T : Subgroup G) V V₁)
    (hn : D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G)) :
    d.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient D t.val ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) D
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, d.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := d.ordinaryContext a hn
  exact ⟨c.borel_in_M, c.exists_sylowBorelAlternative_ordinary a⟩

/-- The covered source assembly retains X=L₁,+ and the zero-direction fixation. -/
theorem sylowBorelAlternative_covered_of_normalizes (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L)
    (hn : D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G)) :
    d.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient X t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) X
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, d.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := d.coveredContext a hfactor hn
  exact ⟨c.borel_in_M, c.exists_sylowBorelAlternative_covered a hfactor⟩

/-- The actual solvable local group normalizes the constructed Borel in
all seven models; no normalization or placement conclusion is assumed. -/
theorem borel_normalized (r : ℕ) (hcard : Nat.card (D ⧸ pCore 2 D) = 3 ^ r) :
    D ⊔ (T : Subgroup G) ≤ normalizer (d.B : Set G) := by
  let : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) :=
    solvable_base D T (solvable_of_three_power_core_quotient D r hcard)
      (T_normalizes_one L (T : Subgroup G) V₁ d.standing.line_stable)
  exact Normalization.source_borel_normalized H K D (T : Subgroup G)
    d.component_le (le_sup_left.trans d.member.1.2) (le_sup_right.trans d.member.1.2)
    d.sylow_H d.model d.degree

/-- The complete ordinary source context, with Borel normalization and
placement derived from the actual order-three local quotient. -/
def ordinarySourceContext (a : NaturalSetup L (T : Subgroup G) V V₁) :
    SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four :=
  d.ordinaryContext a (d.borel_normalized 1 (by
    simpa using source_residual_quotient_card a D rfl))

/-- The complete covered source context, retaining full L₁ and its actual
elementary-nine quotient without an extra normalization premise. -/
def coveredSourceContext (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L) :
    SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four :=
  d.coveredContext a hfactor (d.borel_normalized 2 (by
    simpa using LocalAction.one_quotient_card L (T : Subgroup G) V₁
      a.normalizes_L a.line_stable hfactor a.zero_core_card (a.plus_core_card hfactor)))

/-- The full ordinary source dichotomy with the marked inverter. -/
theorem sylowBorelAlternative_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁) :
    d.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient D t.val ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) D
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, d.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := d.ordinarySourceContext a
  exact ⟨c.borel_in_M, c.exists_sylowBorelAlternative_ordinary a⟩

/-- The full covered source dichotomy retains the same prescribed actor,
the zero-direction fixation and the actual Sylow-centralizer inverter. -/
theorem sylowBorelAlternative_covered (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L) :
    d.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient X t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) X
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, d.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := d.coveredSourceContext a hfactor
  exact ⟨c.borel_in_M, c.exists_sylowBorelAlternative_covered a hfactor⟩

end SourceInput
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
