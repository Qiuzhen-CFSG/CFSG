module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.Transfer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import Theory.Representation.BinaryOffender.EquivariantOffender


/-!
# The projective L₃(4) exclusion on U_H/V₁

This is the conditional projective step in alternative (b) of 13.8.20.
The module is the actual H-conjugate span of V₃ modulo V₁, and its action
agrees with conjugation on representatives. The only quotient normality
required for this carrier is normality of V₁ inside U_H.

F.9.18(2),(3) supplies a nontrivial quadratic elementary actor A ≤ T*,
faithful on K*, with fixed codimension at most twice its binary rank.
Restriction to K*T* preserves this rank and fixed space. Its quotient by
K* is a two-group, and its SQTK property follows from that of H by taking
the quotient by O₂(H) and then a subgroup. The transfer module constructs
the faithful irreducible image and proves its generalized-Fitting equality.

The arguments `hselect` and `hclass` are the precise remaining earlier
representation inputs: existence of the invariant-or-FF Irr⁺ member from
A.1.42 and F.9.18(4), and the bound for faithful component-irreducible actions
from B.4.2/B.4.5. They are not results of this file. In particular this
conditional implication does not complete 13.8.20; the exceptional-field
assembly must supply those inputs and finish its other branches.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.8.20, printed p.955 (PDF p.972), with F.9.18, pp.325--326,
A.1.40--42, pp.31--32, and B.4.2/B.4.5, pp.86--87.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The actual subgroup K*T* inside H/O₂(H). -/
abbrev localActor (H K T : Subgroup G) : Subgroup (Source.Hstar H) :=
  Source.starImage H K ⊔ Source.starImage H T

/-- K* viewed inside K*T*; normality is relative to this local actor. -/
abbrev localComponent (H K T : Subgroup G) : Subgroup (localActor H K T) :=
  (Source.starImage H K).subgroupOf (localActor H K T)

variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The genuine source representation. The denominator lies in U_H, and
compatibility is checked on every conjugated representative. Faithfulness is
the standing identification C_H(U_H/V₁) = O₂(H). -/
structure SourceAction where
  line_le : V₁ ≤ Source.UH H V₃
  seed_le : V₃ ≤ H
  representation : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)
  conjugation : IsSourceAction H V₃ V₁ representation
  faithful : Function.Injective representation

variable {H V₃ V₁}

/-- Conditional exclusion of the actual projective K* model. The marked
quadratic actor and its component faithfulness are the F.9.18(2),(3) inputs.
The earlier classification implications apply only after the faithful
irreducible action and its actual F* have been constructed. -/
theorem projective_exclusion_of_source_inputs
    {κ : GroupClass.{u}} {F : Type v} [Field F] [Finite F]
    (K T : Subgroup G) [(Source.starImage H K).Normal]
    (d : SourceAction H V₃ V₁) (hSQTK : IsSQTK κ H)
    (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (eK : Source.starImage H K ≃* PSL(3, F)) (hF : Nat.card F = 4)
    (A : Subgroup (Source.Hstar H)) (hAT : A ≤ Source.starImage H T)
    (hA : IsElementaryTwo A) (hq : IsQuadratic d.representation A)
    (hc : fixedCodim d.representation A ≤ 2 * rank A)
    (hAC : Disjoint A (centralizer (Source.starImage H K : Set (Source.Hstar H))))
    (hselect : InvariantOrFF (d.representation.comp (localActor H K T).subtype)
      (localComponent H K T))
    (hclass : IrreducibleProjectiveBound κ F) : False := by
  let J := localActor H K T
  let L := localComponent H K T
  let τ := d.representation.comp J.subtype
  let B := A.subgroupOf J
  have hAJ : A ≤ J := hAT.trans le_sup_right
  have hmap : B.map J.subtype = A := map_subgroupOf_eq_of_le hAJ
  let : L.Normal := inferInstance
  have hSQ : IsSQTK κ (Source.Hstar H) := by
    refine ⟨?_, hSQTK.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hSQTK.stronglyQuasithin p hp ho)
  have hTs : IsPGroup 2 (Source.starImage H T) :=
    (hT.of_equiv (subgroupOfEquivOfLe hTH).symm).map _
  have hsup : (Source.starImage H T).subgroupOf J ⊔ L = ⊤ := by
    change (Source.starImage H T).subgroupOf J ⊔
      (Source.starImage H K).subgroupOf J = ⊤
    rw [← subgroupOf_sup (show Source.starImage H T ≤ J from le_sup_right)
      (show Source.starImage H K ≤ J from le_sup_left), sup_comm]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ L) := quotient_isPGroup_of_sup_eq_top
    ((Source.starImage H T).subgroupOf J) L hTs.comap_subtype hsup
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAJ⟩
    intro hb
    apply hA.1
    rw [← hmap, hb, Subgroup.map_bot]
  have hqB : IsQuadratic τ B := by
    intro a ha b hb w
    exact hq a ha b hb w
  have hrank : rank B = rank A :=
    congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv)
  have hcB : fixedCodim τ B ≤ 2 * rank B := by
    have hfix : fixedSpace τ B = fixedSpace d.representation A := by
      change fixedSpace (d.representation.comp J.subtype) B = _
      rw [fixedSpace_comp_map, hmap]
    rw [fixedCodim, hfix, hrank]
    exact hc
  have hBC : Disjoint B (centralizer (L : Set J)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    apply disjoint_iff_inf_le.mp hAC
    refine ⟨hx.1, ?_⟩
    apply mem_centralizer_iff.mpr
    intro k hk
    exact congrArg Subtype.val ((mem_centralizer_iff.mp hx.2)
      (⟨k, (show Source.starImage H K ≤ J from le_sup_left) hk⟩ : J) hk)
  exact projective_exclusion_of_representation_inputs τ L (hSQ.subgroup J) hquot
    B hB hqB hcB hBC
    ((subgroupOfEquivOfLe (show Source.starImage H K ≤ J from le_sup_left)).trans eK)
    hF hselect hclass
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective
