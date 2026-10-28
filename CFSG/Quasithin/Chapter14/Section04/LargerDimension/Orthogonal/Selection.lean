module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Defs
public import Theory.Representation.BinaryPermutation.FiveConjugation
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.OrthogonalA5
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# The selected conjugate and the diagonal module in Lemma 14.4.9

This file isolates the two source constructions which are needed by the
extraspecial lift.  The geometric input is stated with the literal subgroups
and quotient maps used in the proof.  In particular, H is identified with
the centralizer of the distinguished involution, k is chosen in the first
singular-point centralizer, and the second choice produces an element
i = z^x in the conjugate subgroup while escaping the diagonal residual.

The model part retains the actual quotient X quotient V, an identification of its
actor with the alternating group on five letters, and the conjugation equation
on every representative.  The resulting FiveConjugation is therefore a
literal action certificate, rather than an abstract group-family tag.  Rank,
irreducibility and cubic fixed-space conclusions are exposed as conditional
transport lemmas for the model facts used by the source argument.

Source: Aschbacher--Smith, combined manuscript, Lemma 14.4.9, printed
pp.1009--1010; the diagonal module is the binary five-point module from B.3.
-/

@[expose] public section

noncomputable section

open Subgroup
open Representation
open Representation.BinaryOffender
open scoped Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal

universe u

variable {G : Type u} [Group G] [Finite G]

/-! ### The singular-point and conjugator data -/

/-- The source data before the final conjugator is chosen.  W1 is kept as
the actual centralizer C_U(V) and Kstar is the actual diagonal residual
which the selected involution must avoid.  The last field is the precise
source selection assertion (the singular F4 point argument supplies it); it
is deliberately an existential assertion about elements and not an
unconnected tag naming a family. -/
structure SingularPointData (U H : Subgroup G) (z : G) [IsExtraspecial 2 U] where
  hz : orderOf z = 2
  hU : U ≤ H
  hH : H = centralizer ({z} : Set G)
  V : Subgroup G
  V_le_U : V ≤ U
  /-- The singular F₄-point subgroup has the four-point order used in the
  extraspecial quotient.  This is the numerical part of 14.4.8(1). -/
  V_card : Nat.card V = 4
  W1 : Subgroup G
  W1_eq : W1 = U ⊓ centralizer (V : Set G)
  g : G
  Kstar : Subgroup G
  k : G
  k_mem_W1 : k ∈ W1
  k_order : orderOf k = 2
  exists_conjugator :
    ∃ x i : G, i = conjugateElement z x ∧
      Kstar = diagonalResidual H i ∧ i ∈ conjugateCore W1 g ∧ i ∉ Kstar

/-- The output of the singular-point argument.  All fields refer to the
literal ambient elements, so downstream lift proofs can use the selected
x without changing the exponent convention. -/
structure SelectedInvolution (U H : Subgroup G) (z : G) [IsExtraspecial 2 U] where
  V : Subgroup G
  W1 : Subgroup G
  g : G
  k : G
  x : G
  i : G
  Kstar : Subgroup G
  hz : orderOf z = 2
  hU : U ≤ H
  hH : H = centralizer ({z} : Set G)
  V_le_U : V ≤ U
  V_card : Nat.card V = 4
  W1_eq : W1 = U ⊓ centralizer (V : Set G)
  k_mem_W1 : k ∈ W1
  k_order : orderOf k = 2
  i_eq : i = conjugateElement z x
  Kstar_eq : Kstar = diagonalResidual H i
  i_mem_conjugate : i ∈ conjugateCore W1 g
  i_not_Kstar : i ∉ Kstar
  /-- The selected conjugate is again an involution, proved from i_eq. -/
  hi : orderOf i = 2

omit [Finite G] in
/- The exponent-correct selected involution supplied by the singular-point
argument.  The proof of hi is the elementary conjugacy calculation; the
only non-formalized source step is isolated in exists_conjugator. -/
lemma select_involution
    (U H : Subgroup G) (z : G) [IsExtraspecial 2 U]
    (d : SingularPointData U H z) :
    Nonempty (SelectedInvolution U H z) := by
  obtain ⟨x, i, hix, hkstar, himem, hiout⟩ := d.exists_conjugator
  have hi : orderOf i = 2 := by
    rw [hix]
    simpa only [conjugateElement, MulEquiv.orderOf_eq] using d.hz
  exact ⟨{
    V := d.V
    W1 := d.W1
    g := d.g
    k := d.k
    x := x
    i := i
    Kstar := d.Kstar
    hz := d.hz
    hU := d.hU
    hH := d.hH
    V_le_U := d.V_le_U
    V_card := d.V_card
    W1_eq := d.W1_eq
    k_mem_W1 := d.k_mem_W1
    k_order := d.k_order
    i_eq := hix
    Kstar_eq := hkstar
    i_mem_conjugate := himem
    i_not_Kstar := hiout
    hi := hi }⟩

omit [Finite G] in
lemma selected_involution_order
    (U H : Subgroup G) (z : G) [IsExtraspecial 2 U]
    (_d : SingularPointData U H z)
    (s : SelectedInvolution U H z) :
    orderOf s.i = 2 :=
  s.hi

omit [Finite G] in
lemma selected_involution_centralizer
    (U H : Subgroup G) (z : G) [IsExtraspecial 2 U]
    (_d : SingularPointData U H z)
    (s : SelectedInvolution U H z) :
    H = centralizer ({z} : Set G) :=
  s.hH

/-! ### The two quotient maps retained by the source -/

/-- The actual `Ũ = U / Z(U)` quotient carrier. -/
abbrev centralBinaryQuotient (U : Subgroup G) := U ⧸ center U

/-- The quotient map from the extraspecial subgroup to `Ũ`. -/
noncomputable def centralBinaryQuotientMap (U : Subgroup G) :
    U →* centralBinaryQuotient U :=
  QuotientGroup.mk' (center U)

/-- The actual relative quotient `H / U`, with `U` viewed inside `H`. -/
abbrev relativeQuotient (H U : Subgroup G)
    [_hU : (U.subgroupOf H).Normal] := H ⧸ U.subgroupOf H

/-- The quotient map `H → H / U` used by the source actor. -/
noncomputable def relativeQuotientMap (H U : Subgroup G)
    [_hU : (U.subgroupOf H).Normal] : H →* relativeQuotient H U :=
  QuotientGroup.mk' (U.subgroupOf H)

omit [Finite G] in
@[simp] theorem relativeQuotientMap_apply (H U : Subgroup G)
    [_hU : (U.subgroupOf H).Normal] (h : H) :
    relativeQuotientMap H U h = QuotientGroup.mk' (U.subgroupOf H) h := rfl

/-! ### The literal diagonal residual and its model -/

omit [Finite G] in
lemma diagonalResidual_le_H (H : Subgroup G) (i : G) :
    diagonalResidual H i ≤ H := by
  exact (map_subtype_le _).trans inf_le_left

/- The source writes this subgroup as `K₀ = O²(C_H(i))`.  We retain the
ambient subgroup equality rather than replacing it by a name for an abstract
isomorphism type. -/
structure DiagonalResidualData (H : Subgroup G) (i : G) where
  K₀ : Subgroup G
  K₀_eq : K₀ = diagonalResidual H i
  K₀_le_H : K₀ ≤ H
  /-- The image denoted `K₀*` in the source quotient `H / O₂(H)`. -/
  K₀star : Subgroup (coreQuotient H)
  K₀star_eq : K₀star =
    (K₀.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  /-- The diagonal section is identified with the natural `SL₂(4)` model. -/
  model : Nonempty (K₀star ≃* Representation.SL2FourNatural.SL)

omit [Finite G] in
lemma DiagonalResidualData.k0_literal
    (H : Subgroup G) (i : G) (d : DiagonalResidualData H i) :
    d.K₀ = twoResidual (H ⊓ centralizer ({i} : Set G)) := by
  exact d.K₀_eq

omit [Finite G] in
lemma DiagonalResidualData.k0_le_H
    (H : Subgroup G) (i : G) (d : DiagonalResidualData H i) :
    d.K₀ ≤ H := by
  rw [d.K₀_eq]
  exact diagonalResidual_le_H H i

omit [Finite G] in
lemma DiagonalResidualData.k0star_literal
    (H : Subgroup G) (i : G) (d : DiagonalResidualData H i) :
    d.K₀star = (d.K₀.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) :=
  d.K₀star_eq

/- The comparison used when passing a centralizer through a quotient map is
the standard subgroup inclusion.  Keeping it here records the actual image
set and leaves equality to the source hypotheses about its kernel. -/
omit [Finite G] in
lemma centralizer_image_comparison
    {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Set A) :
    Subgroup.map f (centralizer S) ≤ centralizer (f '' S) := by
  exact Subgroup.map_centralizer_le_centralizer_image S f

/-! ### Literal diagonal quotient and binary A5 coordinates -/

/-- Coordinates for the actual conjugation action of a quotient X quotient V.
The normal field is retained explicitly so construction does not rely on an
instance inferred from an unrelated subgroup. -/
structure DiagonalModuleData (X : Subgroup G) where
  V : Subgroup X
  normal : V.Normal
  coordinates : V ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  actor : (X ⧸ V) ≃* alternatingGroup (Fin 5)
  equivariant : ∀ (g : X) (v : V),
    coordinates ⟨g * v * g⁻¹, normal.conj_mem v v.property g⟩ =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5)
        (actor (QuotientGroup.mk' V g)).val (coordinates v).toAdd)

namespace DiagonalModuleData

variable {X : Subgroup G} (d : DiagonalModuleData (G := G) X)

/-- The literal quotient map to the A5 actor. -/
noncomputable def quotientMap : X →* alternatingGroup (Fin 5) :=
  letI : d.V.Normal := d.normal
  d.actor.toMonoidHom.comp (QuotientGroup.mk' d.V)

omit [Finite G] in
@[simp] theorem quotientMap_apply (x : X) (hV : d.V.Normal) :
    d.quotientMap x = d.actor
      ((@QuotientGroup.mk' (↥X) (inferInstance : Group (↥X)) d.V hV) x) := by
  change d.actor
      ((@QuotientGroup.mk' (↥X) (inferInstance : Group (↥X)) d.V d.normal) x) = _
  rfl

/-- Turning the source coordinates into the reusable conjugation certificate. -/
def toConjugation (d : DiagonalModuleData (G := G) X) (hV : d.V.Normal) :
    @BinaryPermutation.FiveConjugation (↥X) (inferInstance : Group (↥X)) d.V hV := by
  letI : d.V.Normal := hV
  exact {
    coordinates := d.coordinates
    actor := d.actor
    equivariant := d.equivariant }

omit [Finite G] in
theorem card : Nat.card d.V = 16 := by
  exact @BinaryPermutation.FiveConjugation.card (↥X)
    (inferInstance : Group (↥X)) d.V d.normal (toConjugation d d.normal)

end DiagonalModuleData

/-! ### The selected outer action on the moved section -/

/-- An action of the selected involution on the actual binary moved section.
outer is a linear endomorphism in the chosen coordinates; its moved-rank
field is the precise rank-four calculation for the diagonal (Frobenius-
adjugation) involution. -/
structure OuterBinaryActionData (X : Subgroup G) (d : DiagonalModuleData X) where
  x : X
  x_order : orderOf x = 2
  outer : BinaryPermutation.core (Fin 5) ≃ₗ[ZMod 2]
      BinaryPermutation.core (Fin 5)
  outer_equivariant : ∀ v : d.V,
    d.coordinates ⟨x * v * x⁻¹, d.normal.conj_mem v v.property x⟩ =
      Multiplicative.ofAdd (outer (d.coordinates v).toAdd)
  moved_rank_eq_four : Module.finrank (ZMod 2)
      (LinearMap.range (outer.toLinearMap - LinearMap.id)) = 4

omit [Finite G] in
/- The moved section has binary dimension four under the supplied outer
action. -/
lemma OuterBinaryActionData.moved_rank_four
    (X : Subgroup G) (d : DiagonalModuleData X)
    (o : OuterBinaryActionData X d) :
    Module.finrank (ZMod 2)
      (LinearMap.range (o.outer.toLinearMap - LinearMap.id)) = 4 :=
  o.moved_rank_eq_four

omit [Finite G] in
/- The selected element retains its involution order in the literal quotient
coordinates. -/
lemma OuterBinaryActionData.order_two
    (X : Subgroup G) (d : DiagonalModuleData X)
    (o : OuterBinaryActionData X d) : orderOf o.x = 2 :=
  o.x_order

/-! ### Transported model facts used by the source sieve -/

/- The binary core is irreducible for the literal alternating-five action.
The proof uses the finite invariant-submodule calculation, so the fact is
available independently of the ambient quotient identification. -/
set_option linter.style.haveILetI false in
theorem binary_core_irreducible :
    Representation.IsIrreducible
      ((BinaryPermutation.coreRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype) := by
  have hdim : 0 < Module.finrank (ZMod 2)
      (BinaryPermutation.core (Fin 5)) := by
    rw [BinaryPermutation.finrank_core]
    norm_num
  letI : Nontrivial (BinaryPermutation.core (Fin 5)) :=
    Module.nontrivial_of_finrank_pos hdim
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  rcases BinaryPermutation.SevenPointChiefFactor.fiveCore_simple P.toSubmodule
      (fun a v hv => P.apply_mem_toSubmodule a hv) with h | h
  · left
    exact Subrepresentation.toSubmodule_injective h
  · right
    exact Subrepresentation.toSubmodule_injective h

/-- A source action package records the invariant-subspace and cubic facts on
the actual actor.  The fields are equations for the literal action and hence
can be discharged by the A5 coordinate calculation without changing quotient
maps. -/
structure BinaryFiveActionFacts (X : Subgroup G) (d : DiagonalModuleData X) where
  irreducible :
    Representation.IsIrreducible
      ((BinaryPermutation.coreRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype)
  cubic : alternatingGroup (Fin 5)
  cubic_order : orderOf cubic = 3
  cubic_fixed_space : ∀ v : BinaryPermutation.core (Fin 5),
    v ∈ fixedSpace
      ((BinaryPermutation.coreRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype)
      BinaryPermutation.CubicFixedSpace.Five.klein →
      BinaryPermutation.coreRepresentation (Fin 5) cubic.val v = v

set_option linter.style.haveILetI false in
theorem standard_cubic_order :
    orderOf BinaryPermutation.CubicFixedSpace.Five.cycle = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime
    BinaryPermutation.CubicFixedSpace.Five.cycle_pow
    BinaryPermutation.CubicFixedSpace.Five.cycle_ne_one

/-- The standard cubic fixed-space calculation is available directly for the
actual permutation core.  This theorem is useful when the source actor
coordinates send its chosen cubic to cycle. -/
theorem standard_cubic_fixed_free
    (cubic : alternatingGroup (Fin 5))
    (hcubic : cubic = BinaryPermutation.CubicFixedSpace.Five.cycle) :
    ∀ v : BinaryPermutation.core (Fin 5),
      v ∈ fixedSpace
        ((BinaryPermutation.coreRepresentation (Fin 5)).comp
          (alternatingGroup (Fin 5)).subtype)
        BinaryPermutation.CubicFixedSpace.Five.klein →
      BinaryPermutation.coreRepresentation (Fin 5) cubic.val v = v := by
  subst cubic
  intro v hv
  exact BinaryPermutation.CubicFixedSpace.Five.cycle_fixes_core v hv

/-- The standard deleted-five-point package discharges the model clauses in
`BinaryFiveActionFacts`; only the source identification of the quotient actor
with these coordinates remains an input to the surrounding argument. -/
def standard_binary_five_action_facts
    (X : Subgroup G) (d : DiagonalModuleData X)
    (cubic : alternatingGroup (Fin 5))
    (hcubic : cubic = BinaryPermutation.CubicFixedSpace.Five.cycle) :
    BinaryFiveActionFacts X d := by
  refine {
    irreducible := binary_core_irreducible
    cubic := cubic
    cubic_order := by
      rw [hcubic]
      exact standard_cubic_order
    cubic_fixed_space := ?_ }
  exact standard_cubic_fixed_free cubic hcubic
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal

end
