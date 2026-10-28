module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.FixedLine
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The faithful binary action used in 15.3.57–58

The vector space is the additive version of the literal `U/Z`. Its actor is
the literal `H/O₂(H)`, identified with the conjugation image by 15.3.48(3).
The formula on cosets proves that this representation is the source action.
Irreducibility is transferred from the fixed-line argument, including its
generation and nontriviality checks; no recognition statement is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1149.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition

variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The binary vector space in the source, without replacing its carrier. -/
abbrev Space := Additive (VectorQuotient Z ZS)

/-- The image of an ambient subgroup in the actual actor quotient. -/
def actorImage (A : Subgroup G) : Subgroup (ActorQuotient Z) :=
  (A.subgroupOf (centralizerH Z)).map (QuotientGroup.mk' _)

/-- The image of an ambient subgroup in the actual vector quotient. -/
def vectorImage (A : Subgroup G) : Subgroup (VectorQuotient Z ZS) :=
  (A.subgroupOf (closureU Z ZS)).map (QuotientGroup.mk' _)

/-- The faithful linear representation of the actor quotient, obtained from
the already constructed conjugation action and its exact kernel. -/
noncomputable def actorRepresentation
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    Representation (ZMod 2) (ActorQuotient Z) (Space Z ZS) where
  toFun a := (actorQuotientEquivRange Z ZS hkernel a).val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change Additive.ofMul ((actorQuotientEquivRange Z ZS hkernel 1).val v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change Additive.ofMul ((actorQuotientEquivRange Z ZS hkernel (a * b)).val v.toMul) = _
    rw [map_mul]
    rfl

/-- On a coset represented by `h`, the linear action is conjugation by `h`. -/
theorem actorRepresentation_mk
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z) (v : Space Z ZS) :
    actorRepresentation Z ZS hkernel (QuotientGroup.mk' _ h) v =
      Additive.ofMul (quotientAction Z ZS h v.toMul) := rfl

/-- The quotient representation is faithful, using the exact action kernel. -/
theorem actorRepresentation_injective
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    Function.Injective (actorRepresentation Z ZS hkernel) := by
  intro a b hab
  apply (actorQuotientEquivRange Z ZS hkernel).injective
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact Additive.ofMul.injective
    (congrArg (fun f : Module.End (ZMod 2) (Space Z ZS) => f (Additive.ofMul v)) hab)

/-- Passing from invariant subgroups to binary subspaces preserves the
irreducibility conclusion of the fixed-line argument. -/
theorem actorRepresentation_irreducible [Nontrivial (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hirr : ∀ D : Subgroup (VectorQuotient Z ZS),
      (∀ h : centralizerH Z, ∀ w ∈ D, quotientAction Z ZS h w ∈ D) →
        D = ⊥ ∨ D = ⊤) :
    Representation.IsIrreducible (actorRepresentation Z ZS hkernel) := by
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro W
  let D : Subgroup (VectorQuotient Z ZS) :=
    AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup
  have hs : ∀ h : centralizerH Z, ∀ w ∈ D, quotientAction Z ZS h w ∈ D := by
    intro h w hw
    exact W.apply_mem_toSubmodule (QuotientGroup.mk' _ h) hw
  rcases hirr D hs with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hm : v.toMul ∈ D := hv
    rw [hbot] at hm
    exact Additive.toMul.injective hm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    change v.toMul ∈ D
    rw [htop]
    trivial

/-- 15.3.57(1) for the literal faithful actor, conditional only on the
earlier kernel, line and paired-actor fixed-point statements. -/
theorem actorRepresentation_irreducible_of_pair_fixed_line [Finite G]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (hcomm : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (J : Subgroup (centralizerH Z))
    (hJT : J ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hJ : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS) :
    Representation.IsIrreducible (actorRepresentation Z ZS hkernel) := by
  have hcard := card_distinguishedLine Z ZS hZZS hZ hZS
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : distinguishedLine Z ZS)).mp hcard
  let : Nontrivial (VectorQuotient Z ZS) :=
    ⟨⟨a.val, 1, fun he => ha (Subtype.ext he)⟩⟩
  apply actorRepresentation_irreducible Z ZS hkernel
  exact lemma_15_3_57_one_of_pair_fixed_line Z ZS T hTH hZZS hZ hZS hcomm J hJT hJ

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
