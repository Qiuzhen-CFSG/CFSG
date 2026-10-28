module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Inputs
public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers

/-!
# Transport of intrinsic four-group geometry to the source action

The recognized actor isomorphism gives the elementary order bound, and the
index-two inner subgroup contains the image of the literal two-residual.
The supplied inner equivariance identifies the common fixed subgroup with
its natural-plus-dual coordinate space. Inner pointwise fixers and normalizers
then control every actor, without an additional outer-action hypothesis.

The final theorem discharges both intrinsic calculations: every residual
four-group fixes eight vectors, its full pointwise fixer is itself, its
normalizer is S₄, and its normalizer action has image of order six.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58 and the
last paragraph proving 15.3.61(2), printed pp.1148–1151.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open BinaryLinearThree.FourGroupGeometry
variable {G : Type*} [Group G] {Z ZS : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  {hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)}

namespace RecognizedAction
variable (d : RecognizedAction Z ZS hkernel)

include d in
/-- Every elementary two-subgroup of the actual actor has order at most four. -/
theorem elementary_card_le_four (A : Subgroup (ActorQuotient Z))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  let := hA
  rw [Nat.card_congr (d.actorEquiv.subgroupMap A).toEquiv]
  exact BinaryLinearThree.FourGroupGeometry.elementary_card_le_four _
    (IsElementaryAbelian.map d.actorEquiv.toMonoidHom)

/-- The literal index-defined two-residual maps into the inner automorphisms.
This uses an index-two preimage and does not need the ambient group finite. -/
theorem residual_actorImage_le_inner :
    (Recognition.actorImage Z (residualK Z)).map d.actorEquiv.toMonoidHom ≤
      MulAut.innerSubgroup BinaryLinearThree.Group := by
  let f : centralizerH Z →* MulAut BinaryLinearThree.Group :=
    d.actorEquiv.toMonoidHom.comp (actorProjection Z)
  have hf : Function.Surjective f :=
    d.actorEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let N := (MulAut.innerSubgroup BinaryLinearThree.Group).comap f
  have hN : N.index = 2 :=
    ((MulAut.innerSubgroup BinaryLinearThree.Group).index_comap_of_surjective hf).trans
      Matrix.PSL3Two.Automorphisms.card_outer_sl
  have hR : Stellmacher.twoResidualSubgroup (centralizerH Z) ≤ N :=
    sInf_le ⟨inferInstance, 1, by simpa using hN⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨h, hh, rfl⟩ := ha
  obtain ⟨r, hr, he⟩ := hh
  have hrh : r = h := Subtype.ext he
  subst h
  exact hR hr

/-- Fixedness in the actual action is equivalent to fixedness in the inner matrix action. -/
theorem mem_commonFixed_iff (A : Subgroup (ActorQuotient Z))
    (hA : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup BinaryLinearThree.Group)
    (w : VectorQuotient Z ZS) :
    w ∈ (actorAction Z ZS hkernel).commonFixed A ↔
      d.vectorEquiv (Additive.ofMul w) ∈ naturalDualFixed (A.map d.actorEquiv.toMonoidHom) := by
  rw [MonoidHom.mem_commonFixed, mem_naturalDualFixed]
  constructor
  · intro hw g hg
    rw [← d.inner_equivariant]
    change d.vectorEquiv (Additive.ofMul
      (actorAction Z ZS hkernel (d.actorEquiv.symm (MulAut.conj g)) w)) = _
    rw [hw _ (mem_map_equiv.mp hg)]
  · intro hw a ha
    obtain ⟨g, hg⟩ := hA (mem_map_of_mem d.actorEquiv.toMonoidHom ha)
    have he : a = d.actorEquiv.symm (MulAut.conj g) := by rw [hg]; simp
    apply Additive.ofMul.injective
    apply d.vectorEquiv.injective
    rw [he]
    change d.vectorEquiv (Recognition.actorRepresentation Z ZS hkernel
      (d.actorEquiv.symm (MulAut.conj g)) (Additive.ofMul w)) = _
    rw [d.inner_equivariant]
    exact hw g (hg ▸ mem_map_of_mem d.actorEquiv.toMonoidHom ha)

/-- Actual fixed elements correspond bijectively to their natural-plus-dual coordinates. -/
noncomputable def commonFixedEquiv (A : Subgroup (ActorQuotient Z))
    (hA : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup BinaryLinearThree.Group) :
    (actorAction Z ZS hkernel).commonFixed A ≃
      naturalDualFixed (A.map d.actorEquiv.toMonoidHom) where
  toFun w := ⟨d.vectorEquiv (Additive.ofMul w.val), (d.mem_commonFixed_iff A hA w.val).mp w.property⟩
  invFun w := ⟨(d.vectorEquiv.symm w.val).toMul, (d.mem_commonFixed_iff A hA _).mpr (by
    simpa using w.property)⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

/-- Transport an inner fixer and an inner normalizer calculation to the full actor. -/
theorem pointwise_fixer_mem_of_geometry (A : Subgroup (ActorQuotient Z))
    (hA : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup BinaryLinearThree.Group)
    (hN : normalizer (A.map d.actorEquiv.toMonoidHom : Set (MulAut BinaryLinearThree.Group)) ≤
      MulAut.innerSubgroup BinaryLinearThree.Group)
    (hfix : ∀ g : BinaryLinearThree.Group,
      (∀ w ∈ naturalDualFixed (A.map d.actorEquiv.toMonoidHom),
        (BinaryLinearThree.W g w.1, BinaryLinearThree.W.dual g w.2) = w) →
          MulAut.conj g ∈ A.map d.actorEquiv.toMonoidHom)
    (a : ActorQuotient Z)
    (ha : ∀ w ∈ (actorAction Z ZS hkernel).commonFixed A, actorAction Z ZS hkernel a w = w) :
    a ∈ A := by
  apply pointwise_fixer_mem_of_inner (actorAction Z ZS hkernel)
    ((MulAut.innerSubgroup BinaryLinearThree.Group).comap d.actorEquiv.toMonoidHom) A
    (fun x hx => hA (mem_map_of_mem _ hx)) ?_ ?_ a ha
  · intro x hx
    exact hN (A.le_normalizer_map d.actorEquiv.toMonoidHom (mem_map_of_mem _ hx))
  · intro b hb hbf
    obtain ⟨g, hg⟩ := hb
    have he : b = d.actorEquiv.symm (MulAut.conj g) := by rw [hg]; simp
    have hgA := hfix g (by
      intro w hw
      let v := (d.vectorEquiv.symm w).toMul
      have hv : v ∈ (actorAction Z ZS hkernel).commonFixed A := by
        apply (d.mem_commonFixed_iff A hA v).mpr
        simpa [v] using hw
      have hh := congrArg (fun u => d.vectorEquiv (Additive.ofMul u)) (hbf v hv)
      rw [he] at hh
      change d.vectorEquiv (Recognition.actorRepresentation Z ZS hkernel
        (d.actorEquiv.symm (MulAut.conj g)) (Additive.ofMul v)) = _ at hh
      rw [d.inner_equivariant] at hh
      simpa [v] using hh)
    rw [he]
    exact mem_map_equiv.mp hgA

include d in
/-- Transfer the two intrinsic calculations to the literal quotient action.
The final theorem below supplies both model premises. -/
theorem fourGroupModelFacts_of_intrinsic
    (hfixed : ∀ A : Subgroup (MulAut BinaryLinearThree.Group),
      A ≤ MulAut.innerSubgroup BinaryLinearThree.Group → IsElementaryAbelian 2 A →
      Nat.card A = 4 → Nat.card (naturalDualFixed A) = 8 ∧
        ∀ g : BinaryLinearThree.Group,
          (∀ w ∈ naturalDualFixed A,
            (BinaryLinearThree.W g w.1, BinaryLinearThree.W.dual g w.2) = w) →
              MulAut.conj g ∈ A)
    (hnormalizer : ∀ A : Subgroup (MulAut BinaryLinearThree.Group),
      A ≤ MulAut.innerSubgroup BinaryLinearThree.Group → IsElementaryAbelian 2 A →
      Nat.card A = 4 →
        normalizer (A : Set (MulAut BinaryLinearThree.Group)) ≤
          MulAut.innerSubgroup BinaryLinearThree.Group ∧
        Nonempty (normalizer (A : Set (MulAut BinaryLinearThree.Group)) ≃*
          Equiv.Perm (Fin 4)) ∧ Nat.card A.normalizerMonoidHom.range = 6) :
    FourGroupModelFacts Z ZS hkernel := by
  intro A hAR hA hcard
  let := hA
  let B := A.map d.actorEquiv.toMonoidHom
  have hBI : B ≤ MulAut.innerSubgroup BinaryLinearThree.Group :=
    (map_mono hAR).trans d.residual_actorImage_le_inner
  have hBE : IsElementaryAbelian 2 B := IsElementaryAbelian.map d.actorEquiv.toMonoidHom
  have hBc : Nat.card B = 4 :=
    (Nat.card_congr (d.actorEquiv.subgroupMap A).toEquiv).symm.trans hcard
  obtain ⟨hsize, hfix⟩ := hfixed B hBI hBE hBc
  obtain ⟨hinner, ⟨eN⟩, haction⟩ := hnormalizer B hBI hBE hBc
  refine ⟨(Nat.card_congr (d.commonFixedEquiv A hBI)).trans hsize, ?_,
    ⟨(normalizerEquivMap d.actorEquiv A).trans eN⟩, ?_⟩
  · exact d.pointwise_fixer_mem_of_geometry A hBI hinner hfix
  · exact (card_normalizerActionRange_map d.actorEquiv A).symm.trans haction

include d in
/-- The four-group geometry of the literal quotient action follows from its
recognized natural-plus-dual structure, with no additional model premises. -/
theorem fourGroupModelFacts : FourGroupModelFacts Z ZS hkernel :=
  d.fourGroupModelFacts_of_intrinsic FixedSpaces.naturalDualFixed_geometry
    inner_fourGroup_normalizer

end RecognizedAction
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
