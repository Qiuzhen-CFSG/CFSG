module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Outside
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Actors
public import Theory.Representation.PSL3Two.TransvectionFixed

/-!
# Counting the fixed lift through the recognized transvection

The residual maps to the inner subgroup of Aut(SL₃(2)). Since U = O₂(H),
an involution of K outside U maps to a nonidentity matrix involution.
Equivariant natural-plus-dual coordinates give sixteen fixed quotient
vectors. The literal center has order two, so the fixed lift has order 32
and relative index four in U.

The coordinate projection and the equivalence with its fixed preimage
are also retained for the separate quadratic product construction.
No square-map, centralizer-identity or product-recognition premise is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58–59
and the first paragraph proving 15.3.61(2), pp.1148–1150.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
variable {G : Type*} [Group G] [Finite G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The actual residual image makes an outside involution an inner matrix involution. -/
theorem exists_inner_involution (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z) (a : centralizerH Z)
    (haK : (a : G) ∈ residualK Z) (haU : (a : G) ∉ closureU Z ZS)
    (ha : orderOf (a : G) = 2) :
    ∃ g : Matrix.PSL3Two.SL, g ≠ 1 ∧ g * g = 1 ∧
      d.actorEquiv (QuotientGroup.mk' _ a) = MulAut.conj g := by
  have hm : d.actorEquiv (actorProjection Z a) ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
    rw [← actorImage_residual_inner Z d.actorEquiv]
    exact mem_map_of_mem _ (mem_map_of_mem _ haK)
  obtain ⟨g, hg⟩ := hm
  have hinj := MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    change (a : G) * (a : G) = 1
    simpa only [ha, pow_two] using pow_orderOf_eq_one (a : G)
  refine ⟨g, ?_, ?_, hg.symm⟩
  · intro he
    apply haU
    rw [hU]
    apply (actorProjection_eq_one_iff Z a).mp
    apply d.actorEquiv.injective
    rw [← hg, he, map_one, map_one]
  · apply hinj
    rw [map_mul, hg, ← map_mul, ← map_mul, ha2, map_one, map_one, map_one]

omit [Finite G] in
/-- The literal fixed quotient has sixteen elements, through the recognized action. -/
theorem quotient_fixed_card (d : RecognizedAction T Z ZS V t)
    (a : centralizerH Z) (g : Matrix.PSL3Two.SL) (hg : g ≠ 1) (hg2 : g * g = 1)
    (hactor : d.actorEquiv (QuotientGroup.mk' _ a) = MulAut.conj g) :
    Nat.card (MulAut.fixedSubgroup (quotientAction Z ZS a)) = 16 := by
  let e : VectorQuotient Z ZS ≃ BinaryLinearThree.TransvectionFixed.Space := {
    toFun w := (d.coordinates w).toAdd
    invFun w := d.coordinates.symm (Multiplicative.ofAdd w)
    left_inv w := d.coordinates.symm_apply_apply w
    right_inv w := d.coordinates.apply_symm_apply (Multiplicative.ofAdd w) }
  have he (w : VectorQuotient Z ZS) :
      w ∈ MulAut.fixedSubgroup (quotientAction Z ZS a) ↔
        BinaryLinearThree.TransvectionFixed.action g (e w) = e w := by
    rw [MulAut.mem_fixedSubgroup]
    rw [← e.injective.eq_iff]
    change (d.coordinates (quotientAction Z ZS a w)).toAdd = _ ↔ _
    rw [d.equivariant a g hactor]
    rfl
  let e' : MulAut.fixedSubgroup (quotientAction Z ZS a) ≃
      BinaryLinearThree.TransvectionFixed.Fixed g := e.subtypeEquiv he
  exact (Nat.card_congr e').trans (BinaryLinearThree.TransvectionFixed.card_fixed g hg hg2)

/-- Counting preimages uses the actual center of order two, never an ambient center. -/
theorem card_and_index [IsExtraspecial 2 (closureU Z ZS)]
    (d : RecognizedAction T Z ZS V t)
    (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hUcard : Nat.card (closureU Z ZS) = 128)
    (a : centralizerH Z) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2) :
    Nat.card (fixedLift Z ZS a) = 32 ∧ (fixedLift Z ZS a).relIndex (closureU Z ZS) = 4 := by
  obtain ⟨g, hg, hg2, hactor⟩ := exists_inner_involution d hU a haK haU ha
  let N := Z.subgroupOf (closureU Z ZS)
  let q := QuotientGroup.mk' N
  let F := MulAut.fixedSubgroup (quotientAction Z ZS a)
  let A := F.comap q
  have hNc : Nat.card N = 2 := by dsimp only [N]; rw [hcenter]; exact IsExtraspecial.center_order_p 2 _
  have hQc : Nat.card (VectorQuotient Z ZS) = 64 := by
    have hc := N.index_mul_card
    rw [hNc, hUcard] at hc
    change Nat.card (VectorQuotient Z ZS) * 2 = 128 at hc
    omega
  have hFc : Nat.card F = 16 := quotient_fixed_card d a g hg hg2 hactor
  have hFi : F.index = 4 := by
    have hc := F.index_mul_card
    rw [hFc, hQc] at hc
    omega
  have hAi : A.index = 4 := (F.index_comap_of_surjective (QuotientGroup.mk'_surjective N)).trans hFi
  have hAc : Nat.card A = 32 := by
    have hc := A.index_mul_card
    rw [hAi, hUcard] at hc
    omega
  constructor
  · change Nat.card (A.map (closureU Z ZS).subtype) = 32
    rw [card_map_of_injective (closureU Z ZS).subtype_injective, hAc]
  · change ((A.map (closureU Z ZS).subtype).subgroupOf (closureU Z ZS)).index = 4
    have he : (A.map (closureU Z ZS).subtype).subgroupOf (closureU Z ZS) = A := by
      ext x
      exact mem_map_iff_mem (closureU Z ZS).subtype_injective
    rw [he, hAi]
/-- Coordinates composed with the literal quotient projection. -/
noncomputable def coordinateProjection (d : RecognizedAction T Z ZS V t) :
    closureU Z ZS →* Multiplicative BinaryLinearThree.TransvectionFixed.Space :=
  d.coordinates.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)))

omit [Finite G] in
/-- Every natural-plus-dual vector has an actual lift in U. -/
theorem coordinateProjection_surjective (d : RecognizedAction T Z ZS V t) :
    Function.Surjective (coordinateProjection d) :=
  d.coordinates.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- The coordinate projection has the relative center as its exact kernel. -/
theorem coordinateProjection_ker (d : RecognizedAction T Z ZS V t)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS)) :
    (coordinateProjection d).ker = center (closureU Z ZS) := by
  rw [← hcenter]
  ext x
  change d.coordinates (QuotientGroup.mk' _ x) = 1 ↔ x ∈ Z.subgroupOf (closureU Z ZS)
  rw [← d.coordinates.map_one, d.coordinates.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- The actual fixed lift is the coordinate fixed preimage, through an actual
multiplicative equivalence. This is transport, not product recognition. -/
noncomputable def equiv_coordinatePreimage (d : RecognizedAction T Z ZS V t)
    (a : centralizerH Z) (g : Matrix.PSL3Two.SL)
    (hactor : d.actorEquiv (QuotientGroup.mk' _ a) = MulAut.conj g) :
    fixedLift Z ZS a ≃*
      (BinaryLinearThree.TransvectionFixed.fixedSubgroup g).comap (coordinateProjection d) := by
  let S := (BinaryLinearThree.TransvectionFixed.fixedSubgroup g).comap (coordinateProjection d)
  have he : S.map (closureU Z ZS).subtype = fixedLift Z ZS a := by
    apply congrArg (fun A : Subgroup (closureU Z ZS) => A.map (closureU Z ZS).subtype)
    ext x
    change coordinateProjection d x ∈ BinaryLinearThree.TransvectionFixed.fixedSubgroup g ↔
      QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x ∈
        MulAut.fixedSubgroup (quotientAction Z ZS a)
    rw [BinaryLinearThree.TransvectionFixed.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    change BinaryLinearThree.TransvectionFixed.action g
      (d.coordinates (QuotientGroup.mk' _ x)).toAdd =
        (d.coordinates (QuotientGroup.mk' _ x)).toAdd ↔
      quotientAction Z ZS a (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
    rw [← d.coordinates.injective.eq_iff]
    rw [← Multiplicative.toAdd.injective.eq_iff]
    rw [d.equivariant a g hactor]
    rfl
  exact (MulEquiv.subgroupCongr he.symm).trans
    (S.equivMapOfInjective (closureU Z ZS).subtype (closureU Z ZS).subtype_injective).symm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
