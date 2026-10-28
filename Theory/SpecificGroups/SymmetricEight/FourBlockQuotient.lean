module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Theory.GroupTheory.PermutationWreathEmbedding
public import Theory.SpecificGroups.SymmetricFourWreath.ResidualQuotient

/-!
# The characteristic nine-subgroup in the four-block quotient

Numbering the two four-point blocks identifies their full stabilizer in S₈
with S₄ wreath C₂. A block-preserving permutation translates the two block
labels by one element of C₂; the regular wreath action then supplies its
unique wreath coordinates. This construction uses only the eight points,
not an enumeration of the full permutation group.

The coordinate quotients S₄ → S₃ identify the actual two-core quotient with
the binary two-plane wreath actor. Transporting its computed three-core
proves that the literal block quotient has characteristic elementary
three-core of order nine, with a two-group quotient.

Source application: Aschbacher–Smith, Chapter E, Section 2.5, symmetric-eight
four-block local model (Lemma 2.5.26, printed p.569). These are the concrete
quotient inputs for the paired local recognition argument.
-/

open Subgroup
namespace Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev W4 := RegularWreathProduct (Equiv.Perm (Fin 4)) C2
private abbrev H := A6ShadowTwoLocals.fourStabilizer
private def coordinates : Fin 8 ≃ Fin 4 × C2 :=
  (@finProdFinEquiv 2 4).symm.trans ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.refl _) ((ZMod.finEquiv 2).toEquiv.trans Multiplicative.ofAdd)))
private theorem same_block (i j : Fin 8) :
    (coordinates i).2 = (coordinates j).2 ↔ i.val / 4 = j.val / 4 := by
  revert i j
  decide +kernel
private theorem c2_translation (q r s : C2) (h : s = q ↔ r = 1) : s = q * r := by
  revert q r s
  decide +kernel
private def wreathHom : W4 →* Equiv.Perm (Fin 8) :=
  coordinates.symm.permCongrHom.toMonoidHom.comp
    (RegularWreathProduct.toPerm (Equiv.Perm (Fin 4)) C2 (Fin 4))
private theorem wreathHom_mem (w : W4) : wreathHom w ∈ H := by
  intro i j
  rw [← same_block, ← same_block]
  simp only [wreathHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]
  exact mul_left_cancel_iff
private def intoBlocks : W4 →* H := wreathHom.codRestrict H wreathHom_mem
private theorem intoBlocks_injective : Function.Injective intoBlocks := by
  intro a b hab
  apply RegularWreathProduct.toPermInj (Equiv.Perm (Fin 4)) C2 (Fin 4)
  apply coordinates.symm.permCongrHom.injective
  exact congrArg Subtype.val hab
private theorem intoBlocks_surjective : Function.Surjective intoBlocks := by
  intro g
  let p := coordinates.permCongrHom (g : Equiv.Perm (Fin 8))
  have hp (x y : Fin 4 × C2) : (p x).2 = (p y).2 ↔ x.2 = y.2 := by
    have h := g.property (coordinates.symm x) (coordinates.symm y)
    rw [← same_block, ← same_block] at h
    simpa only [p, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.apply_symm_apply] using h
  obtain ⟨w, hw⟩ := RegularWreathProduct.exists_toPerm_eq_of_block_translation p
    (p (0,1)).2 (fun x => c2_translation _ _ _ (hp x (0,1)))
  refine ⟨w, Subtype.ext ?_⟩
  apply coordinates.permCongrHom.injective
  change coordinates.permCongrHom (coordinates.symm.permCongrHom
    (RegularWreathProduct.toPerm (Equiv.Perm (Fin 4)) C2 (Fin 4) w)) = p
  rw [← Equiv.permCongrHom_symm, MulEquiv.apply_symm_apply]
  exact hw
/-- The full stabilizer of two unordered four-point blocks is the regular wreath product. -/
public noncomputable def fourStabilizerWreathEquiv : A6ShadowTwoLocals.fourStabilizer ≃*
    RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) :=
  (MulEquiv.ofBijective intoBlocks ⟨intoBlocks_injective, intoBlocks_surjective⟩).symm


/-- The literal two-core quotient is the binary two-plane wreath actor. -/
public noncomputable def fourStabilizerQuotientEquivActor :
    (A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer) ≃*
      Theory.GroupTheory.WreathTwoResidual.Actor :=
  (QuotientGroup.congr _ _ fourStabilizerWreathEquiv
    (pCore_map_iso 2 fourStabilizerWreathEquiv)).trans
      SymmetricFourWreath.quotientEquivActor
private abbrev B := H ⧸ pCore 2 H
private noncomputable def threeCoreEquiv :
    pCore 3 B ≃* pCore 3 Theory.GroupTheory.WreathTwoResidual.Actor :=
  (fourStabilizerQuotientEquivActor.subgroupMap (pCore 3 B)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 fourStabilizerQuotientEquivActor))
/-- The characteristic three-core of the actual block quotient is elementary abelian. -/
public theorem threeCore_elementary :
    IsElementaryAbelian 3 (pCore 3
      (A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer)) := by
  have : IsElementaryAbelian 3 (pCore 3 Theory.GroupTheory.WreathTwoResidual.Actor) :=
    Theory.GroupTheory.WreathTwoResidual.threeCore_elementary
  exact IsElementaryAbelian.of_injective threeCoreEquiv.toMonoidHom threeCoreEquiv.injective
/-- The characteristic three-core of the actual block quotient has order nine. -/
public theorem threeCore_card :
    Nat.card (pCore 3
      (A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer)) = 9 := by
  rw [Nat.card_congr threeCoreEquiv.toEquiv]
  exact Theory.GroupTheory.WreathTwoResidual.threeCore_card
/-- Factoring out the characteristic three-core leaves a two-group. -/
public theorem threeCore_quotient_two :
    IsPGroup 2 ((A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer) ⧸
      pCore 3 (A6ShadowTwoLocals.fourStabilizer ⧸ pCore 2 A6ShadowTwoLocals.fourStabilizer)) := by
  exact Theory.GroupTheory.WreathTwoResidual.threeCore_quotient_two.of_equiv
    (QuotientGroup.congr _ _ fourStabilizerQuotientEquivActor
      (pCore_map_iso 3 fourStabilizerQuotientEquivActor)).symm
end Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
