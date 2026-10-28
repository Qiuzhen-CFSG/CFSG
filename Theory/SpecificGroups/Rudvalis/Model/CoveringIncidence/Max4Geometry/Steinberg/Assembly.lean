module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.QuotientCoordinates

/-!
# Extension of the max4 Steinberg intertwiner from words

The two concrete conjugation tables imply equivariance first on the generating
words of the quotient and then on both generators of max4. Equality of homomorphisms
on a generating set extends each step to the entire group. The action remains
that of the marked natural actor, and the literal quotient projection is retained.
The finite word identities are explicit here until their certificates are supplied.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
open scoped IsMulCommutative
namespace Rudvalis.CoveringIncidence.Max4Steinberg

private noncomputable def adjointAut (g : BinaryLinearThree.Group) : MulAut (Multiplicative Steinberg) where
  toFun x := Multiplicative.ofAdd (S g x.toAdd)
  invFun x := Multiplicative.ofAdd (S g⁻¹ x.toAdd)
  left_inv x := S.inv_self_apply g x.toAdd
  right_inv x := S.self_inv_apply g x.toAdd
  map_mul' x y := (S g).map_add x.toAdd y.toAdd

private noncomputable def adjointAction :
    BinaryLinearThree.Group →* MulAut (Multiplicative Steinberg) where
  toFun := adjointAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    change S 1 x.toAdd = x.toAdd
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change S (g * h) x.toAdd = S g (S h x.toAdd)
    rw [map_mul, Module.End.mul_apply]

private noncomputable def targetAction : max4 →* MulAut (Multiplicative Steinberg) :=
  adjointAction.comp (max4NaturalActor.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 max4)))

private theorem targetAction_apply (g : max4) (x : Multiplicative Steinberg) :
    (targetAction g x).toAdd =
      S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g)) x.toAdd := by rfl

variable (hgen : closure (Set.range Max4Words.generator) = max4Core)

public theorem quotientWord_action (hw : ConjugateWordIdentities) (i : Fin 2) (j : Fin 11) :
    max4CentralQuotientAction (actorGenerator i) (quotientWord hgen j) =
      ((conjugateWord i j).map (quotientWord hgen)).prod := by
  change max4CentralQuotientAction (actorGenerator i)
    (QuotientGroup.mk' (center max4Core) (coreWord hgen j)) = _
  rw [max4CentralQuotientAction_mk]
  have h : max4CoreAction (actorGenerator i) (coreWord hgen j) =
      ((conjugateWord i j).map (coreWord hgen)).prod := by
    apply max4Core.subtype_injective
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
      max4CoreAction_apply, coreWord] using hw i j
  rw [h, map_list_prod, List.map_map]
  rfl

variable [IsElementaryAbelian 2 Max4CentralQuotient]
variable (hcenter : max4CoreCenter = elementary 2) (hc : CentralWordIdentities)

private theorem quotientEquiv_product (w : List (Fin 11)) :
    (quotientEquiv hgen hcenter hc ((w.map (quotientWord hgen)).prod)).toAdd =
      (w.map wordImage).sum := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simpa only [List.map_cons, List.prod_cons, map_mul, toAdd_mul,
      quotientEquiv_word, List.sum_cons] using congrArg (wordImage j + ·) ih

private theorem generator_intertwines (hw : ConjugateWordIdentities) (i : Fin 2) :
    (quotientEquiv hgen hcenter hc).toMonoidHom.comp
        (max4CentralQuotientAction (actorGenerator i)).toMonoidHom =
      (targetAction (actorGenerator i)).toMonoidHom.comp
        (quotientEquiv hgen hcenter hc).toMonoidHom := by
  apply MonoidHom.eq_of_eqOn_dense (quotientWord_closure hgen)
  rintro _ ⟨j, rfl⟩
  apply Multiplicative.toAdd.injective
  change (quotientEquiv hgen hcenter hc
      (max4CentralQuotientAction (actorGenerator i) (quotientWord hgen j))).toAdd =
    S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) (actorGenerator i)))
      (quotientEquiv hgen hcenter hc (quotientWord hgen j)).toAdd
  rw [quotientWord_action hgen hw, quotientEquiv_product, quotientEquiv_word,
    naturalActor_generator]
  exact (wordImage_action i j).symm

/-- Full equivariance follows from the finite word certificates, with no new actor choice. -/
public theorem quotientEquiv_action_of_wordIdentities (hw : ConjugateWordIdentities)
    (g : max4) (x : Max4CentralQuotient) :
    (quotientEquiv hgen hcenter hc (max4CentralQuotientAction g x)).toAdd =
      S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (quotientEquiv hgen hcenter hc x).toAdd := by
  have h : (MulAut.congr (G := Max4CentralQuotient) (H := Multiplicative Steinberg)
        (quotientEquiv hgen hcenter hc)).toMonoidHom.comp
        max4CentralQuotientAction = targetAction := by
    apply MonoidHom.eq_of_eqOn_dense actorGenerator_closure
    rintro _ ⟨i, rfl⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := (quotientEquiv hgen hcenter hc).surjective y
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
        DFunLike.congr_fun (generator_intertwines hgen hcenter hc hw i) z
  have hx := congrArg (fun a : MulAut (Multiplicative Steinberg) =>
      a (quotientEquiv hgen hcenter hc x)) (DFunLike.congr_fun h g)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, targetAction_apply] using
      congrArg Multiplicative.toAdd hx

/-- Compatibility with the original projection, not merely an abstract module isomorphism. -/
public theorem quotientEquiv_action_mk_of_wordIdentities (hw : ConjugateWordIdentities)
    (g : max4) (x : max4Core) :
    (quotientEquiv hgen hcenter hc
      (QuotientGroup.mk' (center max4Core) (max4CoreAction g x))).toAdd =
      S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (quotientEquiv hgen hcenter hc (QuotientGroup.mk' (center max4Core) x)).toAdd := by
  rw [← max4CentralQuotientAction_mk]
  exact quotientEquiv_action_of_wordIdentities hgen hcenter hc hw g _

end Rudvalis.CoveringIncidence.Max4Steinberg
