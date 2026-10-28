module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ExtraspecialIrreducible
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import CFSG.Quasithin.ChapterD.Section03.FrattiniTransport
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Sylow irreducibility in the actual extraspecial action image

For a normal elementary binary subgroup V of the selected local M, its
literal action image is canonically M/C_M(V). That isomorphism carries the
original Sylow image and the actual two-residual to the corresponding objects
in the centralizer quotient. The established source irreducibility theorem
therefore transports to the original image, preserving the Frattini action.

Source: Aschbacher--Smith 15.1.2, printed p.1086, extraspecial case.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The existing centralizer-quotient source theorem on the unchanged action image. -/
theorem source_extraspecial_image_frattini_irreducible
    (T : Sylow 2 G) {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVM : V ≤ M) (hn : M ≤ normalizer (V : Set G))
    (P : Subgroup (internalActionImage M V hn)) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 6)
    (hres : P = pResidual 2 (internalActionImage M V hn)) :
    let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
    ChapterD.Section03.FrattiniIrreducible
      ((T.subtype hM.1.2 : Subgroup M).map f) P
      (le_normalizer_of_normal) := by
  let U := V.subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVM
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  have hf := (actionHom M V hn).rangeRestrict_surjective
  have hker : f.ker = centralizer (U : Set M) := by
    change (actionHom M V hn).rangeRestrict.ker = centralizer (U : Set M)
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext m
    constructor
    · intro h u hu
      apply Subtype.ext
      exact h u hu
    · intro h v hv
      exact congrArg M.subtype (h ⟨v,hVM hv⟩ hv)
  let e : (M ⧸ centralizer (U : Set M)) ≃* internalActionImage M V hn :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let Q := P.map e.symm.toMonoidHom
  let : Q.Normal := Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  let a := P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let : IsExtraspecial 3 Q := IsExtraspecial.of_mulEquiv a inferInstance
  have hQ : Nat.card Q = 27 := (Nat.card_congr a.symm.toEquiv).trans hP
  have hQexp : Monoid.exponent Q = 3 := (Monoid.exponent_eq_of_mulEquiv a).symm.trans hexp
  let x : Additive U ≃ₗ[ZMod 2] Additive V :=
    { (subgroupOfEquivOfLe hVM).toAdditive with
      map_smul' := ZMod.map_smul (subgroupOfEquivOfLe hVM).toAdditive }
  have hUdim : Module.finrank (ZMod 2) (Additive U) = 6 := x.finrank_eq.trans hdim
  have hQres : Q = pResidual 2 (M ⧸ centralizer (U : Set M)) := by
    dsimp only [Q]
    rw [hres,map_pResidual_of_surjective 2 e.symm.toMonoidHom e.symm.surjective]
  have hi := source_extraspecial_residual_frattini_irreducible T hM hu hne U Q hQ hQexp hUdim hQres
  have hback : Q.map e.toMonoidHom = P := by
    dsimp only [Q]
    rw [map_map]
    rw [show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from
      MonoidHom.ext (fun x => e.apply_symm_apply x),map_id]
  have hactor : (((T.subtype hM.1.2 : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M)))).map e.toMonoidHom) =
      (T.subtype hM.1.2 : Subgroup M).map f := by
    rw [map_map]
    congr 1
  have hh := hi.map_equiv e (by rw [hback,normalizer_eq_top]; exact le_top)
  simpa only [hback,hactor] using hh
end CFSG.Quasithin.Chapter15.Section01
