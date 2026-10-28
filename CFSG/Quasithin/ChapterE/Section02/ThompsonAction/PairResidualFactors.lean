module
public import Theory.GroupTheory.PResidual.NormalSup
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedSource
public import Theory.SpecificGroups.SymmetricTwoResidual
/-!
# The original residual factors of an E.2.3 pair

Take the two-residuals of the preimages of the two actual offender factors.
Their join is exactly O²(G): the factor preimages are normal in their join,
which contains the ambient residual, so residual functoriality and the
normal-product identity apply. The quotient images are the residuals of
the same original factors. No restriction on the centralizer kernel is
needed for these transport identities.

Source: Aschbacher--Smith E.2.3(1)--(3), pp.216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

abbrev factorPreimage (q : G →* H) (Y : Subgroup H) (A : Subgroup Y) : Subgroup G :=
  (A.map Y.subtype).comap q
abbrev factorResidual (q : G →* H) (Y : Subgroup H) (A : Subgroup Y) : Subgroup G :=
  (pResidual 2 (factorPreimage q Y A)).map (factorPreimage q Y A).subtype

omit [Finite G] [Finite H] in
theorem factorPreimage_sup (q : G →* H) (hq : Function.Surjective q)
    (Y : Subgroup H) (A B : Subgroup Y) (hAB : A ⊔ B = ⊤) :
    factorPreimage q Y A ⊔ factorPreimage q Y B = Y.comap q := by
  change (A.map Y.subtype).comap q ⊔ (B.map Y.subtype).comap q = _
  rw [comap_sup_eq q _ _ hq,← Subgroup.map_sup,hAB,← MonoidHom.range_eq_map,range_subtype]

omit [Finite G] [Finite H] in
theorem factorPreimage_normal (q : G →* H) (Y : Subgroup H)
    (A : Subgroup Y) [A.Normal] :
    ((factorPreimage q Y A).subgroupOf (Y.comap q)).Normal := by
  let f : Y.comap q →* Y := {
    toFun := fun x => ⟨q x,x.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q (x:G) (y:G)) }
  have he : (factorPreimage q Y A).subgroupOf (Y.comap q) = A.comap f := by
    ext x
    change q (x:G) ∈ A.map Y.subtype ↔ f x ∈ A
    constructor
    · rintro ⟨a,ha,he⟩
      have hx : a = f x := Subtype.ext he
      exact hx ▸ ha
    · intro hx
      exact ⟨f x,hx,rfl⟩
  rw [he]
  infer_instance

theorem factorResidual_image (q : G →* H) (hq : Function.Surjective q)
    (Y : Subgroup H) (A : Subgroup Y) :
    (factorResidual q Y A).map q = ((pResidual 2 A).map A.subtype).map Y.subtype := by
  change ((pResidual 2 ((A.map Y.subtype).comap q)).map _).map q = _
  rw [map_embedded_pResidual,map_comap_eq_self_of_surjective hq]
  exact (map_embedded_pResidual 2 A Y.subtype).symm

omit [Finite H] in
theorem factorResidual_sup (q : G →* H) (hq : Function.Surjective q)
    (Y : Subgroup H) (A B : Subgroup Y) [A.Normal] [B.Normal]
    (hAB : A ⊔ B = ⊤) (hR : (pResidual 2 G).map q ≤ Y) :
    factorResidual q Y A ⊔ factorResidual q Y B = pResidual 2 G := by
  have hjoin := factorPreimage_sup q hq Y A B hAB
  have hA : ((factorPreimage q Y A).subgroupOf
      (factorPreimage q Y A ⊔ factorPreimage q Y B)).Normal := by
    rw [hjoin]
    exact factorPreimage_normal q Y A
  have hB : ((factorPreimage q Y B).subgroupOf
      (factorPreimage q Y A ⊔ factorPreimage q Y B)).Normal := by
    rw [hjoin]
    exact factorPreimage_normal q Y B
  let := hA
  let := hB
  apply embedded_pResidual_sup_eq_of_contains_residual
  rw [hjoin]
  exact (map_le_iff_le_comap).mp hR

/-- The original source factors generate the literal original two-residual. -/
theorem paired_residual_factors_generate
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    factorResidual q Y d.first ⊔ factorResidual q Y d.second = pResidual 2 G := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := d.product.first_normal
  let := d.product.second_normal
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  apply factorResidual_sup q hq Y d.first d.second d.product.sup_eq_top
  rw [map_pResidual_of_surjective 2 q hq]
  exact (offender_generation (T.mapSurjective hq) hp α hff hcore).1
end CFSG.Quasithin.ChapterE.ThompsonAction
