module
public import Theory.GroupTheory.PResidual.NormalSup
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Original residual factors at the B.6.10 boundary

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
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open SourceInduction
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

omit [Finite G] [Finite H] in
theorem factorResidual_le_residual (q : G →* H) (Y : Subgroup H) (A : Subgroup Y) :
    factorResidual q Y A ≤ pResidual 2 G :=
  map_pResidual_le 2 (factorPreimage q Y A).subtype

omit [Finite G] [Finite H] in
theorem factorResidual_normalized (q : G →* H) (Y : Subgroup H)
    (A : Subgroup Y) [A.Normal] :
    Y.comap q ≤ normalizer (factorResidual q Y A : Set G) := by
  have hA : factorPreimage q Y A ≤ Y.comap q := by
    intro x hx
    exact map_subtype_le A hx
  have hn := (normal_subgroupOf_iff_le_normalizer hA).mp (factorPreimage_normal q Y A)
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (factorPreimage q Y A) (pResidual 2 (factorPreimage q Y A)))
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
