module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Spaces
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CentralizerKernel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Coordinates on the original block quotient

The inclusion U(L)→V and quotient by the actual L-fixed vectors give a
surjection whose kernel is precisely C_U(L). Its first-isomorphism map
identifies BlockModule L with the literal central section in V and retains
conjugation on representatives. Equivariant coordinates on this section
therefore construct the required BlockModuleModel, including the marked
quotient L/O₂(L). No abstract module identification is substituted.

Source: Aschbacher--Smith C.1.27--28, printed pp.133--134.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
variable {G Q : Type*} [Group G] [Group Q]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
variable (q : G →* Q) (hq : Function.Surjective q) (hk : q.ker = centralizer (V : Set G))
variable (L : Subgroup G) (hU : (blockU L).map L.subtype ≤ V)

noncomputable def uToSpace : blockU L →*
    Multiplicative (space V ((blockU L).map L.subtype)) where
  toFun u := Multiplicative.ofAdd ⟨Additive.ofMul ⟨u,hU (mem_map_of_mem L.subtype u.property)⟩,
    mem_map_of_mem L.subtype u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [V.Normal] in
theorem uToSpace_surjective : Function.Surjective (uToSpace V L hU) := by
  intro w
  obtain ⟨u,hu,he⟩ := w.toAdd.property
  exact ⟨⟨u,hu⟩, congrArg Multiplicative.ofAdd (Subtype.ext
    (congrArg Additive.ofMul (Subtype.ext he)))⟩

noncomputable def quotientCoordinates : blockU L →* Multiplicative
    (centralQuotient (NormalElementaryQuotient.representation V q hq hk)
      (L.map q) (space V ((blockU L).map L.subtype))) :=
  ((fixedSpace (NormalElementaryQuotient.representation V q hq hk) (L.map q)).comap
    (space V ((blockU L).map L.subtype)).subtype).mkQ.toAddMonoidHom.toMultiplicative.comp
      (uToSpace V L hU)

theorem quotientCoordinates_surjective : Function.Surjective (quotientCoordinates V q hq hk L hU) :=
  (Submodule.mkQ_surjective _).comp (uToSpace_surjective V L hU)

theorem quotientCoordinates_kernel : (quotientCoordinates V q hq hk L hU).ker = blockFixed L := by
  ext u
  change Submodule.Quotient.mk ((uToSpace V L hU u).toAdd) = 0 ↔ (u : L) ∈ center L
  rw [Submodule.Quotient.mk_eq_zero]
  change ((uToSpace V L hU u).toAdd : Additive V) ∈
    fixedSpace (NormalElementaryQuotient.representation V q hq hk) (L.map q) ↔ _
  rw [NormalElementaryQuotient.mem_fixedSpace_image]
  constructor
  · intro hh
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (hh l l.property)
  · intro hh l hl
    exact congrArg Subtype.val (mem_center_iff.mp hh ⟨l,hl⟩)

noncomputable def moduleQuotientEquiv : BlockModule L ≃* Multiplicative
    (centralQuotient (NormalElementaryQuotient.representation V q hq hk)
      (L.map q) (space V ((blockU L).map L.subtype))) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientCoordinates_kernel V q hq hk L hU).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (quotientCoordinates_surjective V q hq hk L hU))

theorem moduleQuotientEquiv_mk (u : blockU L) :
    moduleQuotientEquiv V q hq hk L hU (QuotientGroup.mk' (blockFixed L) u) =
      quotientCoordinates V q hq hk L hU u := by
  rfl

theorem quotientCoordinates_intertwines
    (hs : L.map q ≤ subspaceStabilizer (NormalElementaryQuotient.representation V q hq hk)
      (space V ((blockU L).map L.subtype))) (l : L) (u : blockU L) :
    (quotientCoordinates V q hq hk L hU (blockConjugate L l u)).toAdd =
      centralQuotientRepresentation (NormalElementaryQuotient.representation V q hq hk)
        (L.map q) (space V ((blockU L).map L.subtype)) hs (q.subgroupMap L l)
        (quotientCoordinates V q hq hk L hU u).toAdd := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  change (l : G) * ((u : L) : G) * (l : G)⁻¹ =
    ((NormalElementaryQuotient.representation V q hq hk (q l)
      (Additive.ofMul ⟨u,hU (mem_map_of_mem L.subtype u.property)⟩)).toMul : G)
  exact (NormalElementaryQuotient.representation_apply V q hq hk l
    (Additive.ofMul ⟨u,hU (mem_map_of_mem L.subtype u.property)⟩)).symm

variable {A W k : Type*} [Group A] [AddCommGroup W] [CommSemiring k]
  [Module k W] [Module (ZMod 2) W]

include hU in
/-- Equivariant coordinates on the literal central section mark the original block module. -/
theorem linearBlockModel_of_coordinates
    (hs : L.map q ≤ subspaceStabilizer (NormalElementaryQuotient.representation V q hq hk)
      (space V ((blockU L).map L.subtype)))
    (hcore : (q.subgroupMap L).ker = pCore 2 L)
    (π : Representation k A W) (e : L.map q ≃* A)
    (E : centralQuotient (NormalElementaryQuotient.representation V q hq hk)
      (L.map q) (space V ((blockU L).map L.subtype)) ≃ₗ[ZMod 2] W)
    (hE : ∀ b v, E (centralQuotientRepresentation
      (NormalElementaryQuotient.representation V q hq hk)
      (L.map q) (space V ((blockU L).map L.subtype)) hs b v) = π (e b) (E v)) :
    IsLinearBlockModel L π := by
  let f : (L ⧸ pCore 2 L) ≃* L.map q :=
    (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective L))
  let a : A →* MulAut (Multiplicative W) := {
    toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv (π.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by ext v; change π 1 v.toAdd = v.toAdd; rw [map_one]; rfl
    map_mul' g h := by ext v; change π (g*h) v.toAdd = π g (π h v.toAdd); rw [map_mul]; rfl }
  let m : BlockModuleModel L a := {
    quotientIso := f.trans e
    moduleIso := (moduleQuotientEquiv V q hq hk L hU).trans E.toAddEquiv.toMultiplicative
    intertwining := by
      intro l u
      apply Multiplicative.toAdd.injective
      change E ((moduleQuotientEquiv V q hq hk L hU
        (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u))).toAdd) =
        π (e (q.subgroupMap L l)) (E ((moduleQuotientEquiv V q hq hk L hU
          (QuotientGroup.mk' (blockFixed L) u)).toAdd))
      rw [moduleQuotientEquiv_mk, moduleQuotientEquiv_mk,
        quotientCoordinates_intertwines V q hq hk L hU hs, hE] }
  exact ⟨a,⟨m⟩,fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
