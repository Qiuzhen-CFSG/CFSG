module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Coordinates
public import Theory.Representation.NormalElementaryQuotient

/-!
# The actual block image in its conjugation quotient

Restricting the centralizer quotient to L has kernel O₂(L). Its image is
therefore the original quotient L/O₂(L), retaining the A₇ marking.
The ambient image of U has binary dimension four.

Source: Aschbacher–Smith C.1.23(2), printed p.130.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H]

noncomputable def imageHom (L : Subgroup G) (q : G →* H) : L →* L.map q :=
  (q.comp L.subtype).codRestrict _ (fun l => mem_map_of_mem q l.property)

omit [Finite G] in
theorem imageHom_surjective (L : Subgroup G) (q : G →* H) :
    Function.Surjective (imageHom L q) := by
  rintro ⟨x,l,hl,rfl⟩
  exact ⟨⟨l,hl⟩,rfl⟩

omit [Finite G] in
theorem imageHom_ker (L : Subgroup G) (hL : IsShort L) (q : G →* H)
    (hk : q.ker = centralizer ((blockU L).map L.subtype : Set G)) :
    (imageHom L q).ker = pCore 2 L := by
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change q (l : G) = 1 ↔ l ∈ pCore 2 L
  rw [← MonoidHom.mem_ker, hk, ← hL.centralizer_blockU]
  constructor
  · intro h u hu
    exact Subtype.ext (h u (mem_map_of_mem L.subtype hu))
  · intro h u hu
    obtain ⟨v,hv,rfl⟩ := hu
    exact congrArg Subtype.val (h v hv)

theorem ambient_finrank (L : Subgroup G) (h : IsExceptionalA7Block L) :
    letI := h.1.elementary.map L.subtype
    Module.finrank (ZMod 2) (Additive ((blockU L).map L.subtype)) = 4 := by
  let := h.1.elementary.map L.subtype
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) (Additive ((blockU L).map L.subtype)) =
      Nat.card (Additive ((blockU L).map L.subtype)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = 2 ^ 4 := (card_map_of_injective L.subtype_injective).trans h.u_card


noncomputable def imageEquiv (L : Subgroup G) (hL : IsShort L) (q : G →* H)
    (hk : q.ker = centralizer ((blockU L).map L.subtype : Set G)) :
    (L ⧸ pCore 2 L) ≃* L.map q :=
  (QuotientGroup.quotientMulEquivOfEq (imageHom_ker L hL q hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (imageHom L q) (imageHom_surjective L q))

omit [Finite G] in
theorem image_is_a7 (L : Subgroup G) (hm : IsExceptionalA7Block L)
    (q : G →* H) (hk : q.ker = centralizer ((blockU L).map L.subtype : Set G)) :
    Nonempty (L.map q ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨a⟩ := hm.2.1
  exact ⟨(imageEquiv L hm.1 q hk).symm.trans a⟩

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
