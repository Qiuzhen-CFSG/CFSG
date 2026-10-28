module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Operations on involution-centralizer quotient sections

A surjection from a centralizing subgroup supplies the quotient by its relatively
normal kernel. Pulling back a subgroup of the target requires no splitting;
transport moves the involution, numerator and quotient map along one ambient
isomorphism. In a centerless finite group the resulting section is strictly
smaller than the ambient group.

These operations support smaller-section induction in Aschbacher--Smith A.2.15
and the nonsplit centralizers in A.2.19 (printed pp. 37--41). They do not construct
any of the sporadic centralizers appearing in GLS3 section 5.3.
-/

public section

namespace CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData

variable {G H S T : Type*} [Group G] [Group H] [Group S] [Group T]

/-- First isomorphism theorem with normality inside the numerator only. -/
noncomputable def quotientEquiv (d : InvolutionCentralizerQuotientData G S) :
    d.numerator ⧸ d.quotientMap.ker ≃* S :=
  QuotientGroup.quotientKerEquivOfSurjective d.quotientMap d.surjective

/-- Change the target by an actual isomorphism. -/
def mapTarget (d : InvolutionCentralizerQuotientData G S) (e : S ≃* T) :
    InvolutionCentralizerQuotientData G T where
  involution := d.involution
  involution_order := d.involution_order
  numerator := d.numerator
  centralizes := d.centralizes
  quotientMap := e.toMonoidHom.comp d.quotientMap
  surjective := e.surjective.comp d.surjective

/-- Pull back a subgroup of a quotient; this does not assume a splitting. -/
noncomputable def restrictTarget (d : InvolutionCentralizerQuotientData G S)
    (L : Subgroup S) : InvolutionCentralizerQuotientData G L := by
  let P := L.comap d.quotientMap
  let e := P.equivMapOfInjective d.numerator.subtype Subtype.val_injective
  let f : P →* L :=
    { toFun := fun x => ⟨d.quotientMap x.val, x.property⟩
      map_one' := Subtype.ext d.quotientMap.map_one
      map_mul' := fun x y => Subtype.ext (d.quotientMap.map_mul x.val y.val) }
  refine
    { involution := d.involution
      involution_order := d.involution_order
      numerator := P.map d.numerator.subtype
      centralizes := ?_
      quotientMap := f.comp e.symm.toMonoidHom
      surjective := ?_ }
  · rintro x ⟨y, _, rfl⟩
    exact d.centralizes y.property
  · intro x
    obtain ⟨y, hy⟩ := d.surjective x.val
    have hyP : y ∈ P := by
      change d.quotientMap y ∈ L
      rw [hy]
      exact x.property
    refine ⟨e ⟨y, hyP⟩, ?_⟩
    change f (e.symm (e ⟨y, hyP⟩)) = x
    rw [e.symm_apply_apply]
    exact Subtype.ext hy

/-- Transport the involution, subgroup, and quotient map together. -/
def transport (d : InvolutionCentralizerQuotientData G S) (e : G ≃* H) :
    InvolutionCentralizerQuotientData H S where
  involution := e d.involution
  involution_order := (e.orderOf_eq d.involution).trans d.involution_order
  numerator := d.numerator.map e.toMonoidHom
  centralizes := by
    rintro x ⟨y, hy, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (map_mul e y d.involution).symm.trans
      ((congrArg e (Subgroup.mem_centralizer_singleton_iff.mp (d.centralizes hy))).trans
        (map_mul e d.involution y))
  quotientMap := d.quotientMap.comp (e.subgroupMap d.numerator).symm.toMonoidHom
  surjective := d.surjective.comp (e.subgroupMap d.numerator).symm.surjective

/-- Nonidentity of the involution forces a proper numerator in a centerless group. -/
theorem numerator_ne_top (d : InvolutionCentralizerQuotientData G S)
    (hcenter : Subgroup.center G = ⊥) : d.numerator ≠ ⊤ := by
  intro htop
  have hz : d.involution ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subgroup.mem_centralizer_singleton_iff.mp
    exact d.centralizes (htop ▸ Subgroup.mem_top x)
  have hone : d.involution = 1 := by
    simpa only [hcenter, Subgroup.mem_bot] using hz
  have horder := d.involution_order
  rw [hone, orderOf_one] at horder
  exact (by decide : (1 : ℕ) ≠ 2) horder

/-- The source's nonabelian simple ambient group has trivial center. -/
theorem numerator_ne_top_of_simple [IsSimpleGroup G]
    (d : InvolutionCentralizerQuotientData G S) (hnonabelian : ¬ IsMulCommutative G) :
    d.numerator ≠ ⊤ := by
  apply d.numerator_ne_top
  exact (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top.resolve_right
    (fun h => hnonabelian (Subgroup.center_eq_top_iff.mp h))

end CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData

namespace CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData

variable {G S : Type*} [Group G] [Group S]

/-- Every such quotient is strictly smaller than the centerless finite ambient group. -/
public theorem card_lt [Finite G] (d : InvolutionCentralizerQuotientData G S)
    (hcenter : Subgroup.center G = ⊥) : Nat.card S < Nat.card G := by
  apply lt_of_le_of_lt (Nat.card_le_card_of_surjective _ d.surjective)
  apply lt_of_le_of_ne (Nat.card_le_card_of_injective d.numerator.subtype
    Subtype.val_injective)
  intro heq
  apply d.numerator_ne_top hcenter
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := ((Nat.bijective_iff_injective_and_card d.numerator.subtype).mpr
    ⟨Subtype.val_injective, heq⟩).surjective x
  exact y.property

end CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData
