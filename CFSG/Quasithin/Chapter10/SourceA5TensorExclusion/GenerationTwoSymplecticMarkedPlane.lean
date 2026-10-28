module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.PlaneQuotient

/-!
# The literal marked plane quotient in the tensor Sp₄ branch

The original residual is perfect. Its quotient by its intrinsic commutator
core is a central two-cover of Sp₄(4), so the checked central-cover theorem
identifies that whole core with its two-core. Restrict the original Sylow
to the residual and carry the original local component through the actual
core quotient. Parabolic placement and the lifted rank-one automorphism
then construct a surjection from the original L onto the plane local group
over Binary.F. Its kernel is exactly the original ambient block intersected
with L, and its SL₂ quotient agrees with the original first-factor marking.

The already constructed full-module natural quotient supplies the exact
conjugation equivariance. Thus all original plane maps are proved, with no
remaining plane-recognition premise. Whole-block recognition, in particular
the non-Frattini branch of MS93 (3.6), remains with qt-d-tensor-sp4-plane.

Source: Aschbacher--Smith 9.3.10 and the concluding paragraph of 9.3,
printed pp.734--735, with C.1.8, A.3.12 and I.1.3.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ClassicalOrthogonal.FourPlusMatrix
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

/-- The original perfect residual has no central two-kernel above its intrinsic core. -/
theorem residual_twoCore_eq_blockU
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    pCore 2 (pResidual 2 c.M) = ChapterC.blockU (pResidual 2 c.M) := by
  let := c.component_product.1.perfect
  apply ChapterC.RankTwo.Sp4Four.core_eq_blockU_of_symplectic_quotient _ eK
  rw [ChapterB.QuasisimpleSource.BinaryField.four.card_eq]
  decide

/-- The original L maps onto the literal plane local, with its whole block
intersection as kernel and its original first-factor marking unchanged. -/
theorem exists_marked_plane_quotient
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    ∃ q : L →* planeLocal (F := Binary.F), Function.Surjective q ∧
      q.ker = (((ChapterC.blockU (pResidual 2 c.M)).map
        (pResidual 2 c.M).subtype).map c.M.subtype).subgroupOf L ∧
      ∀ l : L, Plane.quotientMap (q l) =
        m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  let K := pResidual 2 c.M
  let C := L.subgroupOf c.M
  let B := C.subgroupOf K
  have hLM : L ≤ c.M := c.generated ▸ le_sup_of_le_left le_sup_left
  have hCK : C ≤ K := c.component_product.2.1
  let i : B ≃* L := (subgroupOfEquivOfLe hCK).trans (subgroupOfEquivOfLe hLM)
  have hF : Nat.card Binary.F = 4 := by
    rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
  let fieldIso : ChapterB.QuasisimpleSource.BinaryField.four.Carrier ≃+* Binary.F := by
    let := Fintype.ofFinite ChapterB.QuasisimpleSource.BinaryField.four.Carrier
    apply FiniteField.ringEquivOfCardEq
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,
      ChapterB.QuasisimpleSource.BinaryField.four.card_eq,hF]
    rfl
  let eK' := eK.trans (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp fieldIso)
  let eB : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 2) Binary.F :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans (e.trans m.firstMarking)
  obtain ⟨S,hS⟩ := c.sylow
  have heS : (S : Subgroup c.M) =
      ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M := by
    apply Subgroup.map_injective c.M.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (c.generated ▸ le_sup_right)]
  have hClocal : C ∈ localCComponents S := by
    rw [heS]
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLM
  obtain ⟨R,_,hBR⟩ := SourceEmbeddings.exists_local_sylow_restriction S hClocal hCK
    (inferInstance : K.Normal).isSubnormal
  obtain ⟨q,hq,hk,hm⟩ := ChapterC.RankTwo.Sp4Four.local_plane_surjection hF R B hBR eK' eB
  have hcore : pCore 2 K = ChapterC.blockU K := c.residual_twoCore_eq_blockU eK
  refine ⟨q.comp i.symm.toMonoidHom,hq.comp i.symm.surjective,?_,?_⟩
  · ext l
    change q (i.symm l) = 1 ↔ _
    rw [←MonoidHom.mem_ker,hk,hcore]
    change (i.symm l).val ∈ ChapterC.blockU K ↔
      (l : G) ∈ ((ChapterC.blockU K).map K.subtype).map c.M.subtype
    constructor
    · intro h
      exact mem_map_of_mem c.M.subtype (mem_map_of_mem K.subtype h)
    · rintro ⟨x,⟨y,hy,rfl⟩,he⟩
      have hyi : y = (i.symm l).val := Subtype.ext (Subtype.ext he)
      exact hyi ▸ hy
  · intro l
    change Plane.quotientMap (q (i.symm l)) = _
    have h := hm (i.symm l)
    change Plane.quotientMap (q (i.symm l)) =
      m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) (i (i.symm l)))) at h
    simpa only [i.apply_symm_apply] using h

end GenerationTwoOvergroup

/-- The actual marked plane-local quotient has no remaining recognition premise. -/
theorem symplecticMarkedPlaneQuotient (m : SourceA5TensorModel D e) :
    m.SymplecticMarkedPlaneQuotient := by
  intro c eK _
  exact c.exists_marked_plane_quotient eK

/-- Whole-block recognition supplies the order; all original plane maps are constructed. -/
theorem symplecticPlaneFromBlock (m : SourceA5TensorModel D e) :
    m.SymplecticPlaneFromBlock :=
  symplecticPlaneFromBlock_of_marked_quotient m.symplecticMarkedPlaneQuotient

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
