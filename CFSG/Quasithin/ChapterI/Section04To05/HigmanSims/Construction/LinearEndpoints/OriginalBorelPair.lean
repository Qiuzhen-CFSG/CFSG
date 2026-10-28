module
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CompatibleBorelMarking
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The original HS endpoint pair with compatible whole-Borel markings

The original TypeAt hypotheses produce both actual endpoints, their natural
quotient and kernel coordinates, the original elementary radicals and cubic,
and a compatible marking of their whole intersection. Entrywise field
transport reaches the canonical Chapter F projective flag amalgam. This
statement makes no assertion about mixed products in the original ambient
group.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion

private def canonical_flag_iso : RankTwoAmalgam.Iso (fullBorelAmalgam F)
    (ChapterF.GreenBook.LieModels.LinearThree.amalgam Matrix.PSL3Four.F) where
  left := ((Atlas.fieldEquivPSL 3 fieldEquiv).subgroupMap (pointParabolic F)).trans
    (MulEquiv.subgroupCongr (FieldTransport.field_map_pointParabolic fieldEquiv))
  middle := ((Atlas.fieldEquivPSL 3 fieldEquiv).subgroupMap (borel F)).trans
    (MulEquiv.subgroupCongr (FieldTransport.field_map_borel fieldEquiv))
  right := ((Atlas.fieldEquivPSL 3 fieldEquiv).subgroupMap (lineParabolic F)).trans
    (MulEquiv.subgroupCongr (FieldTransport.field_map_lineParabolic fieldEquiv))
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The h-only source construction retains the complete original endpoint
pair and adds compatibility on the whole Borel, with the canonical field. -/
theorem TypeAt.exists_compatibly_marked_natural_endpoints (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p t : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B)
      (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)),
      letI := hAE
      letI := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧ Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧ (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      orderOf t = 3 ∧ t ∈ normalizer (W : Set G) ∧
      Disjoint (A ⊔ B) (zpowers t) ∧
      Nat.card ((A ⊔ B) ⊔ zpowers t : Subgroup G) = 192 ∧
      ∃ (dA : NaturalEndpointData A) (dB : NaturalEndpointData B),
        B ≤ dA.carrier ∧ A ≤ dB.carrier ∧ t ∈ dA.carrier ⊓ dB.carrier ∧
        dA.carrier ⊓ dB.carrier = (A ⊔ B) ⊔ zpowers t ∧
        U0.map dA.embedding = ((dA.symplectic_quotient.toMonoidHom.comp
          (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range ∧
        U0.map dB.embedding = ((dB.symplectic_quotient.toMonoidHom.comp
          (QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G))))).comp (inclusion hAB)).range ∧
        ∃ marking : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups dA.carrier (dA.carrier ⊓ dB.carrier) dB.carrier
            inf_le_left inf_le_right)
          (ChapterF.GreenBook.LieModels.LinearThree.amalgam Matrix.PSL3Four.F),
          (A.subgroupOf dA.carrier).map marking.left.toMonoidHom=
            pCore 2 (pointParabolic Matrix.PSL3Four.F) ∧
          (B.subgroupOf dB.carrier).map marking.right.toMonoidHom=
            pCore 2 (lineParabolic Matrix.PSL3Four.F) := by
  obtain ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hBconj,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,ht3,htW,hdis,h192,
    dA,dB,hBdA,hAdB,htd,hinter,hRA,hRB⟩ := h.exists_paired_natural_endpoints
  let := hAE
  let := hBE
  have hJ192 : Nat.card (dA.carrier ⊓ dB.carrier : Subgroup G)=192 := by
    rw [hinter]
    exact h192
  obtain ⟨e⟩ := dA.compatible_borel_marking dB hA16 hB16 hAB hBA hBdA hAdB hRA hRB hJ192
  have kernel_core {X : Subgroup G} [IsElementaryAbelian 2 X]
      (d : NaturalEndpointData X) : X.subgroupOf d.carrier=pCore 2 d.carrier := by
    obtain ⟨f,_,_,hf,_⟩ := d.exists_affine_marking
    apply Subgroup.map_injective (f:=f.toMonoidHom) f.injective
    rw [hf,pCore_map_iso,Matrix.SL2.affine_twoCore_eq]
  let marking := e.trans canonical_flag_iso
  refine ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hBconj,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,ht3,htW,hdis,h192,
    dA,dB,hBdA,hAdB,htd,hinter,hRA,hRB,marking,?_,?_⟩
  · rw [kernel_core dA,pCore_map_iso]
  · rw [kernel_core dB,pCore_map_iso]

end CFSG.Quasithin.HigmanSims
