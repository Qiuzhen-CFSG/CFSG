module
public import Theory.GroupAction.FixedQuotientMoved
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters

/-!
# The natural quotient on the moved intrinsic center

A natural coefficient map on the center of the commutator core gives the
literal conjugation quotient model on [Z(O₂(K)),K]. Two-perfectness and
centralization by O₂(K) identify this subgroup with the moved intrinsic
center; an invertible displacement in SL₃(2) preserves coefficient
surjectivity on the commutator subgroup.

Source: Aschbacher--Smith 13.6.22, printed pp.932--933, using C.1.34.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open MSSourceModels NonabelianCenters
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

private theorem sourceU_eq_moved_intrinsic_center (hp : IsPPerfect 2 K)
    (hc : (center (blockU K)).map (blockU K).subtype ≤ centralizer (pCore 2 K : Set K)) :
    sourceU K = ⁅((center (blockU K)).map (blockU K).subtype).map K.subtype, K⁆ := by
  have hs : (K.subgroupOf (K ⊔ (⊥ : Subgroup G))).IsSubnormal := by
    have hn : (K.subgroupOf (K ⊔ (⊥ : Subgroup G))).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer bot_le)
    exact hn.isSubnormal
  let Z := ((center (blockU K)).map (blockU K).subtype).map K.subtype
  have hZ : Z = Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ K ⊥) := by
    rw [msQ_eq_ambient_blockU K ⊥ hs hp]
    change _ = (center ((blockU K).map K.subtype)).map ((blockU K).map K.subtype).subtype
    exact (map_embeddedCenter (blockU K) K.subtype K.subtype_injective)
  change sourceU K = ⁅Z,K⁆
  rw [hZ]
  apply sourceU_eq_moved_center K ⊥ hs hp
  rw [← hZ]
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact congrArg Subtype.val (hc hx y hy)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open MSSourceModels NonabelianCenters
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

private noncomputable def centerAmbientEquiv : center (blockU K) ≃*
    (((center (blockU K)).map (blockU K).subtype).map K.subtype) :=
  ((center (blockU K)).equivMapOfInjective (blockU K).subtype (blockU K).subtype_injective).trans
    (((center (blockU K)).map (blockU K).subtype).equivMapOfInjective K.subtype K.subtype_injective)

private noncomputable def centerModel
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (p : center (blockU K) →* Multiplicative BinaryLinearThree.Vector)
    (hp : Function.Surjective p)
    (hk : ∀ z, p z = 1 ↔ (z.val : K) ∈ center K)
    (he : ∀ (k : K) (x y : center (blockU K)),
      (y.val : K) = k * (x.val : K) * k⁻¹ →
      (p y).toAdd = BinaryLinearThree.W (linearThreeActor e k) (p x).toAdd) :
    ConjugationQuotientModel K
      (((center (blockU K)).map (blockU K).subtype).map K.subtype) BinaryLinearThree.W := by
  let Z := ((center (blockU K)).map (blockU K).subtype).map K.subtype
  let f : center (blockU K) ≃* Z := centerAmbientEquiv
  have hn : K ≤ normalizer (Z : Set G) := by
    have h := ((center (blockU K)).map (blockU K).subtype).le_normalizer_map K.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  refine { normalizes := hn
           actor := linearThreeActor e
           quotient := p.comp f.symm.toMonoidHom
           surjective := hp.comp f.symm.surjective
           kernel := ?_
           equivariant := ?_ }
  · ext z
    obtain ⟨x,rfl⟩ := f.surjective z
    change p (f.symm (f x)) = 1 ↔ _
    rw [f.symm_apply_apply, hk]
    constructor
    · intro hx k hkm
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨k,hkm⟩)
    · intro hx
      exact mem_center_iff.mpr (fun k => Subtype.ext (hx k k.property))
  · intro k z
    obtain ⟨x,rfl⟩ := f.surjective z
    apply Multiplicative.toAdd.injective
    change (p (f.symm (Z.normalizerMonoidHom ⟨k,hn k.property⟩ (f x)))).toAdd =
      BinaryLinearThree.W (linearThreeActor e k) (p (f.symm (f x))).toAdd
    rw [f.symm_apply_apply]
    apply he
    have hv := congrArg (fun y : Z => (y : G))
      (f.apply_symm_apply (Z.normalizerMonoidHom ⟨k,hn k.property⟩ (f x)))
    have hfval (z : center (blockU K)) : (f z : G) = ((z.val : K) : G) := rfl
    rw [hfval] at hv
    exact Subtype.ext hv

private def movementMatrix : BinaryLinearThree.Group :=
  ⟨!![0,1,0;0,0,1;1,1,0], by decide⟩

private theorem natural_full_movement :
    ∃ g : BinaryLinearThree.Group,
      Function.Surjective (fun v => BinaryLinearThree.W g v - v) := by
  refine ⟨movementMatrix, ?_⟩
  decide +kernel

theorem natural_source_model_of_center_coefficients
    (hperfect : IsPPerfect 2 K)
    (hc : (center (blockU K)).map (blockU K).subtype ≤ centralizer (pCore 2 K : Set K))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (p : center (blockU K) →* Multiplicative BinaryLinearThree.Vector)
    (hp : Function.Surjective p)
    (hk : ∀ z, p z = 1 ↔ (z.val : K) ∈ center K)
    (he : ∀ (k : K) (x y : center (blockU K)),
      (y.val : K) = k * (x.val : K) * k⁻¹ →
      (p y).toAdd = BinaryLinearThree.W (linearThreeActor e k) (p x).toAdd) :
    ∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e := by
  rw [sourceU_eq_moved_intrinsic_center hperfect hc]
  let m := centerModel e p hp hk he
  exact ⟨m.moved (linearThreeActor_surjective e) natural_full_movement, rfl⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
