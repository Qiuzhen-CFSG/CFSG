module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
public import Theory.Mathieu.M22.CentralCover.QuintetRestriction
public import Theory.GroupTheory.Commutator.PerfectSmallIndex

/-!
# The full native actor image of the original M₂₂-code normalizer residual

The original whole-code marking lifts every native tetrad-pointwise actor
through the relative normalizer of its fixed four-space. Its solvable
residual therefore covers that actor: the reverse containment follows
because every perfect subgroup of the order-3840 quintet lies in the
perfect actor of index four. The theorem retains the exact normalizer map,
so its kernel and its selected five-space marking can be used together.

This fills the local-image premise of the central-double-cover restriction
in Aschbacher--Smith 8.2.10(3), printed p.721, using the four-space recovery
of H.16.3(2,4), printed p.403.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Sporadic.Mathieu
open MathieuCode MathieuCode.M22Quintet
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
open M22ChapterH.Quintet
variable {G : Type*} [Group G] [Finite G]

private theorem native_actor_index : naturalActor.index = 4 := by
  have hQ : Nat.card Q = 3840 := by
    have hk : Nat.card (pCore 2 Q) = 32 :=
      (card_map_of_injective Q.subtype_injective).symm.trans M22ChapterH.Quintet.core_card
    have hq : Nat.card (Q ⧸ pCore 2 Q) = 120 :=
      (Nat.card_congr M22ChapterH.Quintet.quotientEquiv.toEquiv).trans (by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Q),hq,hk]
  have ha : Nat.card naturalActor = 960 := by
    rw [←Nat.card_congr naturalActorEquiv.toEquiv]
    exact Atlas.Codes.tetradPointAffine_card _
  have hh := naturalActor.card_mul_index
  rw [ha,hQ] at hh
  omega

/-- The original relative normalizer maps its full solvable residual onto the
literal native affine actor, retaining the supplied normalizer homomorphism. -/
theorem marked_normalizer_residual_range
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* MathieuCode.m22PairStabilizer) (hq : m22ToPairStabilizer.range ≤ q.range)
    (F : Additive W ≃ₗ[ZMod 2] M22Code)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        m22OuterCodeRepresentation (q l) (F (Additive.ofMul w)))
    (hspace : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ V4)
    (f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* Q)
    (hf : ∀ l, (f l).val = q ⟨l,l.property.1⟩) :
    (f.comp (inclusion (Chapter8.Section02.Normalizer.localResidual_le L U))).range =
      naturalActor := by
  let N := L ⊓ normalizer (U : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let j : R →* N := inclusion (Chapter8.Section02.Normalizer.localResidual_le L U)
  have hactor : naturalActor ≤ f.range := by
    intro a ha
    obtain ⟨l,hl⟩ := hq (naturalActor_inner ⟨a,ha⟩)
    have ht : q l ∈ Q := hl.symm ▸ a.property
    rw [←V4_stabilizer_eq_native] at ht
    have hlU : l.val ∈ normalizer (U : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hh := (ht (F (Additive.ofMul ⟨x,hUW hx⟩))).mpr ((hspace _).mp hx)
        rw [←hF,←hspace] at hh
        exact hh
      · intro hx
        have hxW := (mem_normalizer_iff.mp (hLW l.property) x).mpr (hUW hx)
        apply (hspace ⟨x,hxW⟩).mpr
        apply (ht _).mp
        rw [←hF]
        exact (hspace _).mp hx
    refine ⟨⟨l,⟨l.property,hlU⟩⟩,Subtype.ext ?_⟩
    exact (hf _).trans hl
  let b : solvableResidual N ≃* R :=
    (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
  have hb (x : R) : (b.symm x).val = j x := by
    apply Subtype.ext
    exact congrArg (fun y : R => (y : G)) (b.apply_symm_apply x)
  have hrange : (f.comp j).range = (solvableResidual N).map f := by
    ext y
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨b.symm r,(b.symm r).property,congrArg f (hb r)⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨b ⟨x,hx⟩,rfl⟩
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : Group.IsPerfect (f.comp j).range := Group.IsPerfect.range _
  change (f.comp j).range = naturalActor
  apply le_antisymm (le_of_isPerfect_of_index_le_four _ _ native_actor_index.le)
  let H := naturalActor.subgroupOf f.range
  let : Group.IsPerfect naturalActor := Matrix.SL2.isPerfect_of_equiv_affine _
    (by rw [Matrix.PSL3Four.card_F]) naturalActorAffineEquiv
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hactor).symm.toMonoidHom)
    (subgroupOfEquivOfLe hactor).symm.surjective
  have hh := map_mono (f := f.range.subtype) (le_solvableResidual_of_isPerfect H)
  change (naturalActor.subgroupOf f.range).map f.range.subtype ≤ _ at hh
  rw [map_subgroupOf_eq_of_le hactor,←map_solvableResidual_eq f.rangeRestrict
    f.rangeRestrict_surjective,map_map] at hh
  exact hrange.symm ▸ hh

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeNormalizer
