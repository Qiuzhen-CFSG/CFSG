module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic

/-!
# The actual C.2.7 symplectic marking on the full core quotient

The centerless symplectic core makes the literal core-to-star comparison
bijective. Transporting the original marked intersection through that same
map gives a native parabolic. No independent identification of the star and
normalizer images, or reversed action on an elementary support, is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The same C.2.7 marked intersection is a parabolic under the full core marking. -/
theorem raw_symplectic_core_marked_parabolic
    {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hfour : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Sp F) :
    ∃ g : Sp F,
      ((N.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj g).toMonoidHom = pointParabolic ∨
      ((N.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).map
        (MulAut.conj g).toMonoidHom = planeParabolic := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Theory.GroupTheory.FixedElementary.map_center,EvenProjective.center_eq_bot,Subgroup.map_bot]
  have hinj : Function.Injective (coreToStar hi.normalizes) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((coreToStar_ker_central_from_source hi).trans_eq hz)
  let c := MulEquiv.ofBijective (coreToStar hi.normalizes)
    ⟨hinj,coreToStar_surjective hi.normalizes⟩
  let es := c.symm.trans e
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) =
      es.toMonoidHom.comp (toStarImage L R) := by
    apply MonoidHom.ext
    intro x
    change e (QuotientGroup.mk' _ x) = e (c.symm (c (QuotientGroup.mk' _ x)))
    rw [c.symm_apply_apply]
  have hm : (N.subgroupOf L).map (toStarImage L R) =
      (starM L R N).subgroupOf (starImage L R L) := by
    apply map_injective (starImage L R L).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (starM_le L R N)]
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,mem_sup_left x.property⟩,⟨hx,x.property⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [he,←map_map,hm]
  exact star_symplectic_marked_parabolic_from_source hi es hfour

end CFSG.Quasithin.Chapter15.Section01
