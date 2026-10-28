module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Basic
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The local residual in the faithful shadow image

The range restriction gives a surjection from the actual N_L(V) to its action
image. Surjections preserve O², so the image of the embedded O²(N_L(V)) is
the embedded O² of the local image. An actual S₅ comparison therefore gives
an actual A₅ comparison for L_V⁺. This makes no splitting assumption on C_M(V).

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
variable {G : Type*} [Group G]

noncomputable def localImageMap (L : Subgroup G) (g r z : G) :
    localNormalizer L r z →* imageSubgroup L g r z (localNormalizer L r z) :=
  ((shadowAction L g r z).rangeRestrict.comp (inclusion (localNormalizer_le L g r z))).codRestrict
    _ (fun a => ⟨inclusion (localNormalizer_le L g r z) a, a.property, rfl⟩)

theorem localImageMap_surjective (L : Subgroup G) (g r z : G) :
    Function.Surjective (localImageMap L g r z) := by
  rintro ⟨x, ⟨m, hm, rfl⟩⟩
  exact ⟨⟨m.val, hm⟩, rfl⟩

theorem residual_image [Finite G] (L : Subgroup G) (g r z : G) :
    imageSubgroup L g r z (localResidual L r z) =
      (pResidual 2 (imageSubgroup L g r z (localNormalizer L r z))).map
        (imageSubgroup L g r z (localNormalizer L r z)).subtype := by
  rw [← map_pResidual_of_surjective 2 (localImageMap L g r z)
    (localImageMap_surjective L g r z), map_map]
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨a, ha, he⟩ := hm
    refine ⟨a, ha, ?_⟩
    have ham : inclusion (localNormalizer_le L g r z) a = m := Subtype.ext he
    change (shadowAction L g r z).rangeRestrict (inclusion (localNormalizer_le L g r z) a) = _
    rw [ham]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨inclusion (localNormalizer_le L g r z) a, ⟨a, ha, rfl⟩, rfl⟩
theorem localResidual_image_equiv [Finite G] (L : Subgroup G) (g r z : G)
    (e : imageSubgroup L g r z (localNormalizer L r z) ≃* Equiv.Perm (Fin 5)) :
    Nonempty (imageSubgroup L g r z (localResidual L r z) ≃* alternatingGroup (Fin 5)) := by
  refine ⟨(MulEquiv.subgroupCongr (residual_image L g r z)).trans ?_⟩
  refine ((pResidual 2 (imageSubgroup L g r z (localNormalizer L r z))).equivMapOfInjective
    _ (imageSubgroup L g r z (localNormalizer L r z)).subtype_injective).symm.trans ?_
  refine (e.subgroupMap (pResidual 2 _)).trans ?_
  exact MulEquiv.subgroupCongr ((map_pResidual 2 e).trans (Equiv.Perm.twoResidual_eq_alternating (Fin 5)))

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
