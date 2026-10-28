module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.Sections
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor.Binary.Calculation
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.BinaryResidual

/-!
# Actor rigidity in the second parabolic of G₂(2)′

The actual derived parabolic embeds in the binary long local group, whose
SL₂(2) quotient map has a two-group kernel. Its intrinsic two-core contains
C(1)D(1). The square condition against that element forces every element of
the actor's quotient image to square to one, including all radical
perturbations. The image and kernel are thus two-groups, so the actor is a
two-group. Two-perfection then makes it trivial.

The argument proves the requested subnormal-actor statement without using
subnormality. It supplies the binary second-parabolic case in the block
exclusion for Aschbacher–Smith 2.3.9(7), printed p.526. Root calculations
and the quotient map use the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

/-- A square-trivial subnormal two-perfect actor in the actual second
parabolic of G₂(2)′ is trivial. -/
theorem binary_actor_eq_bot
    (X : Subgroup BinaryParabolicPair.derivedSecond) (_hX : X.IsSubnormal)
    (hp : IsPPerfect 2 X)
    (hsq : ∀ q ∈ pCore 2 BinaryParabolicPair.derivedSecond, ∀ x ∈ X,
      (⁅q,x⁆ : BinaryParabolicPair.derivedSecond)^2 = 1) : X = ⊥ := by
  let P := BinaryParabolicPair.derivedSecond
  let g := BinaryParabolicPair.DerivedModel.subtype.comp P.subtype
  let i : P →* local₂ (F := ZMod 2) := g.codRestrict _ (by
    intro x
    rw [local₂_binary]
    exact x.property)
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : local₂ (F := ZMod 2) => z.val) h))
  let f := (longSLHom (F := ZMod 2)).comp i
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((longSLHom (F := ZMod 2)).comp i).ker
    rw [← MonoidHom.comap_ker, longSLHom_ker, ← local₂_pCore]
    exact pCore_isPGroup.comap_of_injective i hi
  obtain ⟨q, hq, hqg⟩ := binary_long_core_root_mem_derivedSecond_core
  change g q = rootC (1 : ZMod 2) * rootD 1 at hqg
  have himage : IsPGroup 2 (X.map f) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨1, Subtype.ext ?_⟩
    change f x ^ 2 = 1
    apply binary_long_square_image (i x)
    change ⁅rootC (1 : ZMod 2) * rootD 1, g x⁆ ^ 2 = 1
    have hs := congrArg g (hsq q hq x hx)
    simpa only [map_pow, map_commutatorElement, map_one, hqg] using hs
  have hpX : IsPGroup 2 X :=
    (himage.comap_of_ker_isPGroup f hker).to_le (by
      intro x hx
      exact ⟨x, hx, rfl⟩)
  have he := hp.hom_eq_one_of_isPGroup hpX (MonoidHom.id X)
  apply X.eq_bot_iff_forall.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

end
