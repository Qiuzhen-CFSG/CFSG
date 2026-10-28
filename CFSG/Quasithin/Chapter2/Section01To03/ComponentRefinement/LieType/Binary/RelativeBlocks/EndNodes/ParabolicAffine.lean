module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.ParabolicAffine.Point
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.FlagGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.AffineModule

/-!
# The affine isomorphisms for both binary end-node flags

The component Sylow identifies the source flag with the central transvection's
image line or fixed hyperplane. The line stabilizer fixes its unique nonzero
vector. Inverse duality carries the hyperplane stabilizer to the stabilizer of
its defining covector. The point-stabilizer calculation then constructs the
whole affine group, with a compatible contragredient quotient reparametrization.

The resulting equivalence maps the intrinsic two-core onto translations and
intertwines its conjugation action with the actual column-vector action.
Only the intrinsic flag stabilizer is identified here. The parent component-orbit
embedding uses this seed while retaining all permutations induced by S.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526; the associated block
module uses the conventions of C.1.7/C.1.12, printed pp.123–124.
-/

public section

open BinaryLinear BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra Subgroup
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes.ParabolicAffine
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem parabolic_ker_iff_dual_fixed (f : Module.Dual (ZMod 2) V) (g : BinaryLinear.GL V) :
    g ∈ parabolic f.ker ↔ dualGroupEquiv g f = f := by
  constructor
  · intro hg
    ext v
    change f (g.symm v) = f v
    have hzero : f (g.symm v) = 0 ↔ f v = 0 := (hg (g.symm v)).symm.trans (by simp)
    by_cases hv : f v = 0
    · exact (hzero.mpr hv).trans hv.symm
    · have hbinary : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      rw [hbinary _ hv, hbinary _ (mt hzero.mp hv)]
  · intro hg v
    have hv := LinearMap.congr_fun hg (g v)
    change f (g.symm (g v)) = f (g v) at hv
    rw [g.symm_apply_apply] at hv
    change f (g v) = 0 ↔ f v = 0
    rw [hv]

/-- Inverse duality identifies the actual hyperplane stabilizer with a point stabilizer. -/
noncomputable def hyperplanePointEquiv (f : Module.Dual (ZMod 2) V) :
    parabolic f.ker ≃* pointStabilizer f :=
  ((dualGroupEquiv (V := V)).subgroupMap (parabolic f.ker)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      change g ∈ (parabolic f.ker).map (dualGroupEquiv (V := V)).toMonoidHom ↔ _
      rw [mem_map_equiv, parabolic_ker_iff_dual_fixed, MulEquiv.apply_symm_apply]
      rfl))

/-- Coordinates on the annihilator, whose dimension is exactly one less than the ambient dimension. -/
noncomputable def annihilatorBasis {x : V} (hx : x ≠ 0) {n : ℕ}
    (hn : Module.finrank (ZMod 2) V = n) : annihilator x ≃ₗ[ZMod 2] Vector (n - 1) :=
  LinearEquiv.ofFinrankEq _ _ (by
    obtain ⟨f,hf⟩ := exists_pairing hx
    have h := finrank_annihilator hf
    rw [hn] at h
    simp only [Vector, Module.finrank_pi, Fintype.card_fin]
    omega)

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

/-- The singleton flag stabilizer in the component, using its supplied PSL matrix model. -/
noncomputable def flagParabolicEquiv (e : L ≃* PSL n) (F : Flag n) (W : Space n)
    (hF : F.spaces = {W}) : flagStabilizer e F ≃* parabolic W :=
  ((linearModel e).subgroupMap (flagStabilizer e F)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      change g ∈ (flagStabilizer e F).map (linearModel e).toMonoidHom ↔ _
      rw [mem_map_equiv, mem_flagStabilizer, hF]
      simp only [Finset.mem_singleton, forall_eq, MulEquiv.apply_symm_apply]
      rfl))

variable {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    {e : L ≃* PSL n} {t : L}

/-- The source line end node is the full affine group in natural dimension n−1. -/
noncomputable def lineFlagAffineEquiv (c : TransvectionCoordinates e t)
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1}) : flagStabilizer e F ≃* Affine (n - 1) :=
  (flagParabolicEquiv e F c.line (c.flag_spaces_eq_line h ht F hSF hF)).trans
    ((MulEquiv.subgroupCongr (parabolic_line_eq c.vector_ne_zero)).trans
      (pointAffineEquiv c.vector_ne_zero (annihilatorBasis c.vector_ne_zero
        (Module.finrank_fin_fun (ZMod 2)))))

/-- The source hyperplane end node has the same affine model through inverse duality. -/
noncomputable def hyperplaneFlagAffineEquiv (c : TransvectionCoordinates e t)
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {n - 1}) : flagStabilizer e F ≃* Affine (n - 1) :=
  (flagParabolicEquiv e F c.hyperplane (c.flag_spaces_eq_hyperplane h ht F hSF hF)).trans
    ((hyperplanePointEquiv c.functional).trans
      (pointAffineEquiv c.functional_ne_zero (annihilatorBasis c.functional_ne_zero
        (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_fin_fun (ZMod 2)))))

/-- The seed equivalence consumed by the parent finite-power block embedding.
No restriction to degrees four and five or further local-overgroup premise is needed. -/
noncomputable def flagAffineEquiv (c : TransvectionCoordinates e t)
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1} ∨ F.types = {n - 1}) : flagStabilizer e F ≃* Affine (n - 1) := by
  classical
  exact if hline : F.types = {1} then lineFlagAffineEquiv c h ht F hSF hline
    else hyperplaneFlagAffineEquiv c h ht F hSF (hF.resolve_left hline)

variable (c : TransvectionCoordinates e t)
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1} ∨ F.types = {n - 1})

/-- The intrinsic two-core becomes exactly the translation subgroup. -/
theorem flagAffineEquiv_twoCore :
    (pCore 2 (flagStabilizer e F)).map (flagAffineEquiv c h ht F hSF hF).toMonoidHom =
      translations (n - 1) := by
  rw [pCore_map_iso, affine_twoCore_eq]

/-- Actual translation coordinates on the original flag stabilizer’s intrinsic two-core. -/
noncomputable def flagCoreCoordinates :
    pCore 2 (flagStabilizer e F) ≃* Multiplicative (Vector (n - 1)) :=
  ((pCore 2 (flagStabilizer e F)).equivMapOfInjective
    (flagAffineEquiv c h ht F hSF hF).toMonoidHom
    (flagAffineEquiv c h ht F hSF hF).injective).trans
    ((MulEquiv.subgroupCongr (flagAffineEquiv_twoCore c h ht F hSF hF)).trans
      (translationsEquiv (n - 1)).symm)

/-- These coordinates use the same affine equivalence as the whole stabilizer. -/
theorem inl_flagCoreCoordinates (k : pCore 2 (flagStabilizer e F)) :
    SemidirectProduct.inl (flagCoreCoordinates c h ht F hSF hF k) =
      flagAffineEquiv c h ht F hSF hF k.val := by
  let k' : translations (n - 1) := MulEquiv.subgroupCongr
    (flagAffineEquiv_twoCore c h ht F hSF hF)
    ((pCore 2 (flagStabilizer e F)).equivMapOfInjective
      (flagAffineEquiv c h ht F hSF hF).toMonoidHom
      (flagAffineEquiv c h ht F hSF hF).injective k)
  change SemidirectProduct.inl ((translationsEquiv (n - 1)).symm k') = _
  rw [← translationsEquiv_apply]
  exact congrArg Subtype.val ((translationsEquiv (n - 1)).apply_symm_apply k')

/-- Conjugation on the original two-core is precisely the published column-vector action. -/
theorem flagCoreCoordinates_conj (g : flagStabilizer e F)
    (k : pCore 2 (flagStabilizer e F)) :
    flagCoreCoordinates c h ht F hSF hF (MulAut.conjNormal g k) =
      naturalAction (n - 1) (flagAffineEquiv c h ht F hSF hF g).right
        (flagCoreCoordinates c h ht F hSF hF k) := by
  apply SemidirectProduct.inl_injective (φ := naturalAction (n - 1))
  rw [inl_flagCoreCoordinates, MulAut.conjNormal_apply, map_mul, map_mul, map_inv,
    ← inl_flagCoreCoordinates, conjugate_inl]

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes.ParabolicAffine

end
