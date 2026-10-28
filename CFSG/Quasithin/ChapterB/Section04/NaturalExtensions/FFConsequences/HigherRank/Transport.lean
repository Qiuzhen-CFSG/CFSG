module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.DualExtensions
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.SmallFields

/-!
# Transport of higher-dimensional binary two-factor extensions

For the dual quotient orientation, common-center elementary roots act
quadratically on the original extension. This follows from sparse commuting
matrix relations, after choosing an ordinary linear section of the actual
quotient. Both group and module coordinates are transported through the
original marking. Prime-field transport keeps the submodule and quotient
literal for every carrier of the field of two elements.

These are unconditional inputs to the missing higher-dimensional branch of
Aschbacher–Smith B.4.9(2)(i), printed pp.92–95. The same-orientation root
calculation and construction of an axis four-group remain separate obligations;
this module does not yet assert the full FF splitting conclusion.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace HigherRank

private noncomputable def dualEquiv {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {σ : Representation (ZMod 2) G X} {τ : Representation (ZMod 2) G Y}
    (e : σ.Equiv τ) : σ.dual.Equiv τ.dual :=
  .mk e.toLinearEquiv.symm.dualMap (by
    intro g
    ext f y
    change f (σ g⁻¹ (e.symm y)) = f (e.symm (τ g⁻¹ y))
    congr 1
    apply e.toLinearEquiv.injective
    have h := LinearMap.congr_fun (e.isIntertwining' g⁻¹) (e.symm y)
    change e (σ g⁻¹ (e.symm y)) = τ g⁻¹ (e (e.symm y)) at h
    change e (σ g⁻¹ (e.symm y)) = e (e.symm (τ g⁻¹ y))
    simpa only [e.apply_symm_apply] using h)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {n : ℕ} {ρ : Representation (ZMod 2) G V}

/-- Pull the common-center roots back to the original actors. The result is
quadraticity on the given extension, not only on its two composition factors. -/
theorem binary_dual_root_product (d : DoubleNatural BinaryField.two n ρ)
    (hn : 5 ≤ n)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) :
    (ρ (d.natural.groupEquiv.symm (SpecialLinearGroup.transvection hij 1)) - 1) *
      (ρ (d.natural.groupEquiv.symm (SpecialLinearGroup.transvection hik 1)) - 1) = 0 := by
  let f := d.natural.groupEquiv
  let τ := ρ.comp f.symm.toMonoidHom
  let N : Subrepresentation τ :=
    ⟨d.space.toSubmodule, fun g _ hv => d.space.apply_mem_toSubmodule (f.symm g) hv⟩
  let en : N.toRepresentation.Equiv (linearNatural BinaryField.two n) :=
    .mk d.natural.linearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact (d.natural.intertwines (f.symm g) v).trans (by rw [f.apply_symm_apply]; rfl))
  let eq : N.quotientRepresentation.Equiv N.toRepresentation.dual :=
    .mk eQ.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      have h := LinearMap.congr_fun (eQ.isIntertwining' (f.symm g)) v
      change eQ (d.space.quotientRepresentation (f.symm g) v) =
        d.space.toRepresentation.dual (f.symm g) (eQ v) at h
      change eQ (d.space.quotientRepresentation (f.symm g) v) w = _
      rw [h]
      change eQ v (d.space.toRepresentation ((f.symm g)⁻¹) w) =
        eQ v (d.space.toRepresentation (f.symm g⁻¹) w)
      rw [f.symm.map_inv])
  exact dual_extension_root_product hn τ N en (eq.trans (dualEquiv en)) hij hik

variable {F : BinaryField}

/-- Replace only the natural coordinates by prime-field coordinates. The
original representation, natural submodule and quotient map remain literal. -/
noncomputable def binaryForm (d : DoubleNatural F n ρ) (hF : F.degree = 1) :
    DoubleNatural BinaryField.two n ρ := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  let eTop : ActionEquiv (d.space.toRepresentation.comp (⊤ : Subgroup G).subtype)
      (linearNatural F n) :=
    ⟨Subgroup.topEquiv.trans d.natural.groupEquiv, d.natural.linearEquiv,
      fun g v => d.natural.intertwines g v⟩
  let e := ChapterK.Linear.Natural.primeFieldActionEquiv d.space.toRepresentation ⊤ F hF n eTop
  exact {
    faithful := d.faithful
    space := d.space
    natural :=
      ⟨Subgroup.topEquiv.symm.trans e.groupEquiv, e.linearEquiv,
        fun g v => e.intertwines ⟨g, Subgroup.mem_top g⟩ v⟩
    quotient := d.quotient }

/-- Actual degree-one `DoubleNatural` application, retaining the original
actors and module and covering every higher dimension in the source. -/
theorem degree_one_dual_root_product (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) :
    (ρ ((binaryForm d hF).natural.groupEquiv.symm
      (SpecialLinearGroup.transvection hij 1)) - 1) *
      (ρ ((binaryForm d hF).natural.groupEquiv.symm
        (SpecialLinearGroup.transvection hik 1)) - 1) = 0 :=
  binary_dual_root_product (binaryForm d hF) (by omega) eQ hij hik

end HigherRank
end CFSG.Quasithin.ChapterB.NaturalExtensions
