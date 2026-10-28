module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions.MatrixDerivations
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.SubspaceQuotient

/-!
# Splitting homogeneous binary natural extensions

Every extension of the natural SL₃(2) module by the same natural module splits,
including after any common automorphism marking. Choose an ordinary linear
section of the quotient. Its failure to intertwine is a derivation into the
natural matrix bimodule. The generator calculation in `MatrixDerivations` makes
this derivation inner; subtracting its primitive gives an equivariant section.
Adding that section to the given natural submodule gives the actual product
intertwining equivalence.

This supplies the same-orientation binary case needed in Aschbacher–Smith
B.4.9(2)(i), printed pp.92–94, and B.5.1, pp.100–101, combined manuscript of
1 March 2004. This specialization needs neither an FF assumption nor a separate
finite-dimensionality assumption.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
open SelfExtensions.MatrixDerivations (SL)

namespace SelfExtensions
private abbrev W := BinaryLinearThree.Vector

private lemma natural_matrix (g : SL) :
    LinearMap.toMatrix' (BinaryLinearThree.W g) = g.val :=
  LinearMap.toMatrix'_toLin' g.val

private lemma linear_derivation_inner (a : SL ≃* SL) (d : SL → Module.End (ZMod 2) W)
    (hd : ∀ g h, d (g * h) = (BinaryLinearThree.W (a g)).comp (d h) +
      (d g).comp (BinaryLinearThree.W (a h))) :
    ∃ b : Module.End (ZMod 2) W, ∀ g,
      d g = (BinaryLinearThree.W (a g)).comp b - b.comp (BinaryLinearThree.W (a g)) := by
  let dm : SL → MatrixDerivations.Mat := fun g => LinearMap.toMatrix' (d (a.symm g))
  have hm : MatrixDerivations.IsDerivation dm := by
    intro g h
    dsimp [dm]
    rw [map_mul, hd, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      a.apply_symm_apply, a.apply_symm_apply, natural_matrix, natural_matrix]
  obtain ⟨b,hb⟩ := MatrixDerivations.derivation_inner dm hm
  refine ⟨Matrix.toLin' b, fun g => ?_⟩
  apply LinearMap.toMatrix'.injective
  have hh := hb (a g)
  simpa only [dm, a.symm_apply_apply, map_sub, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin', natural_matrix] using hh

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem split_of_inner (ρ : Representation (ZMod 2) SL V)
    (N : Subrepresentation ρ) (a : SL ≃* SL)
    (en : N.toRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom))
    (eq : N.quotientRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom))
    (hinner : ∀ d : SL → Module.End (ZMod 2) W,
      (∀ g h, d (g * h) = (BinaryLinearThree.W (a g)).comp (d h) +
        (d g).comp (BinaryLinearThree.W (a h))) →
      ∃ b : Module.End (ZMod 2) W, ∀ g,
        d g = (BinaryLinearThree.W (a g)).comp b - b.comp (BinaryLinearThree.W (a g))) :
    Nonempty (ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
      (BinaryLinearThree.W.comp a.toMonoidHom))) := by
  classical
  let σ := BinaryLinearThree.W.comp a.toMonoidHom
  let i : W →ₗ[ZMod 2] V := N.toSubmodule.subtype.comp en.symm.toLinearEquiv.toLinearMap
  let q : V →ₗ[ZMod 2] W := eq.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp en.symm.toLinearEquiv.injective
  have hq : Function.Surjective q := eq.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective
  have hi_equiv (g : SL) (w : W) : ρ g (i w) = i (σ g w) := by
    exact (congrArg Subtype.val (LinearMap.congr_fun (en.symm.isIntertwining' g) w)).symm
  have hq_equiv (g : SL) (v : V) : q (ρ g v) = σ g (q v) := by
    exact LinearMap.congr_fun (eq.isIntertwining' g) (N.toSubmodule.mkQ v)
  have hqi (w : W) : q (i w) = 0 := by
    change eq (N.toSubmodule.mkQ (en.symm w).val) = 0
    rw [show N.toSubmodule.mkQ (en.symm w).val = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (en.symm w).property, map_zero]
  have hqker (v : V) : q v = 0 ↔ v ∈ N.toSubmodule := by
    change eq.toLinearEquiv (N.toSubmodule.mkQ v) = 0 ↔ _
    rw [eq.toLinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨j, hj⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj (w : W) : q (j w) = w := LinearMap.congr_fun hj w
  let δ (g : SL) : W →ₗ[ZMod 2] V := (ρ g).comp j - j.comp (σ g)
  have hδ (g : SL) (w : W) : δ g w ∈ N.toSubmodule := by
    apply (hqker _).mp
    change q (ρ g (j w) - j (σ g w)) = 0
    rw [map_sub, hq_equiv, hqj, hqj, sub_self]
  let d (g : SL) : Module.End (ZMod 2) W :=
    en.toLinearEquiv.toLinearMap.comp ((δ g).codRestrict N.toSubmodule (hδ g))
  have hid (g : SL) (w : W) : i (d g w) = ρ g (j w) - j (σ g w) := by
    change (en.symm (en ⟨δ g w, hδ g w⟩)).val = _
    rw [en.symm_apply_apply]
    rfl
  have hd (g h : SL) : d (g * h) = (σ g).comp (d h) + (d g).comp (σ h) := by
    apply LinearMap.ext
    intro w
    apply hi
    change i (d (g * h) w) = i (σ g (d h w) + d g (σ h w))
    rw [hid, map_add, ← hi_equiv, hid, hid, map_sub,
      map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    abel
  obtain ⟨b, hb⟩ := hinner d hd
  let k : W →ₗ[ZMod 2] V := j - i.comp b
  have hqk (w : W) : q (k w) = w := by
    change q (j w - i (b w)) = w
    rw [map_sub, hqj, hqi, sub_zero]
  have hk (g : SL) (w : W) : ρ g (k w) = k (σ g w) := by
    have hh := hid g w
    rw [hb g] at hh
    change i (σ g (b w) - b (σ g w)) = ρ g (j w) - j (σ g w) at hh
    rw [map_sub, ← hi_equiv] at hh
    change ρ g (j w - i (b w)) = j (σ g w) - i (b (σ g w))
    rw [map_sub]
    apply sub_eq_sub_iff_sub_eq_sub.mpr
    exact hh.symm
  let f : (W × W) →ₗ[ZMod 2] V := i.coprod k
  have hf : Function.Bijective f := by
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      apply bot_unique
      rintro ⟨x,y⟩ hxy
      change i x + k y = 0 at hxy
      have hy : y = 0 := by
        have hh := congrArg q hxy
        simpa only [map_add, hqi, hqk, map_zero, zero_add] using hh
      subst y
      simp only [map_zero, add_zero] at hxy
      have hx : x = 0 := hi (hxy.trans (map_zero i).symm)
      subst x
      rfl
    · intro v
      have hn : v - k (q v) ∈ N.toSubmodule := by
        apply (hqker _).mp
        rw [map_sub, hqk, sub_self]
      refine ⟨(en ⟨v - k (q v), hn⟩, q v), ?_⟩
      change i (en ⟨v - k (q v), hn⟩) + k (q v) = v
      have hh : i (en ⟨v - k (q v), hn⟩) = v - k (q v) := by
        change (en.symm (en ⟨v - k (q v), hn⟩)).val = _
        rw [en.symm_apply_apply]
      rw [hh, sub_add_cancel]
  refine ⟨(Representation.Equiv.mk (LinearEquiv.ofBijective f hf) ?_).symm⟩
  intro g
  apply LinearMap.ext
  intro w
  change i (σ g w.1) + k (σ g w.2) = ρ g (i w.1 + k w.2)
  rw [map_add, hi_equiv, hk]

end SelfExtensions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- An extension of two natural binary modules with a common marking splits.
The FF hypothesis in B.4.9(2)(i) is unnecessary for this particular case. -/
theorem homogeneous_splitting (ρ : Representation (ZMod 2) SL V)
    (N : Subrepresentation ρ) (a : SL ≃* SL)
    (hN : Nonempty (N.toRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)))
    (hQ : Nonempty (N.quotientRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom))) :
    Nonempty (ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
      (BinaryLinearThree.W.comp a.toMonoidHom))) := by
  obtain ⟨eN⟩ := hN
  obtain ⟨eQ⟩ := hQ
  exact SelfExtensions.split_of_inner ρ N a eN eQ (SelfExtensions.linear_derivation_inner a)

/-- The actual intertwining equivalence realizing homogeneous splitting. -/
noncomputable def homogeneousEquiv (ρ : Representation (ZMod 2) SL V)
    (N : Subrepresentation ρ) (a : SL ≃* SL)
    (eN : N.toRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom))
    (eQ : N.quotientRepresentation.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) :
    ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
      (BinaryLinearThree.W.comp a.toMonoidHom)) :=
  Classical.choice (homogeneous_splitting ρ N a ⟨eN⟩ ⟨eQ⟩)

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
