module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.Normalizers.Intertwiners
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# Exclusion of graph automorphisms on both universal-cover models

A noninner automorphism of the actual SL₃(2) group takes the natural module
to its inequivalent dual. Schur's lemma therefore kills every map from the
twisted natural module to the natural module. The fixed-kernel factorization
through the covering projection gives the same vanishing for the twisted
universal cover. Applying it to each product summand excludes an equivalence
with either twisted model, since each original model surjects onto the natural
module. No choice of a coordinate realization of the cover is involved.

This is the graph-automorphism step in the independent C.1.34 cover-rigidity
argument, with the universal-cover convention of Aschbacher–Smith I.1.5–6,
combined manuscript (1 March 2004), printed p.408.
-/

@[expose] public section
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
noncomputable section

private lemma base_outer_intertwiner_zero (a : MulAut MatrixGroup)
    (ha : a ∉ MulAut.innerSubgroup MatrixGroup)
    (f : Representation.IntertwiningMap (base.comp a.toMonoidHom) base) : f = 0 := by
  let e := BinaryLinearThree.AutomorphismAction.naturalOuterEquiv a ha
  let F : base.dual.IntertwiningMap base := f.comp e.symm.toIntertwiningMap
  let : IsIrreducible base := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible base.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  rcases IsIrreducible.bijective_or_eq_zero F with hF | hF
  · exact (BinaryLinearThree.AutomorphismAction.natural_not_equiv_dual
      ⟨(F.ofBijective hF).symm⟩).elim
  · apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f x = 0
    have h := congrArg (fun t : base.dual.IntertwiningMap base => t (e x)) hF
    change f (e.symm (e x)) = 0 at h
    simpa only [e.symm_apply_apply] using h

private lemma cover_outer_intertwiner_zero (a : MulAut MatrixGroup)
    (ha : a ∉ MulAut.innerSubgroup MatrixGroup)
    (f : Representation.IntertwiningMap (cover.comp a.toMonoidHom) base) : f = 0 := by
  let p : Representation.IntertwiningMap (cover.comp a.toMonoidHom) (base.comp a.toMonoidHom) :=
    ⟨projection.toLinearMap, fun g => projection.isIntertwining' (a g)⟩
  have hp : IsCover p := by
    refine ⟨projection_isCover.1, ?_, ?_⟩
    · intro x hx g
      exact projection_isCover.2.1 hx (a g)
    · apply top_unique
      rw [← projection_isCover.2.2]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, x⟩, rfl⟩
      change cover g x - x ∈ Coinvariants.ker (cover.comp a.toMonoidHom)
      have h := Coinvariants.sub_mem_ker (ρ := cover.comp a.toMonoidHom) (a.symm g) x
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, a.apply_symm_apply] using h
  obtain ⟨q, hq⟩ := factor_through_cover p hp f base_fixed
  rw [base_outer_intertwiner_zero a ha q] at hq
  rw [← hq]
  apply IntertwiningMap.ext
  rfl

private lemma product_not_equiv_twist
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) MatrixGroup X)
    (σ : Representation (ZMod 2) MatrixGroup Y)
    (p : Representation.IntertwiningMap (ρ.prod σ) base) (hp : Function.Surjective p)
    (a : MulAut MatrixGroup)
    (hρ : ∀ f : Representation.IntertwiningMap (ρ.comp a.toMonoidHom) base, f = 0)
    (hσ : ∀ f : Representation.IntertwiningMap (σ.comp a.toMonoidHom) base, f = 0) :
    ¬ Nonempty (Representation.Equiv ((ρ.prod σ).comp a.toMonoidHom) (ρ.prod σ)) := by
  rintro ⟨e⟩
  let f := p.comp e.toIntertwiningMap
  have hf₁ := hρ (f.comp (IntertwiningMap.inl (ZMod 2)
    (ρ.comp a.toMonoidHom) (σ.comp a.toMonoidHom)))
  have hf₂ := hσ (f.comp (IntertwiningMap.inr (ZMod 2)
    (ρ.comp a.toMonoidHom) (σ.comp a.toMonoidHom)))
  have hf (x : X × Y) : f x = 0 := by
    have h₁ : f (x.1, 0) = 0 := congrArg (fun t => t x.1) hf₁
    have h₂ : f (0, x.2) = 0 := congrArg (fun t => t x.2) hf₂
    have hx : x = (x.1, 0) + (0, x.2) := by simp
    rw [hx, map_add, h₁, h₂, zero_add]
  have hsur : Function.Surjective f := hp.comp e.surjective
  obtain ⟨x, hx⟩ := hsur (fun _ => 1)
  have hz : (fun _ : Fin 3 => (1 : ZMod 2)) = 0 := hx.symm.trans (hf x)
  exact one_ne_zero (congrFun hz 0)

/-- No outer automorphism stabilizes the mixed universal-cover model. -/
lemma mixed_twist_inner (a : MulAut MatrixGroup)
    (he : Nonempty (Representation.Equiv (mixed.comp a.toMonoidHom) mixed)) :
    a ∈ MulAut.innerSubgroup MatrixGroup := by
  by_contra ha
  exact product_not_equiv_twist cover base
    (projection.comp (IntertwiningMap.fst (ZMod 2) cover base))
    (projection_isCover.1.comp (fun v => ⟨(v, 0), rfl⟩))
    a (cover_outer_intertwiner_zero a ha) (base_outer_intertwiner_zero a ha) he

/-- No outer automorphism stabilizes the doubled universal-cover model. -/
lemma doubled_twist_inner (a : MulAut MatrixGroup)
    (he : Nonempty (Representation.Equiv (doubled.comp a.toMonoidHom) doubled)) :
    a ∈ MulAut.innerSubgroup MatrixGroup := by
  by_contra ha
  exact product_not_equiv_twist cover cover
    (projection.comp (IntertwiningMap.fst (ZMod 2) cover cover))
    (projection_isCover.1.comp (fun v => ⟨(v, 0), rfl⟩))
    a (cover_outer_intertwiner_zero a ha) (cover_outer_intertwiner_zero a ha) he

end
end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
