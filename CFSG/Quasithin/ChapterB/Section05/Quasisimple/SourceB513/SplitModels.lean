module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.BinaryOffender.DualFixedSupplement
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# Contragredient ratios for the reducible B.5.1 models

Finite products commute with duality. The natural-plus-dual model is
self-dual, while repeated natural models use the same graph twist on every
copy. Thus duality preserves the quadratic ratio of all three reducible
models. The ratio identities are exposed separately from their coordinate
maps so source applications do not unfold the matrix constructions.

Source: Aschbacher–Smith B.5.13, printed p.111, cases B.5.1(1)(ii)–(iv).
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
open ExtensionConsequences
variable {G H J V W X : Type*} [Group G] [Group H] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}
  {τ : Representation (ZMod 2) J X}
noncomputable def ActionEquiv.trans (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := by change f.linearEquiv (e.linearEquiv (ρ g v)) = _; rw [e.intertwines,f.intertwines]; rfl
noncomputable def ActionEquiv.dual (e : ActionEquiv ρ σ) : ActionEquiv ρ.dual σ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    apply LinearMap.ext
    intro w
    change f (ρ g⁻¹ (e.linearEquiv.symm w)) = f (e.linearEquiv.symm (σ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines,e.linearEquiv.apply_symm_apply,e.linearEquiv.apply_symm_apply,map_inv]
theorem ActionEquiv.quadraticRatio_eq (e : ActionEquiv ρ σ) : quadraticRatio ρ = quadraticRatio σ := by
  apply le_antisymm
  · let f := actionSymm e
    exact quadraticRatio_le_of_injective_equivariant σ ρ f.groupEquiv.toMonoidHom
      f.groupEquiv.injective f.linearEquiv f.intertwines
  · exact quadraticRatio_le_of_injective_equivariant ρ σ e.groupEquiv.toMonoidHom
      e.groupEquiv.injective e.linearEquiv e.intertwines
noncomputable def ActionEquiv.repeated (e : ActionEquiv ρ σ) (r : ℕ) :
    ActionEquiv (QuasisimpleSource.repeated ρ r) (QuasisimpleSource.repeated σ r) where
  groupEquiv := e.groupEquiv
  linearEquiv := LinearEquiv.piCongrRight fun _ => e.linearEquiv
  intertwines g v := funext fun i => e.intertwines g (v i)

noncomputable def repeatedDualEquiv (ρ : Representation (ZMod 2) G V) (r : ℕ) :
    ActionEquiv (repeated ρ.dual r) (repeated ρ r).dual where
  groupEquiv := MulEquiv.refl G
  linearEquiv := LinearMap.lsum (ZMod 2) (fun _ : Fin r => V) (ZMod 2)
  intertwines g v := by
    apply LinearMap.ext
    intro w
    change (∑ i, (ρ.dual g (v i)).comp (LinearMap.proj i)) w =
      (∑ i, (v i).comp (LinearMap.proj i)) (fun i => ρ g⁻¹ (w i))
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rfl

noncomputable def naturalPairSelfDual (ρ : Representation (ZMod 2) G V)
    [FiniteDimensional (ZMod 2) V] : ActionEquiv (ρ.prod ρ.dual) (ρ.prod ρ.dual).dual where
  groupEquiv := MulEquiv.refl G
  linearEquiv := ((LinearEquiv.prodComm (ZMod 2) V (Module.Dual (ZMod 2) V)).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl (ZMod 2) _) (Module.evalEquiv (ZMod 2) V))).trans
      (Module.dualProdDualEquivDual (ZMod 2) V (Module.Dual (ZMod 2) V))
  intertwines g v := by
    apply LinearMap.ext
    intro w
    change (ρ.dual g v.2) w.1 + (ρ g v.1 |> Module.Dual.eval (ZMod 2) V) w.2 =
      v.2 (ρ g⁻¹ w.1) + (ρ.dual g⁻¹ w.2) v.1
    change v.2 (ρ g⁻¹ w.1) + w.2 (ρ g v.1) =
      v.2 (ρ g⁻¹ w.1) + w.2 (ρ (g⁻¹)⁻¹ v.1)
    rw [inv_inv]

theorem FF_subrepresentation [FiniteDimensional (ZMod 2) V]
    (U : Subrepresentation ρ) (hff : IsFFModule ρ) : IsFFModule U.toRepresentation := by
  obtain ⟨A,hA⟩ := hff
  exact ⟨A,hA.1,(fixedCodim_subrepresentation_le ρ U A).trans hA.2⟩

theorem doubledThree_dual_ratio (F : BinaryField) :
    quadraticRatio (repeated (linearNatural F 3) 2).dual =
      quadraticRatio (repeated (linearNatural F 3) 2) :=
  (((SourceCompletion.linearThreeGraphDualAction F).repeated 2).trans
    (repeatedDualEquiv (linearNatural F 3) 2)).quadraticRatio_eq.symm

theorem repeatedBinary_dual_ratio (d r : ℕ) :
    quadraticRatio (repeated (linearNatural BinaryField.two d) r).dual =
      quadraticRatio (repeated (linearNatural BinaryField.two d) r) :=
  (((actionSymm (dualNaturalEquiv d)).repeated r).trans
    (repeatedDualEquiv (linearNatural BinaryField.two d) r)).quadraticRatio_eq.symm

theorem naturalPlusDual_dual_ratio (d : ℕ) :
    quadraticRatio (naturalPlusDual d).dual = quadraticRatio (naturalPlusDual d) :=
  (naturalPairSelfDual (linearNatural BinaryField.two d)).quadraticRatio_eq.symm

theorem dual_bound_of_marked_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    (e : ActionEquiv ρ σ) (he : quadraticRatio σ.dual = quadraticRatio σ)
    (hff : IsFFModule ρ) : quadraticRatio ρ.dual ≤ 2 := by
  rw [e.dual.quadraticRatio_eq, he, ← e.quadraticRatio_eq]
  exact ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num)
end CFSG.Quasithin.ChapterB.QuasisimpleSource
