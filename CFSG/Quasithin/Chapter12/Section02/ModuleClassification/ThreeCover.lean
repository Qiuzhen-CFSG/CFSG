module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.Representation.SLThreeCentralExtension
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# Central extensions of the natural binary three-space

The moved space is commutator generated. Its projection onto the natural
three-space is therefore a module cover; the checked dual H1 calculation
bounds its fixed kernel by one dimension. It is either the natural module
or a four-dimensional extension.
Source: Aschbacher--Smith I.1.5 and 12.2.2, pp.408,795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} {K : Subgroup H}

@[expose] noncomputable def naturalProjection (s : MovedSection ρ K)
    (e : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3)) :
    Representation.IntertwiningMap
      ((s.space.toRepresentation.comp K.subtype).comp e.groupEquiv.symm.toMonoidHom)
      (specialLinearNatural (k := ZMod 2) 3) :=
  (e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g v
      have he := e.intertwines (e.groupEquiv.symm g) (Submodule.Quotient.mk v)
      exact he.trans (congrArg (fun a => linearNatural BinaryField.two 3 a
        (e.linearEquiv (Submodule.Quotient.mk v))) (e.groupEquiv.apply_symm_apply g)))

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
theorem naturalProjection_isCover (s : MovedSection ρ K)
    (hi : IsIrrPlus ρ K s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3)) :
    Representation.OneCohomology.IsCover (naturalProjection s e) := by
  refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
  · intro v hv g
    have hz : Submodule.Quotient.mk v = (0 : s.space.toSubmodule ⧸ s.central.toSubmodule) :=
      e.linearEquiv.injective (hv.trans (map_zero _).symm)
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hmem
    exact hmem (e.groupEquiv.symm g)
  · let τ := (s.space.toRepresentation.comp K.subtype).comp e.groupEquiv.symm.toMonoidHom
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      refine ⟨τ (e.groupEquiv ⟨g,hg⟩) ⟨v,hv⟩ - ⟨v,hv⟩,
        Coinvariants.sub_mem_ker _ _, ?_⟩
      change (s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv ⟨g,hg⟩)) ⟨v,hv⟩).val - v = _
      rw [e.groupEquiv.symm_apply_apply]
      rfl
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

omit [Finite H] in
/-- A central extension of the binary natural three-space has dimension
three or four; Irr+ already supplies indecomposability in the latter case. -/
theorem natural_three_isomorphism_or_dimension_four
    (s : MovedSection ρ K) (hi : IsIrrPlus ρ K s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3)) :
    Nonempty (ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (specialLinearNatural (k := ZMod 2) 3)) ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 4 := by
  let p := naturalProjection s e
  have hc := naturalProjection_isCover s hi e
  have hle := Representation.OneCohomology.finrank_ker_le_H1_of_cover p hc
  change Module.finrank (ZMod 2) p.toLinearMap.ker ≤
    Module.finrank (ZMod 2) (Representation.OneCohomology.H1
      (specialLinearNatural (k := ZMod 2) 3).dual) at hle
  rw [Representation.OneCohomology.SLThreeCentralExtension.finrank_H1_dual] at hle
  by_cases hz : p.toLinearMap.ker = ⊥
  · let f := LinearEquiv.ofBijective p.toLinearMap ⟨LinearMap.ker_eq_bot.mp hz,hc.1⟩
    let a : ActionEquiv (s.space.toRepresentation.comp K.subtype)
        (specialLinearNatural (k := ZMod 2) 3) :=
      ⟨e.groupEquiv,f,fun g v => by
        have he := LinearMap.congr_fun (p.isIntertwining' (e.groupEquiv g)) v
        change p.toLinearMap (s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv g)) v) = _ at he
        rw [e.groupEquiv.symm_apply_apply] at he
        exact he⟩
    exact Or.inl ⟨a⟩
  · have hpos : 0 < Module.finrank (ZMod 2) p.toLinearMap.ker := by
      have hn : Module.finrank (ZMod 2) p.toLinearMap.ker ≠ 0 :=
        fun h => hz (Submodule.finrank_eq_zero.mp h)
      omega
    have he := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hc.1,finrank_top] at he
    have hv : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := Module.finrank_fin_fun _
    rw [hv] at he
    exact Or.inr (by omega)

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification
