module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Constituent
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Exchange
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Ratio
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.CentralCover
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.QuadraticFourGroup.TensorClassification.FactorIrreducible
/-!
# The original A₅ product module alternatives

An irreducible binary product module is isotypic on the first factor. The
single-factor classification gives either cubic-free copies or deleted copies;
in the latter case the scalar commutant produces a literal external tensor.
The actual factor exchange excludes the mixed case. Thus only the cubic-free
product and the sixteen-dimensional deleted square remain. Its full-normalizer
ratio bound then excludes the deleted case for a source central cover with an
offender of ratio at most two.

Source: Aschbacher–Smith D.3.7, printed pp.197–199. This is the branch where the
exchange preserves the irreducible product module; a moved constituent orbit
requires a separate argument.
-/
public section
open scoped TensorProduct MatrixGroups
open Representation Representation.QuadraticFourGroup.TensorClassification
open BinaryPermutation BinaryPermutation.FiveTensorSquare
namespace CFSG.Quasithin.Chapter10
noncomputable local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
/-- The two nontrivial simple binary A₅ types, with an exact deleted marking. -/
theorem source_a5_irreducible_cubicFree_or_deleted {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) Alt U) [σ.IsIrreducible] (hn : ∃ g, σ g ≠ 1) :
    CubicFixedPointFree σ ∨ Nonempty (σ.Equiv δ) := by
  obtain ⟨_,hnat | hdel⟩ :=
    ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
      σ (MulEquiv.refl _) hn
  · obtain ⟨f,⟨e⟩⟩ := hnat
    left
    apply CubicFixedPointFree.of_equiv (e := e.symm)
    intro g hg v hv
    exact Matrix.SL2.cubic_fixed_eq_zero (f g)
      ((orderOf_injective f.toMonoidHom f.injective g).trans hg) v hv
  · obtain ⟨f,⟨e⟩⟩ := hdel
    obtain ⟨s,hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective f
    let b := (coreEquiv s).trans (coreEquivNatural (Fin 5) (by decide))
    have hb : δ.Equiv
        (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp f.toMonoidHom) :=
      Representation.Equiv.mk b (by
        intro g
        apply LinearMap.ext
        intro v
        change coreEquivNatural (Fin 5) (by decide)
          (coreRepresentation (Fin 5) s (δ g v)) =
          naturalRepresentation (Fin 5) (f g).val
            (coreEquivNatural (Fin 5) (by decide) (coreRepresentation (Fin 5) s v))
        rw [←coreEquivNatural_equivariant,←hs]
        congr 1
        change coreRepresentation (Fin 5) s (coreRepresentation (Fin 5) g.val v) =
          coreRepresentation (Fin 5) (s*g.val*s⁻¹) (coreRepresentation (Fin 5) s v)
        simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one])
    exact Or.inr ⟨e.trans hb.symm⟩

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The source exchange leaves only a cubic-free product or the literal
sixteen-dimensional deleted tensor square. -/
theorem source_a5_product_module_alternatives
    (ρ : Representation (ZMod 2) (Alt × Alt) U) [ρ.IsIrreducible]
    (hleft : ∃ g, ρ (g,1) ≠ 1) (hright : ∃ g, ρ (1,g) ≠ 1)
    (E : U ≃ₗ[ZMod 2] U) (α β : MulAut Alt)
    (hE : ∀ g v, E (ρ g v) = ρ (α g.2,β g.1) (E v)) :
    CubicFreeOnFactors ρ ∨ Nonempty (ρ.Equiv deletedAction) := by
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
  let τ := ProductIsotypic.left ρ
  obtain ⟨S,hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional τ
  let σ := S.toRepresentation
  let := hS
  let inc : σ.IntertwiningMap τ := ⟨S.toSubmodule.subtype,fun _ => rfl⟩
  have hi : inc ≠ 0 := by
    let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg (fun f : σ.IntertwiningMap τ => f v) hz))
  obtain ⟨n,c,hc⟩ := ProductIsotypic.exists_copy_coordinates ρ σ inc hi
  have hσ : ∃ g, σ g ≠ 1 := by
    by_contra! hn
    obtain ⟨g,hg⟩ := hleft
    apply hg
    apply LinearMap.ext
    intro v
    apply c.injective
    simp only [hc,hn,Module.End.one_apply]
  rcases source_a5_irreducible_cubicFree_or_deleted σ hσ with hfree | hdeleted
  · left
    have hl : ∀ g, orderOf g = 3 → FixedPointFreeAt ρ (g,1) := by
      intro g hg v hv
      apply c.injective
      rw [map_zero]
      funext i
      have he := congrFun ((hc g v).symm.trans (congrArg c hv)) i
      exact hfree g hg (c v i) he
    refine ⟨hl,fun g hg v hv => ?_⟩
    apply E.injective
    rw [map_zero]
    apply hl (α g) ((orderOf_injective α.toMonoidHom α.injective g).trans hg)
    have he := hE (1,g) v
    simpa only [map_one,hv] using he.symm
  · obtain ⟨ed⟩ := hdeleted
    let := core_irreducible
    let := core_absolute
    let f := inc.comp ed.symm.toIntertwiningMap
    have hf : f ≠ 0 := by
      intro hz
      apply hi
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have he := congrArg (fun q : δ.IntertwiningMap τ => q (ed v)) hz
      change inc (ed.toLinearEquiv.symm (ed.toLinearEquiv v)) = 0 at he
      rw [ed.toLinearEquiv.symm_apply_apply] at he
      exact he
    obtain ⟨m,μ,⟨ep⟩⟩ := ProductIsotypic.exists_externalTensor ρ δ f hf
    let : (externalTensor δ μ).IsIrreducible :=
      (RepEquiv.ofRepresentationEquiv ep.symm).irreducible_of_euqiv inferInstance
    let : Nontrivial C := Subrepresentation.irreducible_module_nontrivial δ
    let : μ.IsIrreducible := irreducible_right_of_externalTensor δ μ
    have hep (g : Alt × Alt) (v : U) :
        ep.toLinearEquiv (ρ g v) = externalTensor δ μ g (ep.toLinearEquiv v) :=
      Representation.IntertwiningMap.isIntertwining ρ (externalTensor δ μ)
        ep.toIntertwiningMap g v
    have hμ : ∃ g, μ g ≠ 1 := by
      by_contra! hn
      obtain ⟨g,hg⟩ := hright
      apply hg
      apply LinearMap.ext
      intro v
      apply ep.toLinearEquiv.injective
      change ep.toLinearEquiv (ρ (1,g) v) = ep.toLinearEquiv v
      rw [hep]
      have hid : externalTensor δ μ (1,g) = 1 := by
        ext u w
        simp [externalTensor_apply,hn]
      rw [hid,Module.End.one_apply]
    rcases source_a5_irreducible_cubicFree_or_deleted μ hμ with hμfree | hμdel
    · exfalso
      let : Nontrivial (Fin m → ZMod 2) := Subrepresentation.irreducible_module_nontrivial μ
      let F := ep.toLinearEquiv.symm.trans (E.trans ep.toLinearEquiv)
      apply no_exchange_deleted_cubic_free μ hμfree F β
      intro g v
      obtain ⟨u,rfl⟩ := ep.toLinearEquiv.surjective v
      change ep.toLinearEquiv (E (ep.toLinearEquiv.symm
        (externalTensor δ μ (g,1) (ep.toLinearEquiv u)))) =
        externalTensor δ μ (1,β g) (ep.toLinearEquiv (E
          (ep.toLinearEquiv.symm (ep.toLinearEquiv u))))
      rw [←hep,ep.toLinearEquiv.symm_apply_apply,ep.toLinearEquiv.symm_apply_apply,hE]
      simpa only [map_one] using hep (1,β g) (E u)
    · obtain ⟨eμ⟩ := hμdel
      right
      exact ⟨ep.trans (externalTensorEquiv (Representation.Equiv.refl δ) eμ)⟩
open Representation.BinaryOffender

/-- The genuine cubic ratio bound on the faithful full actor removes the
deleted alternative, including a possible central kernel in the source module. -/
theorem source_a5_product_cubic_free_of_cover_ratio
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : Alt × Alt →* H) [i.range.Normal]
    (σ : Representation (ZMod 2) (Alt × Alt) U) [σ.IsIrreducible]
    (p : Representation.IntertwiningMap (ρ.comp i) σ) (hp : OneCohomology.IsCover p)
    (hleft : ∃ g, σ (g,1) ≠ 1) (hright : ∃ g, σ (1,g) ≠ 1)
    (E : U ≃ₗ[ZMod 2] U) (α β : MulAut Alt)
    (hE : ∀ g v, E (σ g v) = σ (α g.2,β g.1) (E v))
    (hbound : cubicRatio ρ ≤ 2) : CubicFreeOnFactors σ := by
  rcases source_a5_product_module_alternatives σ hleft hright E α β hE with hf | hd
  · exact hf
  obtain ⟨ed⟩ := hd
  let q := ed.toIntertwiningMap.comp p
  have hq : OneCohomology.IsCover q := by
    refine ⟨ed.toLinearEquiv.surjective.comp hp.1,?_,hp.2.2⟩
    intro v hv
    apply hp.2.1
    change ed.toLinearEquiv (p v) = 0 at hv
    exact ed.toLinearEquiv.injective (hv.trans ed.toLinearEquiv.map_zero.symm)
  let e := centralCoverEquiv q hq
  obtain ⟨A,hA,_,hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hbound
  exact False.elim ((Nat.not_lt_of_ge hsmall) (faithful_actor_ratio_gt_two ρ hρ i e hA))

end CFSG.Quasithin.Chapter10
