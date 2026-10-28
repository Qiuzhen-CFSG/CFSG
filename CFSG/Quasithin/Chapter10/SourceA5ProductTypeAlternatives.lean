module
public import CFSG.Quasithin.Chapter10.SourceA5ProductAlternatives
/-!
# Binary A₅ product alternatives without constituent exchange

Restriction to the first simple factor is isotypic. A cubic-free constituent
makes that entire factor cubic-free; a deleted constituent is absolutely
irreducible and supplies an actual external tensor over the binary field.
Repeating with the factors reversed gives the natural/natural, deleted/natural,
natural/deleted and deleted/deleted alternatives, with literal intertwiners.

Unlike the same-constituent D.3.7 branch, no exchanging operator is assumed.
The mixed alternatives are needed in the moved homogeneous orbit of D.3.5.
The natural/natural branch is characterized by cubic freeness, so the proved
natural-tensor descent applies without an additional classification premise.

Source: Aschbacher–Smith D.3.5–7, printed pp.195–199.
-/
public section
open scoped TensorProduct MatrixGroups
open Representation Representation.QuadraticFourGroup.TensorClassification
open BinaryPermutation BinaryPermutation.FiveTensorSquare
namespace CFSG.Quasithin.Chapter10
noncomputable local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
/-- The two nontrivial simple binary A₅ types, with an exact deleted marking. -/
theorem source_a5_irreducible_natural_or_deleted {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) Alt U) [σ.IsIrreducible] (hn : ∃ g, σ g ≠ 1) :
    (∃ f : Alt ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (σ.Equiv (SL2.BinarySmall.natural.comp f.toMonoidHom))) ∨
    Nonempty (σ.Equiv δ) := by
  obtain ⟨_,hnat | hdel⟩ :=
    ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
      σ (MulEquiv.refl _) hn
  · exact Or.inl hnat
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

/-- Isotypy supplies a deleted tensor when the first factor is not cubic-free. -/
theorem source_a5_product_left_alternatives
    (ρ : Representation (ZMod 2) (Alt × Alt) U) [ρ.IsIrreducible]
    (hleft : ∃ g, ρ (g,1) ≠ 1) (hright : ∃ g, ρ (1,g) ≠ 1) :
    (∀ g, orderOf g = 3 → FixedPointFreeAt ρ (g,1)) ∨
    ∃ (m : ℕ) (μ : Representation (ZMod 2) Alt (Fin m → ZMod 2)),
      μ.IsIrreducible ∧ (∃ g, μ g ≠ 1) ∧
      Nonempty (ρ.Equiv (externalTensor δ μ)) := by
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
    intro g hg v hv
    apply c.injective
    rw [map_zero]
    funext i
    have he := congrFun ((hc g v).symm.trans (congrArg c hv)) i
    exact hfree g hg (c v i) he
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
    exact Or.inr ⟨m,μ,inferInstance,hμ,⟨ep⟩⟩

private def productSwap : MulAut (Alt × Alt) := MulEquiv.prodComm

private noncomputable def externalTensorSwap
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (μ : Representation (ZMod 2) Alt W) :
    Representation.Equiv ((externalTensor δ μ).comp productSwap.toMonoidHom)
      (externalTensor μ δ) :=
  Representation.Equiv.mk (TensorProduct.comm _ _ _) (by
    intro g
    ext u v
    rfl)

/-- The irreducible product alternatives without any seed-preserving exchange.
The two mixed orientations remain, as required for a moved homogeneous seed. -/
theorem source_a5_product_module_alternatives_without_exchange
    (ρ : Representation (ZMod 2) (Alt × Alt) U) [ρ.IsIrreducible]
    (hleft : ∃ g, ρ (g,1) ≠ 1) (hright : ∃ g, ρ (1,g) ≠ 1) :
    CubicFreeOnFactors ρ ∨
    (∃ f : Alt ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (ρ.Equiv (externalTensor δ (SL2.BinarySmall.natural.comp f.toMonoidHom)))) ∨
    (∃ f : Alt ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (ρ.Equiv (externalTensor (SL2.BinarySmall.natural.comp f.toMonoidHom) δ))) ∨
    Nonempty (ρ.Equiv deletedAction) := by
  rcases source_a5_product_left_alternatives ρ hleft hright with hfree | hdel
  · let σ : Representation (ZMod 2) (Alt × Alt) U := ρ.comp productSwap.toMonoidHom
    let : σ.IsIrreducible :=
      (irreducible_comp_surjective_iff productSwap.toMonoidHom productSwap.surjective ρ).mpr
        inferInstance
    have hσl : ∃ g, σ (g,1) ≠ 1 := hright
    have hσr : ∃ g, σ (1,g) ≠ 1 := hleft
    rcases source_a5_product_left_alternatives σ hσl hσr with hfree' | hdel'
    · exact Or.inl ⟨hfree,hfree'⟩
    · obtain ⟨m,μ,hμ,hn,⟨e⟩⟩ := hdel'
      let := hμ
      let e' : ρ.Equiv ((externalTensor δ μ).comp productSwap.toMonoidHom) :=
        Representation.Equiv.mk e.toLinearEquiv (by
          intro g
          apply LinearMap.ext
          intro v
          exact Representation.IntertwiningMap.isIntertwining σ _ e.toIntertwiningMap
            (productSwap g) v)
      let es := e'.trans (externalTensorSwap μ)
      rcases source_a5_irreducible_natural_or_deleted μ hn with hnat | hdel
      · obtain ⟨f,⟨b⟩⟩ := hnat
        exact Or.inr (Or.inr (Or.inl ⟨f,⟨es.trans
          (externalTensorEquiv b (Representation.Equiv.refl δ))⟩⟩))
      · obtain ⟨b⟩ := hdel
        exact Or.inr (Or.inr (Or.inr ⟨es.trans
          (externalTensorEquiv b (Representation.Equiv.refl δ))⟩))
  · obtain ⟨m,μ,hμ,hn,⟨e⟩⟩ := hdel
    let := hμ
    rcases source_a5_irreducible_natural_or_deleted μ hn with hnat | hdel
    · obtain ⟨f,⟨b⟩⟩ := hnat
      exact Or.inr (Or.inl ⟨f,⟨e.trans
        (externalTensorEquiv (Representation.Equiv.refl δ) b)⟩⟩)
    · obtain ⟨b⟩ := hdel
      exact Or.inr (Or.inr (Or.inr ⟨e.trans
        (externalTensorEquiv (Representation.Equiv.refl δ) b)⟩))
end CFSG.Quasithin.Chapter10
