module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicLinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicField

/-!
# Cubic containment on a faithful natural SL₃ constituent

A cubic first has trivial coefficient action by the fixed-field rank argument.
On the resulting linear kernel, a nontrivial cubic determinant forces three
independent diagonal cubics. Thus it has determinant one and belongs to the
original marked SL₃ subgroup. No field-four restriction or center quotient is
used. The companion action-image transport allows the original two-kernel.

Source: Aschbacher--Smith A.3.19, printed pp.54--55, applied in 11.0.4,
printed p.760. The invariant-constituent selection is a separate step.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Group H] [Finite H]
open Representation.SL3OddNaturalNormalizer

/-- Every cubic in a faithful natural overgroup of full SL₃ belongs to SL₃
when three divides the field-unit order and the ambient three-rank is at most two. -/
theorem cubic_mem_of_natural
    (L : Subgroup H) [L.Normal] (e : L ≃* SL(3,F))
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hf : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = (e g).val.mulVec v)
    (hd : 3 ∣ Nat.card F - 1) (hr : primeRank 3 H ≤ 2)
    (x : H) (hx : x ^ 3 = 1) : x ∈ L := by
  by_cases hxe : x = 1
  · exact hxe ▸ L.one_mem
  have hxo : orderOf x = 3 := orderOf_eq_prime hx hxe
  let hsemi := normalizer_semilinear L e ρ hnat
  let φ := fieldAction ρ hsemi
  have hxφ : φ x = 1 := by
    by_contra hn
    have hh := three_le_rank_of_cubic_field L e ρ hf hnat hd x hxo hn
    omega
  have hL : L ≤ φ.ker := by
    intro g hg
    apply (fieldAction_eq_one_iff ρ hsemi g).mpr
    intro c v
    change ρ (⟨g,hg⟩ : L) (c • v) = c • ρ (⟨g,hg⟩ : L) v
    rw [hnat,hnat,Matrix.mulVec_smul]
  let τ : Representation F φ.ker (Fin 3 → F) := {
    toFun g := {
      toFun := ρ (g : H)
      map_add' := (ρ (g : H)).map_add
      map_smul' := by
        intro c v
        exact (fieldAction_eq_one_iff ρ hsemi g).mp g.property c v }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρ.map_mul g h) v }
  let μ : φ.ker →* GL (Fin 3) F :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
  have hμ (g : φ.ker) (v : Fin 3 → F) : (μ g).val.mulVec v = ρ (g : H) v := by
    change (GeneralLinearGroup.toLin (μ g) : Module.End F (Fin 3 → F)) v = _
    have he : GeneralLinearGroup.toLin (μ g) = τ.asGroupHom g :=
      GeneralLinearGroup.toLin.apply_symm_apply _
    rw [he]
    rfl
  have hμinj : Function.Injective μ := by
    intro a b hab
    apply Subtype.ext
    apply hf
    apply LinearMap.ext
    intro v
    rw [← hμ a v,← hμ b v,hab]
  have hSL : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ μ.range := by
    intro A hA
    let a : SL(3,F) := ⟨A.val,congrArg Units.val hA⟩
    refine ⟨⟨e.symm a,hL (e.symm a).property⟩,?_⟩
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    exact (hμ _ v).trans (by rw [hnat,e.apply_symm_apply]; rfl)
  have hrμ : primeRank 3 μ.range ≤ 2 := by
    rw [← primeRank_equiv 3 (MonoidHom.ofInjective hμinj)]
    exact (Theory.GroupTheory.primeRank_le_of_injective 3 φ.ker.subtype φ.ker.subtype_injective).trans hr
  let y : φ.ker := ⟨x,hxφ⟩
  have hyd : GeneralLinearGroup.det (μ y) = 1 :=
    cubic_det_eq_one μ.range hSL hrμ ⟨μ y,⟨y,rfl⟩⟩ (by
      apply Subtype.ext
      change μ y ^ 3 = 1
      rw [← map_pow,show y ^ 3 = 1 from Subtype.ext hx,map_one])
  let a : SL(3,F) := ⟨(μ y).val,congrArg Units.val hyd⟩
  have he : x = (e.symm a : H) := by
    apply hf
    apply LinearMap.ext
    intro v
    rw [hnat,e.apply_symm_apply]
    exact (hμ y v).symm
  exact he ▸ (e.symm a).property

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
