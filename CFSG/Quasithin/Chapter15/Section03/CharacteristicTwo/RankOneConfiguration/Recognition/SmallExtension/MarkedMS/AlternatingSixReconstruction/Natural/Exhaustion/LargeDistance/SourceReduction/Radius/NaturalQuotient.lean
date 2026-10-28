module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Irreducible
public import Theory.Representation.AlternatingSixInvolutionDegree
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryPermutation.SixPolar

/-!
# Recognizing the moving central quotient from its fixed index

The centralizer-modulo index is exactly the binary fixed-space index on
P/Z(P), with its literal conjugation action. An irreducible nontrivial
module for a two-group extension of A₆ descends to A₆. Three conjugate
involutions bound its degree by nine when the fixed codimension is at most
three. The proved binary catalogue then leaves the two natural four-modules.
The conclusion supplies actual equivariant coordinates on the six-letter
quotient module, retaining the possible exceptional automorphism of A₆.

The application to the original moving radius is in NaturalApplication.
Source: MS93 (3.8), printed pp.878--879; Aschbacher--Smith G.5.1--2.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
variable {H : Type*} [Group H] [Finite H]

/-- The fixed-space index is computed on the literal central quotient. -/
theorem central_quotient_fixed_index (P : Subgroup H) [P.Normal]
    [IsElementaryAbelian 2 (P ⧸ center P)]
    (α : H →* MulAut (P ⧸ center P))
    (hα : ∀ g (x : P), α g (QuotientGroup.mk' (center P) x) =
      QuotientGroup.mk' (center P) (MulAut.conjNormal g x))
    (A : Subgroup H) :
    2 ^ fixedCodim (Offenders.linearize α) A =
      (centralizerModulo P A (P ⊓ centralizer (P : Set H))).relIndex P := by
  let ρ := Offenders.linearize α
  let q := QuotientGroup.mk' (center P)
  let F : Subgroup (P ⧸ center P) := AddSubgroup.toSubgroup' (fixedSpace ρ A).toAddSubgroup
  have hf : F.index = 2 ^ fixedCodim ρ A := by
    have hi := fixed_subgroup_index (ρ.comp A.subtype)
    have hs : fixedSpace (ρ.comp A.subtype) ⊤ = fixedSpace ρ A := by
      rw [fixedSpace_comp_map, ←MonoidHom.range_eq_map, range_subtype]
    change (AddSubgroup.toSubgroup' (fixedSpace (ρ.comp A.subtype) ⊤).toAddSubgroup).index =
      2 ^ Module.finrank (ZMod 2) (Additive (P ⧸ center P) ⧸ fixedSpace (ρ.comp A.subtype) ⊤) at hi
    rw [hs] at hi
    exact hi
  have he : F.comap q = (centralizerModulo P A (P ⊓ centralizer (P : Set H))).subgroupOf P := by
    ext x
    change (∀ g : A, Additive.ofMul (α g (q x)) = Additive.ofMul (q x)) ↔ _
    rw [mem_subgroupOf, mem_centralizerModulo_iff]
    constructor
    · intro hx
      refine ⟨x.property,?_⟩
      intro g hg
      have hh : q (MulAut.conjNormal g x) = q x := by
        have hh := congrArg Additive.toMul (hx ⟨g,hg⟩)
        change α g (QuotientGroup.mk' (center P) x) = q x at hh
        rwa [hα] at hh
      have hc := QuotientGroup.eq_iff_div_mem.mp hh
      refine ⟨P.mul_mem (show (MulAut.conjNormal g x : H) ∈ P from (MulAut.conjNormal g x).property)
        (P.inv_mem x.property),?_⟩
      intro y hy
      have hh := congrArg Subtype.val (mem_center_iff.mp hc (⟨y,hy⟩ : P))
      change y * (g * x * g⁻¹ / x) = (g * x * g⁻¹ / x) * y at hh
      simpa only [commutatorElement_def, div_eq_mul_inv] using hh
    · rintro ⟨_,hx⟩ g
      apply congrArg Additive.ofMul
      rw [hα]
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      change (y : H) * ((g : H) * x * (g : H)⁻¹ / x) =
        ((g : H) * x * (g : H)⁻¹ / x) * y
      simpa only [commutatorElement_def, div_eq_mul_inv] using (hx g g.property).2 y y.property
  rw [←hf, ←F.index_comap_of_surjective (QuotientGroup.mk'_surjective (center P)), he]
  rfl

omit [Finite H] in
private theorem range_subtype_comp {K : Type*} [Group K] (B : Subgroup K)
    (f : H →* B) (hf : Function.Surjective f) : (B.subtype.comp f).range = B := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, ←MonoidHom.range_eq_map, range_subtype]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Small involution movement identifies an irreducible action with an
actual natural module, allowing the exceptional six-letter marking. -/
theorem natural_of_fixedCodim
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (hp : IsPGroup 2 q.ker) (ρ : Representation (ZMod 2) H W)
    [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q) (hi : fixedCodim ρ A ≤ 3) :
    ∃ π : H →* Equiv.Perm (Fin 6), π.range = alternatingGroup (Fin 6) ∧
      ∃ e : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
        ∀ g v, e (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 6) (π g) (e v) := by
  have hk : q.ker ≤ ρ.ker := normal_p_subgroup_le_ker ρ q.ker hp
  let eqv := QuotientGroup.quotientKerEquivOfSurjective q hq
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) W := (quotientOfLEKer ρ q.ker hk).comp eqv.symm.toMonoidHom
  have he (g : H) : σ (q g) = ρ g := by
    change quotientOfLEKer ρ q.ker hk (eqv.symm (q g)) = _
    rw [show eqv.symm (q g) = QuotientGroup.mk' q.ker g from eqv.symm_apply_eq.mpr rfl]
    rfl
  have hcomp : σ.comp q = ρ := MonoidHom.ext he
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq σ).mp
    (hcomp ▸ (inferInstance : IsIrreducible ρ))
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hne
    rw [←hcomp,hs]
    rfl
  have hfix : fixedSpace σ ⊤ = ⊥ := by
    by_contra hn
    have hk := σ.le_ker_of_normal_invariants_ne_bot ⊤ hn
    apply hnσ
    ext g v
    exact LinearMap.congr_fun (hk (mem_top g)) v
  have hbound : fixedCodim σ (zpowers a) ≤ 3 := by
    have hi' : fixedCodim σ (A.map q) ≤ 3 := by
      rw [←hcomp, fixedCodim, fixedSpace_comp_map] at hi
      exact hi
    have hh := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr haA))
    have ht := fixedCodim_add_finrank σ (zpowers a)
    have hA := fixedCodim_add_finrank σ (A.map q)
    omega
  obtain ⟨c,hc⟩ := AlternatingSix.InvolutionDisplacement.exists_three_conjugate_generators a ha
  have hd : Module.finrank (ZMod 2) W ≤ 9 := by
    have hh := finrank_le_mul_fixedCodim_of_conjugate_generation σ ⊤ hfix a c hc.ge
    omega
  rcases BinaryAlternatingSix.alternating_classify σ with ht | ht | ht | ht
  · obtain ⟨e⟩ := ht
    apply False.elim
    apply hnσ
    ext g v
    apply e.toLinearEquiv.injective
    exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  · obtain ⟨e⟩ := ht
    refine ⟨(alternatingGroup (Fin 6)).subtype.comp q,?_,
      e.toLinearEquiv.trans Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv,?_⟩
    · exact range_subtype_comp _ q hq
    · intro g v
      change Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv (e (ρ g v)) = _
      rw [←he]
      have hh := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (q g) v
      change e (σ (q g) v) = _ at hh
      rw [hh]
      exact Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv_action _ _
  · obtain ⟨e⟩ := ht
    let π := (alternatingGroup (Fin 6)).subtype.comp
      (BinaryAlternatingSix.alternatingDiagramAut.toMonoidHom.comp q)
    refine ⟨π,?_,e.toLinearEquiv.trans Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv,?_⟩
    · exact range_subtype_comp _ _ (BinaryAlternatingSix.alternatingDiagramAut.surjective.comp hq)
    · intro g v
      change Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv (e (ρ g v)) = _
      rw [←he]
      have hh := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (q g) v
      change e (σ (q g) v) = _ at hh
      rw [hh]
      exact Theory.SpecificGroups.SymmetricSix.PolarNatural.equiv_action _ _
  · obtain ⟨e⟩ := ht
    have hh := e.toLinearEquiv.finrank_eq.trans BinaryAlternatingSix.tensor_finrank
    omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
