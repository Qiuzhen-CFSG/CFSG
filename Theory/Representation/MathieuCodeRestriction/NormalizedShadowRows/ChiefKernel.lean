module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.Representation.BinaryRadicalFlag.FlagKernel
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# The two-core detected by a common chief-action kernel

The kernel of the actions on every factor of an actual elementary-abelian
chief series has a two-group image on the whole module: its faithful image
lies in the unitriangular flag kernel. The whole action surjects onto each
literal chief action, whose faithful irreducible image has trivial two-core.
Thus a common kernel on the noncentral factors maps onto exactly the
whole-action two-core. Quotienting gives the original chief image, with the
original action homomorphisms retained.

This is the kernel transport used in Aschbacher--Smith, 3.1.9(6), printed
pp.577--578, for the original M22-code parabolic in 8.2.2(1), p.715.
It does not identify the original group kernel with its two-core.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
namespace MathieuCode.NormalizedShadowRows
variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [IsElementaryAbelian 2 U]

/-- A subgroup acting trivially on all actual chief factors has a two-group
image on the full elementary-abelian span. -/
theorem chief_kernel_image_isPGroup (s : SeriesOn U) (N : Subgroup H)
    (hN : ∀ i, N ≤ (s.factorRepresentation i).ker) :
    IsPGroup 2 (N.map (actionHom (normalRepresentation U))) := by
  let ρ := normalRepresentation U
  let σ := imageRepresentation ρ
  let W : Fin (s.series.length + 1) → Submodule (ZMod 2) (Additive U) :=
    fun i => (s.linearTerm i).toSubmodule
  by_cases ht : Nontrivial (Additive U)
  · let := ht
    have hNF : N.map (actionHom ρ) ≤ BinaryRadical.flagKernel σ W := by
      rintro _ ⟨g,hg,rfl⟩
      refine ⟨(BinaryRadical.mem_flagStabilizer σ W).mpr (fun i v => ?_),?_⟩
      · change ρ g v ∈ (s.linearTerm i).toSubmodule ↔ v ∈ (s.linearTerm i).toSubmodule
        constructor
        · intro hv
          have hh := (s.linearTerm i).apply_mem_toSubmodule g⁻¹ hv
          change ρ g⁻¹ (ρ g v) ∈ (s.linearTerm i).toSubmodule at hh
          simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
            Module.End.one_apply] using hh
        · intro hv
          exact (s.linearTerm i).apply_mem_toSubmodule g hv
      · intro i v hv
        apply (sectionRepresentation_trivial_iff ρ (s.linearTerm i.castSucc)
          (s.linearTerm i.succ) g).mp _ v hv
        intro w
        apply (s.factorLinearEquiv i).injective
        change s.factorLinearEquiv i (s.linearFactor i g w) = _
        rw [s.factorLinearEquiv_equivariant]
        exact LinearMap.congr_fun (hN i hg) _
    exact (BinaryRadical.flagKernel_isPGroup σ (imageRepresentation_injective ρ) W
      (by change (s.linearTerm 0).toSubmodule = ⊥; rw [s.linearTerm_zero]; rfl)
      (by change (s.linearTerm (Fin.last _)).toSubmodule = ⊤; rw [s.linearTerm_last]; rfl)).to_le hNF
  · let : Subsingleton (Additive U) := not_nontrivial_iff_subsingleton.mp ht
    have he : N.map (actionHom ρ) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro g _
      apply (actionHom_eq_one_iff ρ g).mpr
      intro v
      exact Subsingleton.elim _ _
    rw [he]
    exact IsPGroup.of_bot

/-- The original action on the span surjects onto each literal chief image. -/
theorem exists_chief_image_surjection (s : SeriesOn U) (i : Fin s.series.length) :
    ∃ f : actionImage (normalRepresentation U) →* actionImage (s.factorRepresentation i),
      Function.Surjective f ∧
      (∀ g, f (actionHom (normalRepresentation U) g) = actionHom (s.factorRepresentation i) g) ∧
      f.ker = (s.factorRepresentation i).ker.map (actionHom (normalRepresentation U)) := by
  let q := actionHom (normalRepresentation U)
  let r := actionHom (s.factorRepresentation i)
  have hq : Function.Surjective q := (normalRepresentation U).asGroupHom.rangeRestrict_surjective
  have hk : q.ker ≤ r.ker := by
    rw [actionHom_ker_eq, actionHom_ker_eq]
    intro g hg
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (s.factorLinearEquiv i).surjective w
    rw [← s.factorLinearEquiv_equivariant]
    have hfix : ∀ x, s.linearFactor i g x = x := by
      apply (sectionRepresentation_trivial_iff (normalRepresentation U)
        (s.linearTerm i.castSucc) (s.linearTerm i.succ) g).mpr
      intro x hx
      rw [show normalRepresentation U g x = x from LinearMap.congr_fun hg x,sub_self]
      exact Submodule.zero_mem _
    exact congrArg (s.factorLinearEquiv i) (hfix v)
  let f := q.liftOfSurjective hq ⟨r,hk⟩
  have he (g : H) : f (q g) = r g := q.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨f, ?_, he, ?_⟩
  · intro x
    obtain ⟨g,rfl⟩ := (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective x
    exact ⟨q g,he g⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨g,rfl⟩ := hq x
      have hg : g ∈ r.ker := (he g).symm.trans hx
      rw [actionHom_ker_eq] at hg
      exact mem_map_of_mem q hg
    · rintro ⟨g,hg,rfl⟩
      change f (q g) = 1
      rw [he]
      change g ∈ r.ker
      rw [actionHom_ker_eq]
      exact hg

/-- A common kernel on all noncentral chief factors has precisely the
whole-span two-core as its image. -/
theorem common_chief_kernel_image_eq_twoCore [Finite H]
    (s : SeriesOn U) (N : Subgroup H) [N.Normal]
    (hN : ∀ i, ¬ s.Central i → (s.factorRepresentation i).ker = N)
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    N.map (actionHom (normalRepresentation U)) = pCore 2 (actionImage (normalRepresentation U)) := by
  let q := actionHom (normalRepresentation U)
  have hq : Function.Surjective q := (normalRepresentation U).asGroupHom.rangeRestrict_surjective
  let : (N.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hp : IsPGroup 2 (N.map q) := chief_kernel_image_isPGroup U s N (fun j => by
    by_cases hj : s.Central j
    · intro g hg
      apply LinearMap.ext
      intro w
      exact congrArg Additive.ofMul ((s.central_iff_action j).mp hj g w.toMul)
    · rw [hN j hj])
  have hl : N.map q ≤ pCore 2 (actionImage (normalRepresentation U)) :=
    le_sSup ⟨inferInstance,hp⟩
  apply le_antisymm hl
  obtain ⟨f,hf,he,hk⟩ := exists_chief_image_surjection U s i
  have hnormal : ((pCore 2 (actionImage (normalRepresentation U))).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hm : (pCore 2 (actionImage (normalRepresentation U))).map f ≤
      pCore 2 (actionImage (s.factorRepresentation i)) :=
    le_sSup ⟨hnormal,pCore_isPGroup.map f⟩
  let := s.factorRepresentation_irreducible i
  rw [irreducible_image_twoCore_eq_bot (s.factorRepresentation i)] at hm
  have hle := (map_le_iff_le_comap).mp hm
  rw [MonoidHom.comap_bot, hk, hN i hi] at hle
  exact hle


/-- After removal of the actual whole-span two-core, the original action
becomes the same faithful chief actor. -/
theorem exists_span_twoCore_quotient_equiv [Finite H]
    (s : SeriesOn U) (N : Subgroup H) [N.Normal]
    (hN : ∀ i, ¬ s.Central i → (s.factorRepresentation i).ker = N)
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    ∃ e : (actionImage (normalRepresentation U) ⧸
        pCore 2 (actionImage (normalRepresentation U))) ≃* actionImage (s.factorRepresentation i),
      ∀ g, e (QuotientGroup.mk' (pCore 2 (actionImage (normalRepresentation U)))
        (actionHom (normalRepresentation U) g)) = actionHom (s.factorRepresentation i) g := by
  obtain ⟨f,hf,he,hk⟩ := exists_chief_image_surjection U s i
  have hk' : f.ker = pCore 2 (actionImage (normalRepresentation U)) := by
    rw [hk,hN i hi]
    exact common_chief_kernel_image_eq_twoCore U s N hN i hi
  let e := (QuotientGroup.quotientMulEquivOfEq hk'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨e,?_⟩
  intro g
  change QuotientGroup.quotientKerEquivOfSurjective f hf
    (QuotientGroup.mk' f.ker (actionHom (normalRepresentation U) g)) = _
  simpa [QuotientGroup.quotientKerEquivOfSurjective, QuotientGroup.kerLift_mk] using he g

end MathieuCode.NormalizedShadowRows

namespace MathieuCode.NormalizedShadowRows
open Subgroup Representation Representation.BinaryOffender
variable {H W W' : Type*} [Group H]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W']

/-- A reduction of the whole action by its actual two-core, retaining the
original homomorphisms. The kernel equality concerns its image only. -/
structure ActionImageReduction
    (ρ : Representation (ZMod 2) H W) (σ : Representation (ZMod 2) H W') where
  kernel_image : σ.ker.map (actionHom ρ) = pCore 2 (actionImage ρ)
  equiv : (actionImage ρ ⧸ pCore 2 (actionImage ρ)) ≃* actionImage σ
  map_action : ∀ x, equiv (QuotientGroup.mk' (pCore 2 (actionImage ρ)) (actionHom ρ x)) =
    actionHom σ x

/-- The reduction carries every original subgroup to its original image. -/
theorem ActionImageReduction.map_subgroup
    {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) H W'}
    (d : ActionImageReduction ρ σ) (B : Subgroup H) :
    (B.map ((QuotientGroup.mk' (pCore 2 (actionImage ρ))).comp
      (actionHom ρ))).map d.equiv.toMonoidHom = B.map (actionHom σ) := by
  rw [map_map]
  congr 1
  exact MonoidHom.ext d.map_action

end MathieuCode.NormalizedShadowRows
