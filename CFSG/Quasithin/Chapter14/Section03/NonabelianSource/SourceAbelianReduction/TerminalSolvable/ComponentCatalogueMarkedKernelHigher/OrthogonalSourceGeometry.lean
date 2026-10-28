module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.OrthogonalSourceLinear

open Module Representation Subgroup Representation.BinaryOffender
open scoped MonoidAlgebra
open CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
public noncomputable section

/-!
# Stabilized orthogonal constituent at higher multiplicity

In a semisimple homogeneous binary normal restriction, an involution
stabilizing an isotropic simple constituent also stabilizes a disjoint
constituent in its orthogonal hyperplane whenever the ambient dimension is
more than twice the simple degree. Fixed intertwiners first bound the
hypothetical unique-fixed-constituent case to multiplicity three. A fixed
exterior image then forms a nondegenerate paired sum; its nonzero orthogonal
complement has simple degree and provides the second fixed constituent.

This is the projective multiplicity-space argument of G.11.9(1), expressed
directly in binary intertwining spaces so no projective-coordinate input is
required. Source: Aschbacher--Smith, printed p.369.
-/

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
section Geometry
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H : Subgroup D) [H.Normal]
  (R : Subrepresentation (ρ.comp H.subtype))
  [IsIrreducible R.toRepresentation]
  [IsSemisimpleModule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype))]
  (hh : ∀ J : Subrepresentation (ρ.comp H.subtype), IsIrreducible J.toRepresentation →
    Homogeneous.SameModule R J)
  (B : LinearMap.BilinForm (ZMod 2) W)
  (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
  (halt : B.IsAlt) (hnd : B.Nondegenerate)
  (hiso : ∀ u ∈ R.toSubmodule, ∀ w ∈ R.toSubmodule, B u w = 0)
  (x : D) (hx : x*x=1) (hxR : x ∈ subspaceStabilizer ρ R.toSubmodule)
  (hd : 2*finrank (ZMod 2) R.toSubmodule < finrank (ZMod 2) W)
include hh hpres halt hnd hiso hx hxR hd

theorem exists_stable_orthogonal_simple :
    ∃ J : Subrepresentation (ρ.comp H.subtype), IsIrreducible J.toRepresentation ∧
      Disjoint R.toSubmodule J.toSubmodule ∧
      J.toSubmodule ≤ B.orthogonal R.toSubmodule ∧
      x ∈ subspaceStabilizer ρ J.toSubmodule := by
  classical
  by_contra hn
  have hRat : IsAtom R := (Subrepresentation.irreducible_iff_isAtom R).mp inferInstance
  have hunique (K : Subrepresentation (ρ.comp H.subtype))
      (hi : IsIrreducible K.toRepresentation)
      (hp : K.toSubmodule ≤ B.orthogonal R.toSubmodule)
      (hxK : x ∈ subspaceStabilizer ρ K.toSubmodule) : K ≤ R := by
    by_contra hnot
    have hne : R ≠ K := fun he => hnot he.ge
    have hdis : Disjoint R.toSubmodule K.toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule
        (hRat.disjoint_of_ne ((Subrepresentation.irreducible_iff_isAtom K).mp hi) hne).eq_bot
    exact hn ⟨K,hi,hdis,hp,hxK⟩
  have hRH : H ≤ subspaceStabilizer ρ R.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun h hh w hw => R.apply_mem_toSubmodule ⟨h,hh⟩ hw
  have hUH := orthogonal_invariant ρ B hpres hRH
  let U : Subrepresentation (ρ.comp H.subtype) :=
    ⟨B.orthogonal R.toSubmodule, fun h w hw => (hUH h.property w).mpr hw⟩
  have hxU : x ∈ subspaceStabilizer ρ U.toSubmodule :=
    orthogonal_invariant ρ B hpres (zpowers_le.mpr hxR) (mem_zpowers x)
  have hisotypic := isotypic_of_sameModule (ρ.comp H.subtype) R hh
  have hUdim : finrank (ZMod 2) U.toSubmodule ≤ 2*finrank (ZMod 2) R.toSubmodule :=
    dimension_le_twice_of_fixedHom_range ρ H R U x hxR hxU hisotypic hx
      (fixedHom_range_of_unique_constituent ρ H R U x hxR hxU hx
        (fun K hi hKU hxK => hunique K hi hKU hxK))
  have hvdim : finrank (ZMod 2) W ≤ 3*finrank (ZMod 2) R.toSubmodule := by
    have he := B.finrank_orthogonal hnd R.toSubmodule
    have hr := R.toSubmodule.finrank_le
    change finrank (ZMod 2) (B.orthogonal R.toSubmodule) ≤ _ at hUdim
    omega
  let Vtop : Subrepresentation (ρ.comp H.subtype) := ⊤
  have hxV : x ∈ subspaceStabilizer ρ Vtop.toSubmodule := by intro w; exact ⟨fun _ => trivial,fun _ => trivial⟩
  obtain ⟨f,hf,w,hw⟩ : ∃ f : IntertwiningMap R.toRepresentation Vtop.toRepresentation,
      conjugateHom ρ H R Vtop x hxR hxV f = f ∧
      ∃ w, (f w).val ∉ B.orthogonal R.toSubmodule := by
    by_contra hno
    have hall : ∀ f : IntertwiningMap R.toRepresentation Vtop.toRepresentation,
        conjugateHom ρ H R Vtop x hxR hxV f = f → ∀ w, (f w).val ∈ R.toSubmodule := by
      intro f hf
      have hperp : ∀ w, (f w).val ∈ B.orthogonal R.toSubmodule := by
        intro w
        by_contra hw
        exact hno ⟨f,hf,w,hw⟩
      by_cases hz : f = 0
      · subst f; intro; exact R.toSubmodule.zero_mem
      · have hle := hunique (ambientRange ρ H R Vtop f)
          (ambientRange_irreducible ρ H R Vtop f hz)
          (by
            intro u hu
            obtain ⟨w,rfl⟩ := (mem_ambientRange_iff ρ H R Vtop f u).mp hu
            exact hperp w)
          (fixedHom_range_stable ρ H R Vtop x hxR hxV hx f hf)
        exact fun w => hle ((mem_ambientRange_iff ρ H R Vtop f (f w).val).mpr ⟨w,rfl⟩)
    have he := dimension_le_twice_of_fixedHom_range ρ H R Vtop x hxR hxV hisotypic hx hall
    have htop : finrank (ZMod 2) Vtop.toSubmodule = finrank (ZMod 2) W := by
      exact finrank_top (R := ZMod 2) (M := W)
    omega
  have hf0 : f ≠ 0 := by
    intro hz
    apply hw
    rw [hz]
    exact (B.orthogonal R.toSubmodule).zero_mem
  let J := ambientRange ρ H R Vtop f
  have hjirr : IsIrreducible J.toRepresentation := ambientRange_irreducible ρ H R Vtop f hf0
  have hxJ := fixedHom_range_stable ρ H R Vtop x hxR hxV hx f hf
  have hne : ∃ u ∈ R.toSubmodule, ∃ z ∈ J.toSubmodule, B u z ≠ 0 := by
    have hnz : ¬ ∀ u ∈ R.toSubmodule, B u (f w).val = 0 := hw
    push Not at hnz
    obtain ⟨u,hu,hnz⟩ := hnz
    exact ⟨u,hu,(f w).val,(mem_ambientRange_iff ρ H R Vtop f (f w).val).mpr ⟨w,rfl⟩,hnz⟩
  have hndsum := paired_sum_nondegenerate (ρ.comp H.subtype) B
    (fun h u z => hpres h u z) halt R J inferInstance hjirr hiso hne
  let S := R.toSubmodule ⊔ J.toSubmodule
  let K : Subrepresentation (ρ.comp H.subtype) :=
    ⟨B.orthogonal S, fun h w hw =>
      (orthogonal_invariant ρ B hpres (subspaceStabilizer_sup ρ hRH
        (by apply le_subspaceStabilizer; exact fun h hh w hw => J.apply_mem_toSubmodule ⟨h,hh⟩ hw))
        h.property w).mpr hw⟩
  have hc : IsCompl S K.toSubmodule := B.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl hndsum
  have hxK : x ∈ subspaceStabilizer ρ K.toSubmodule :=
    orthogonal_invariant ρ B hpres
      (subspaceStabilizer_sup ρ (zpowers_le.mpr hxR) (zpowers_le.mpr hxJ)) (mem_zpowers x)
  have hdJ : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) R.toSubmodule := by
    obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv R J).mp (hh J hjirr)
    exact e.toLinearEquiv.finrank_eq.symm
  have hdis : Disjoint R.toSubmodule J.toSubmodule := by
    rw [disjoint_iff]
    have hneq : R ≠ J := by
      intro he
      apply hw
      have hi : (f w).val ∈ R.toSubmodule :=
        (congrArg Subrepresentation.toSubmodule he).ge ((mem_ambientRange_iff ρ H R Vtop f (f w).val).mpr ⟨w,rfl⟩)
      exact fun u hu => hiso u hu (f w).val hi
    exact congrArg Subrepresentation.toSubmodule
      (hRat.disjoint_of_ne ((Subrepresentation.irreducible_iff_isAtom J).mp hjirr) hneq).eq_bot
  have hSdim : finrank (ZMod 2) S = 2*finrank (ZMod 2) R.toSubmodule := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq R.toSubmodule J.toSubmodule
    rw [hdis.eq_bot,finrank_bot,add_zero,hdJ] at he
    exact he.trans (by omega)
  have hKdim : finrank (ZMod 2) K.toSubmodule = finrank (ZMod 2) W -
      2*finrank (ZMod 2) R.toSubmodule := by
    exact (B.finrank_orthogonal hnd S).trans (congrArg (fun n => finrank (ZMod 2) W-n) hSdim)
  have hK0 : K ≠ ⊥ := by
    intro hz
    have he : finrank (ZMod 2) K.toSubmodule = 0 := by rw [hz]; exact finrank_bot (ZMod 2) W
    omega
  have hsmall : finrank (ZMod 2) K.toSubmodule ≤ finrank (ZMod 2) R.toSubmodule := by omega
  have hkirr := irreducible_of_small_dimension (ρ.comp H.subtype) K _
    (fun N hi => by
      obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv R N).mp (hh N hi)
      exact e.toLinearEquiv.finrank_eq.symm) hK0 hsmall
  have hKR := hunique K hkirr (B.orthogonal_le le_sup_left) hxK
  apply hK0
  apply Subrepresentation.toSubmodule_injective
  apply le_bot_iff.mp
  have hdisK : Disjoint R.toSubmodule K.toSubmodule := hc.disjoint.mono_left le_sup_left
  exact fun z hz => (Submodule.disjoint_def.mp hdisK) z (hKR hz) hz
end Geometry

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
end
