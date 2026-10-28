module
public import CFSG.Quasithin.ChapterG.Section11.WholeAlternating
public import CFSG.Quasithin.ChapterG.Section11.NontrivialActorCatalogue

/-!
# Excluding a whole A7 component with nontrivial smaller actor

The actual binary degree catalogue recognizes the six-dimensional core.
Its faithful ambient extension and the original G.10 identities then give
the seven-point transvection contradiction with the same relative quotient.
This connects whole-component recognition to the original HS smaller actor,
without a strict-intersection or type-a2 assumption.
Source: Aschbacher--Smith G.9.3, G.11.2(4), 14.3.24, pp.354,364,1000.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open BinaryPermutation SevenParabolic Representation.BinaryOffender
private theorem binary_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))


/-- The actual whole A7 action is excluded when its original smaller actor is nontrivial. -/
theorem not_seven_of_smaller_ne_bot
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X Z L : Subgroup G}
    [IsElementaryAbelian 2 X] {C : GroupClass}
    (h : Section10.Hypothesis ρ B v W X (Z.subgroupOf X))
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V) (hZX : Z ≤ X) (hZ : Z ≠ ⊥)
    (eK : L ≃* alternatingGroup (Fin 7)) : False := by
  let := h9.normal_H
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr eK)] at hu
  have hb := Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  let σ := (ρ.comp L.subtype).comp eK.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eK.symm.toMonoidHom eK.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp eK.symm.injective)
  have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ hf inferInstance (by omega)
  have hdim : finrank (ZMod 2) V = 6 := by rcases hs with hs | hs | hs <;> omega
  obtain ⟨f⟩ := ChapterK.Alternating.SevenSixSpace.of_point_fixed_or_dual σ hdim
    (ChapterK.Alternating.SevenSixSpace.fixed_or_dual
      ChapterK.Alternating.SevenSixSpace.pointSimpleDegrees _ hdim)
  let c := coreEquivNatural (Fin 7) (by decide)
  let eV := f.toLinearEquiv.trans c.symm
  have he (l : L) (u : V) : eV (ρ l u) =
      alternatingCoreRepresentation (Fin 7) (eK l) (eV u) := by
    apply c.injective
    change c (c.symm (f (ρ l u))) =
      c (alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u)))
    rw [c.apply_symm_apply]
    have hh := coreEquivNatural_equivariant (Fin 7) (by decide) (eK l).val (c.symm (f u))
    change c (alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u))) =
      alternatingNaturalRepresentation (Fin 7) (eK l) (c (c.symm (f u))) at hh
    rw [hh,c.apply_symm_apply]
    have hh := IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (eK l) u
    change f (ρ (eK.symm (eK l)) u) = alternatingNaturalRepresentation (Fin 7) (eK l) (f u) at hh
    rwa [eK.symm_apply_apply] at hh
  obtain ⟨f,hf,hfK,hact⟩ := faithful_extension L ρ h.faithful eK eV he
  have hAlt : alternatingGroup (Fin 7) ≤ f.range := by
    intro a ha
    obtain ⟨k,hk⟩ := eK.surjective ⟨a,ha⟩
    exact ⟨k,by rw [hfK,hk]⟩
  have hform (u w : V) : B u w = pairing (eV u) (eV w) :=
    marked_form_eq L ρ eK eV he B h.nondegenerate (fun k => h.preserves k) u w
  have hv : eV v ≠ 0 := fun hh => h.point_ne_zero (eV.injective (hh.trans eV.map_zero.symm))
  have hmapFix : (fixedSpace ρ X).map eV.toLinearMap = fixedSpace (action.comp f) X := by
    ext w
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [Submodule.mem_map_equiv,eV.symm_apply_apply]
    constructor
    · intro hu x
      change action (f x) (eV u) = eV u
      rw [← hact]
      exact congrArg eV (hu x)
    · intro hu x
      apply eV.injective
      change eV (ρ (x:G) u) = eV u
      rw [hact]
      exact hu x
  have hfixed : W.map eV.toLinearMap ⊓ fixedSpace (action.comp f) X =
      Submodule.span (ZMod 2) {eV v} := by
    have hh := congrArg (fun P : Submodule (ZMod 2) V => P.map eV.toLinearMap) h.fixedSpace_in_W
    rwa [Submodule.map_inf _ eV.injective,hmapFix,Submodule.map_span,Set.image_singleton] at hh
  apply exclude f hf hAlt X X Z le_rfl hZX (W.map eV.toLinearMap) (eV v) hv
  · intro x hx
    rw [← hact]
    exact congrArg eV (h.fixes_point hx)
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨w,hw,rfl⟩
    exact (hform u w).symm.trans (h.isotropic u hu w hw)
  · rintro x hx _ ⟨u,hu,rfl⟩
    change action (f x) (eV u) - eV u ∈ Submodule.span (ZMod 2) {eV v}
    obtain ⟨l,_,hl⟩ := h.transvections ⟨x,hx⟩
    rw [← hact,hl ⟨u,hu⟩,map_add,map_smul,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact hfixed
  · intro x hx w hw
    obtain ⟨u,rfl⟩ := eV.surjective w
    rw [← hact,← map_sub]
    exact Submodule.mem_map_of_mem (h.displacement ⟨x,hx⟩ u ((hform v u).trans hw))
  · rw [eV.finrank_map_eq]
    have hh := h.dimension
    rwa [binary_rank,hdim] at hh
  · exact fun _ => hZ

end CFSG.Quasithin.ChapterG.Section11.LargeWhole
