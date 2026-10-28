module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.Representation.Quotient

/-!
# Marking the eight-dimensional component alternative

The component alternative is an actual four-space plus its dual. Three-cycles
act without nonzero fixed vectors on both constituents, hence on the whole
module. If the ambient action is irreducible, its seven-letter image cannot
be just A₇: surjectivity of the component inclusion would make the first
coordinate summand a proper nonzero ambient submodule. The image is therefore
S₇, and its marking transports the fixed-point calculation unchanged.

Source: Aschbacher–Smith, 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
universe u v
variable {H : Type u} [Group H] {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} {ι : A7 →* H}

private theorem dual_faithful
    (σ : Representation (ZMod 2) A7 Four) (hσ : Function.Injective σ) :
    Function.Injective σ.dual := by
  intro a b hab
  apply inv_injective
  apply hσ
  apply (Module.dualMap_dualMap_eq_iff (ZMod 2) Four).mp
  exact congrArg LinearMap.dualMap hab

/-- Every three-cycle acts without nonzero fixed vectors on the actual
four-plus-dual component restriction. -/
theorem fourPlusDual_component_threeCycle_fixedPointFree
    (hpair : IsFourPlusDual ρ ι) (a : A7) (ha : a.val.IsThreeCycle)
    (x : E) (hx : ρ (ι a) x = x) : x = 0 := by
  obtain ⟨σ,hσ,⟨e⟩⟩ := hpair
  have he := Representation.IntertwiningMap.isIntertwining (ρ.comp ι) (σ.prod σ.dual)
    e.symm.toIntertwiningMap a x
  change e.symm (ρ (ι a) x) = (σ.prod σ.dual) a (e.symm x) at he
  rw [hx] at he
  have hfirst : (e.symm x).1 = 0 :=
    binaryAlternatingSeven_threeCycle_fixedPointFree σ hσ
      (Module.finrank_fin_fun _) a ha _ (congrArg Prod.fst he.symm)
  have hsecond : (e.symm x).2 = 0 :=
    binaryAlternatingSeven_threeCycle_fixedPointFree σ.dual
      (dual_faithful σ hσ)
      (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_fin_fun _) a ha _
      (congrArg Prod.snd he.symm)
  apply e.symm.injective
  rw [map_zero]
  exact Prod.ext hfirst hsecond

/-- A four-plus-dual component cannot exhaust an irreducible ambient action. -/
theorem fourPlusDual_not_irreducible_of_surjective
    (hpair : IsFourPlusDual ρ ι) (hι : Function.Surjective ι)
    (hirr : IsIrreducible ρ) : False := by
  obtain ⟨σ,hσ,⟨e⟩⟩ := hpair
  let : IsIrreducible (ρ.comp ι) :=
    (irreducible_comp_surjective_iff ι hι ρ).mpr hirr
  let f : E →ₗ[ZMod 2] Module.Dual (ZMod 2) Four :=
    (LinearMap.snd _ _ _).comp e.symm.toLinearMap
  let N : Subrepresentation (ρ.comp ι) := {
    toSubmodule := f.ker
    apply_mem_toSubmodule a x hx := by
      change (e.symm ((ρ.comp ι) a x)).2 = 0
      have he : (e.symm ((ρ.comp ι) a x)).2 = σ.dual a ((e.symm x).2) :=
        congrArg Prod.snd (Representation.IntertwiningMap.isIntertwining
          (ρ.comp ι) (σ.prod σ.dual) e.symm.toIntertwiningMap a x)
      change (e.symm x).2 = 0 at hx
      exact he.trans (by rw [hx,map_zero]) }
  let u : Four := fun _ => 1
  have hu : u ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  let d : Module.Dual (ZMod 2) Four := LinearMap.proj 0
  have hd : d ≠ 0 := by
    intro h
    have hz := LinearMap.congr_fun h u
    exact one_ne_zero hz
  rcases eq_bot_or_eq_top N with hn | hn
  · have hv : e (u,0) ∈ N.toSubmodule := by
      change (e.symm (e (u,0))).2 = 0
      simp
    rw [hn] at hv
    have hv0 : e (u,0) = 0 := hv
    have hz := congrArg (fun x => (e.symm x).1) hv0
    exact hu (by simpa using hz)
  · have hv : e (0,d) ∈ N.toSubmodule := by
      rw [hn]
      trivial
    change (e.symm (e (0,d))).2 = 0 at hv
    exact hd (by simpa using hv)

/-- In the eight-dimensional alternative, the faithful seven-letter image
of an irreducible ambient group is the whole symmetric group. -/
theorem fourPlusDual_range_eq_top
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))
    (hpair : IsFourPlusDual ρ (componentInclusion φ hφ K hK))
    (hirr : IsIrreducible ρ)
    (hcases : φ.range = alternatingGroup (Fin 7) ∨ φ.range = ⊤) : φ.range = ⊤ := by
  rcases hcases with hrange | hrange
  · have hι : Function.Surjective (componentInclusion φ hφ K hK) := by
      intro x
      have hx : φ x ∈ alternatingGroup (Fin 7) := hrange ▸ ⟨x,rfl⟩
      refine ⟨⟨φ x,hx⟩,hφ ?_⟩
      exact componentInclusion_compatible φ hφ K hK ⟨φ x,hx⟩
    exact (fourPlusDual_not_irreducible_of_surjective hpair hι hirr).elim
  · exact hrange

/-- The same component calculation on the S₇ action obtained from a compatible
ambient marking. -/
theorem fourPlusDual_threeCycle_fixedPointFree
    (hpair : IsFourPlusDual ρ ι) (b : H ≃* Equiv.Perm (Fin 7))
    (hb : ∀ a : A7, b (ι a) = a.val)
    (t : Equiv.Perm (Fin 7)) (ht : t.IsThreeCycle)
    (x : E) (hx : (ρ.comp b.symm.toMonoidHom) t x = x) : x = 0 := by
  let a : A7 := ⟨t,ht.mem_alternatingGroup⟩
  have hi : ι a = b.symm t := b.injective ((hb a).trans (b.apply_symm_apply t).symm)
  apply fourPlusDual_component_threeCycle_fixedPointFree hpair a ht x
  rw [hi]
  exact hx

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
