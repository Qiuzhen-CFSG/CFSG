module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixC28
public import Theory.Representation.IrreduciblePairBound
public import Theory.Representation.IrreducibleFixedPoints

/-!
# The actual A₆ residual on the whole graph pair

The reciprocal cover L=LH O₂(L) preserves surjectivity of the original
graph-pair actor on LH: O₂(L) centralizes the whole orbit, and the actual
derived pair is faithful. Thus the original intersection residual retains
both irreducible, inequivalent four-dimensional summands. It has no fixed
point on the eight-space, and that space cannot embed in repetitions of a
module of dimension less than eight.

Source: Aschbacher--Smith C.4.8 and 7.3.4, printed pp.154,699, with the
graph-pair commutant of H.7, pp.388--389, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem six_derived_irreducible :
    IsIrreducible (symplecticDerivedNatural (k := ZMod 2) 2) :=
  ExtensionConsequences.irreducible_of_equiv
    ExtensionConsequences.SymplecticTwo.derivedNaturalActionEquiv
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))

private theorem six_pair_fixed_zero (v : Space (ZMod 2))
    (hv : ∀ g : commutator (Sp (ZMod 2)), derivedPair graphAut g v = v) : v = 0 := by
  let : IsIrreducible (symplecticDerivedNatural (k := ZMod 2) 2) := six_derived_irreducible
  have hz := OneCohomology.fixed_eq_bot_of_irreducible_finrank
    (symplecticDerivedNatural (k := ZMod 2) 2) (by simp)
  have h₁ : v.1 ∈ OneCohomology.fixed (symplecticDerivedNatural (k := ZMod 2) 2) :=
    fun g => congrArg Prod.fst (hv g)
  let a := MulAut.characteristic (commutator (Sp (ZMod 2))) graphAut
  have h₂ : v.2 ∈ OneCohomology.fixed (symplecticDerivedNatural (k := ZMod 2) 2) := by
    intro g
    have hh := congrArg Prod.snd (hv (a.symm g))
    change symplecticDerivedNatural 2 (a (a.symm g)) v.2 = v.2 at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  rw [hz, Submodule.mem_bot] at h₁ h₂
  exact Prod.ext h₁ h₂

/-- The original residual still surjects onto the actual derived graph-pair
actor, with coordinates for its literal action on the complete source orbit. -/
theorem sourceOrbit_six_witness_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ q : LH →* commutator (Sp (ZMod 2)), Function.Surjective q ∧
      ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2] Space (ZMod 2),
        ∀ l v, e (doubledSeedAction LH D.sourceOrbit
          (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes) l v) =
          derivedPair graphAut (q l) (e v) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨_,_,_,q,hq,e,he,_⟩ := D.sourceOrbit_six_pair_coordinates h hd hmodel
  have hQC : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) :=
    ((componentCore_le_sectionCentralizer L.le_normalizer).trans inf_le_right).trans
      (D.sourceOrbit_six_sectionCentralizer_centralizes h hd hmodel)
  have hk (b : G) (hb : b ∈ L.pCoreIn 2) : q ⟨b,pCoreIn_le 2 L hb⟩ = 1 := by
    apply Subtype.ext
    apply binaryPair_injective graphAut
    change derivedPair graphAut (q ⟨b,pCoreIn_le 2 L hb⟩) = derivedPair graphAut 1
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := e.surjective v
    rw [←he,map_one,Module.End.one_apply]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hQC hb w.toMul w.toMul.property).symm
  let p := q.comp (inclusion hLH)
  have hp : Function.Surjective p := by
    intro g
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨a,ha,b,hb,hab⟩ := hw.2.2.2.2.2.2.2.1.subset l.property
    refine ⟨⟨a,ha⟩,?_⟩
    have hh : (⟨a,hLH ha⟩ : L) * ⟨b,pCoreIn_le 2 L hb⟩ = l := Subtype.ext hab
    change q ⟨a,hLH ha⟩ = q l
    rw [←hh,map_mul,hk b hb,mul_one]
  exact ⟨p,hp,e,fun l v => he (inclusion hLH l) v⟩

/-- The literal intersection residual has no fixed point on the original
eight-dimensional doubled orbit. -/
theorem sourceOrbit_six_witness_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    D.sourceOrbit ⊓ centralizer (LH : Set G) = ⊥ := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  obtain ⟨q,hq,e,he⟩ := D.sourceOrbit_six_witness_pair_coordinates h hd hmodel hw
  apply bot_unique
  intro x hx
  let v : Additive D.sourceOrbit := Additive.ofMul ⟨x,hx.1⟩
  have hv : e v = 0 := six_pair_fixed_zero (e v) (by
    intro g
    obtain ⟨l,rfl⟩ := hq g
    rw [←he]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 l l.property))
  exact congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G)) (e.map_eq_zero_iff.mp hv)

private theorem no_small_graph_pair
    {F Y ι : Type*} [Group F] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y]
    (p : F →* commutator (Sp (ZMod 2))) (hp : Function.Surjective p)
    (σ : Representation (ZMod 2) F Y)
    (τ : Representation (ZMod 2) F (ι → Y))
    (hτ : ∀ x v i, τ x v i = σ x (v i))
    (hd : Module.finrank (ZMod 2) Y < 8)
    (f : Space (ZMod 2) →ₗ[ZMod 2] (ι → Y)) (hf : Function.Injective f)
    (he : ∀ x v, f (derivedPair graphAut (p x) v) = τ x (f v)) : False := by
  let a := MulAut.characteristic (commutator (Sp (ZMod 2))) graphAut
  let ρ : Representation (ZMod 2) F (Theory.SpecificGroups.SymplecticFour.Vector (ZMod 2)) :=
    (symplecticDerivedNatural (k := ZMod 2) 2).comp p
  let η : Representation (ZMod 2) F (Theory.SpecificGroups.SymplecticFour.Vector (ZMod 2)) :=
    (symplecticDerivedNatural (k := ZMod 2) 2).comp (a.toMonoidHom.comp p)
  let : IsIrreducible (symplecticDerivedNatural (k := ZMod 2) 2) := six_derived_irreducible
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff p hp _).mpr inferInstance
  let : IsIrreducible η := (irreducible_comp_surjective_iff _ (a.surjective.comp hp) _).mpr inferInstance
  have hz (b : η.IntertwiningMap ρ) : b = 0 := by
    have hh := Ambient.Normalizer.Commutant.graph_natural_intertwiner_zero
      b.toLinearMap.toAddMonoidHom (by
        intro g v
        obtain ⟨x,rfl⟩ := hp g
        exact LinearMap.congr_fun (b.isIntertwining' x) v)
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact DFunLike.congr_fun hh v
  let j : (ρ.prod η).IntertwiningMap τ := {
    toLinearMap := f
    isIntertwining' := by
      intro x
      apply LinearMap.ext
      intro v
      exact he x v }
  apply no_small_repeated_inequivalent_pair hz (σ := σ) _ τ hτ j hf
  simpa [Theory.SpecificGroups.SymplecticFour.Vector] using hd

/-- The same original residual action cannot embed in any number of copies
of a module of dimension less than eight. -/
theorem sourceOrbit_six_witness_no_small_repeated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    {Y ι : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y] :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∀ (σ : Representation (ZMod 2) LH Y) (τ : Representation (ZMod 2) LH (ι → Y)),
      (∀ x v i, τ x v i = σ x (v i)) → Module.finrank (ZMod 2) Y < 8 →
      ∀ f : Additive D.sourceOrbit →ₗ[ZMod 2] (ι → Y), Function.Injective f →
        (∀ l v, f (doubledSeedAction LH D.sourceOrbit
          (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes) l v) =
          τ l (f v)) → False := by
  intro LH σ τ hτ hdim f hf he
  obtain ⟨p,hp,e,hepair⟩ := D.sourceOrbit_six_witness_pair_coordinates h hd hmodel hw
  apply no_small_graph_pair p hp σ τ hτ hdim (f.comp e.symm.toLinearMap)
    (hf.comp e.symm.injective)
  intro l v
  change f (e.symm (derivedPair graphAut (p l) v)) = τ l (f (e.symm v))
  have hh := hepair l (e.symm v)
  rw [e.apply_symm_apply] at hh
  rw [←hh,e.symm_apply_apply]
  exact he l (e.symm v)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
