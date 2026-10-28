module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.FlagGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.CyclicFlag
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed

/-!
# The original cyclic flag excludes split natural constituents

The tree Sylow fixes only one nonzero vector of the six-dimensional natural
module. A fixed vector in two copies therefore lies in one factor or in the
diagonal, and its orbit cannot generate both copies. In the augmentation
core the fixed vectors are constant, so a cyclic fixed generator cannot
surject onto that core either. These are obstructions to actual split
models, without an assertion that an arbitrary extension splits.

The source consumers obtain the fixed cyclic generator from the original
flag and its conjugate generation. Source: Aschbacher–Smith 14.7.2(1) and
14.7.51, printed pp.1043 and 1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation
open BinaryLinearThree.ParabolicCyclic
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Theory.SpecificGroups.SymmetricEight.CentralPair
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource

private theorem linearMap_zero_of_orbit_zero
    {H W X : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H W) (v : W)
    (hcyc : orbitSpan ρ ⊤ v = ⊤) (f : W →ₗ[ZMod 2] X)
    (hf : ∀ g : H, f (ρ g v) = 0) : f = 0 := by
  have hle : orbitSpan ρ ⊤ v ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,rfl⟩
    exact hf g
  rw [hcyc] at hle
  exact LinearMap.ext fun w => hle (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) W))

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- Two natural copies have no Sylow-fixed cyclic generator. -/
theorem not_double_natural_of_fixed_cyclic
    (ρ : Representation (ZMod 2) H W) (π : H →* Equiv.Perm (Fin 8))
    (P : Subgroup H) (hP : P.map π = treeGroup)
    (v : W) (hfix : ∀ g ∈ P, ρ g v = v) (hcyc : orbitSpan ρ ⊤ v = ⊤)
    (e : W ≃ₗ[ZMod 2] (natural (Fin 8) × natural (Fin 8)))
    (he : ∀ g w, e (ρ g w) =
      (naturalRepresentation (Fin 8) (π g) (e w).1,
       naturalRepresentation (Fin 8) (π g) (e w).2)) : False := by
  have hf (g : Equiv.Perm (Fin 8)) (hg : g ∈ treeGroup) :
      (naturalRepresentation (Fin 8) g (e v).1,
       naturalRepresentation (Fin 8) g (e v).2) = e v := by
    obtain ⟨a,ha,rfl⟩ := hP.symm ▸ hg
    exact (he a v).symm.trans (congrArg e (hfix a ha))
  by_cases hfirst : (e v).1 = 0
  · let f := (LinearMap.fst (ZMod 2) (natural (Fin 8)) (natural (Fin 8))).comp e.toLinearMap
    have hz : f = 0 := linearMap_zero_of_orbit_zero ρ v hcyc f (fun g => by
      change (e (ρ g v)).1 = 0
      rw [he,hfirst,map_zero])
    have hh := LinearMap.congr_fun hz (e.symm (standardPoint,0))
    exact standardPoint_ne_zero (by simpa [f] using hh)
  by_cases hsecond : (e v).2 = 0
  · let f := (LinearMap.snd (ZMod 2) (natural (Fin 8)) (natural (Fin 8))).comp e.toLinearMap
    have hz : f = 0 := linearMap_zero_of_orbit_zero ρ v hcyc f (fun g => by
      change (e (ρ g v)).2 = 0
      rw [he,hsecond,map_zero])
    have hh := LinearMap.congr_fun hz (e.symm (0,standardPoint))
    exact standardPoint_ne_zero (by simpa [f] using hh)
  have hsame : (e v).1 = (e v).2 :=
    (tree_fixed_eq_standardPoint _ hfirst (fun g hg => congrArg Prod.fst (hf g hg))).trans
      (tree_fixed_eq_standardPoint _ hsecond (fun g hg => congrArg Prod.snd (hf g hg))).symm
  let f := ((LinearMap.fst (ZMod 2) (natural (Fin 8)) (natural (Fin 8))) -
    (LinearMap.snd (ZMod 2) (natural (Fin 8)) (natural (Fin 8)))).comp e.toLinearMap
  have hz : f = 0 := linearMap_zero_of_orbit_zero ρ v hcyc f (fun g => by
    change (e (ρ g v)).1 - (e (ρ g v)).2 = 0
    rw [he,hsame,sub_self])
  have hh := LinearMap.congr_fun hz (e.symm (standardPoint,0))
  exact standardPoint_ne_zero (by simpa [f] using hh)

/-- A tree-fixed cyclic module cannot have the augmentation core as a quotient. -/
theorem not_core_quotient_of_fixed_cyclic
    (ρ : Representation (ZMod 2) H W) (π : H →* Equiv.Perm (Fin 8))
    (P : Subgroup H) (hP : P.map π = treeGroup)
    (v : W) (hfix : ∀ g ∈ P, ρ g v = v) (hcyc : orbitSpan ρ ⊤ v = ⊤)
    (f : W →ₗ[ZMod 2] core (Fin 8)) (hsurj : Function.Surjective f)
    (he : ∀ g w, f (ρ g w) = coreRepresentation (Fin 8) (π g) (f w)) : False := by
  have hf (g : Equiv.Perm (Fin 8)) (hg : g ∈ treeGroup) :
      coreRepresentation (Fin 8) g (f v) = f v := by
    obtain ⟨a,ha,rfl⟩ := hP.symm ▸ hg
    exact (he a v).symm.trans (congrArg f (hfix a ha))
  have hc : (f v).val ∈ constants (Fin 8) :=
    alternatingEight_core_sylow_fixed_constant evenTreeSylow (f v) (by
      intro a ha
      exact hf a.val (by rwa [evenTreeSylow_coe] at ha))
  have hv : coreToNatural (Fin 8) (f v) = 0 := by
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr hc
  let q := (coreToNatural (Fin 8)).comp f
  have hz : q = 0 := linearMap_zero_of_orbit_zero ρ v hcyc q (fun g => by
    change coreToNatural (Fin 8) (f (ρ g v)) = 0
    rw [he,coreToNatural_equivariant,hv,map_zero])
  obtain ⟨w,hw⟩ := coreToNatural_surjective.comp hsurj standardPoint
  exact standardPoint_ne_zero (hw.symm.trans (by
    exact LinearMap.congr_fun hz w))

/-- The natural module plus its augmentation core has no fixed cyclic generator. -/
theorem not_natural_core_of_fixed_cyclic
    (ρ : Representation (ZMod 2) H W) (π : H →* Equiv.Perm (Fin 8))
    (P : Subgroup H) (hP : P.map π = treeGroup)
    (v : W) (hfix : ∀ g ∈ P, ρ g v = v) (hcyc : orbitSpan ρ ⊤ v = ⊤)
    (e : W ≃ₗ[ZMod 2] (natural (Fin 8) × core (Fin 8)))
    (he : ∀ g w, e (ρ g w) =
      (naturalRepresentation (Fin 8) (π g) (e w).1,
       coreRepresentation (Fin 8) (π g) (e w).2)) : False := by
  let f := (LinearMap.snd (ZMod 2) (natural (Fin 8)) (core (Fin 8))).comp e.toLinearMap
  apply not_core_quotient_of_fixed_cyclic ρ π P hP v hfix hcyc f
  · intro w
    exact ⟨e.symm (0,w),by simp [f]⟩
  · intro g w
    exact congrArg Prod.snd (he g w)

open Chapter12.Section08 CriticalFusion.Source
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {I : Subgroup G} {σ : Representation (ZMod 2) I U}

/-- The original local section is not a direct sum of two marked natural modules. -/
theorem local_double_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 8))
    (hT : ((T : Subgroup G).subgroupOf I).map π = treeGroup)
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) σ)
    (e : U ≃ₗ[ZMod 2] (natural (Fin 8) × natural (Fin 8)))
    (he : ∀ g w, e (σ g w) =
      (naturalRepresentation (Fin 8) (π g) (e w).1,
       naturalRepresentation (Fin 8) (π g) (e w).2)) : False := by
  obtain ⟨x,_,_,hcyc,hfix⟩ := local_exists_sylow_fixed_cyclic_at h hI c
  exact not_double_natural_of_fixed_cyclic σ π _ hT x hfix hcyc e he

/-- The original local section cannot surject onto the marked augmentation core. -/
theorem local_core_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 8))
    (hT : ((T : Subgroup G).subgroupOf I).map π = treeGroup)
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) σ)
    (f : U →ₗ[ZMod 2] core (Fin 8)) (hsurj : Function.Surjective f)
    (he : ∀ g w, f (σ g w) = coreRepresentation (Fin 8) (π g) (f w)) : False := by
  obtain ⟨x,_,_,hcyc,hfix⟩ := local_exists_sylow_fixed_cyclic_at h hI c
  exact not_core_quotient_of_fixed_cyclic σ π _ hT x hfix hcyc f hsurj he

/-- The original local section is not the natural module plus its core. -/
theorem local_natural_core_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 8))
    (hT : ((T : Subgroup G).subgroupOf I).map π = treeGroup)
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) σ)
    (e : U ≃ₗ[ZMod 2] (natural (Fin 8) × core (Fin 8)))
    (he : ∀ g w, e (σ g w) =
      (naturalRepresentation (Fin 8) (π g) (e w).1,
       coreRepresentation (Fin 8) (π g) (e w).2)) : False := by
  obtain ⟨x,_,_,hcyc,hfix⟩ := local_exists_sylow_fixed_cyclic_at h hI c
  exact not_natural_core_of_fixed_cyclic σ π _ hT x hfix hcyc e he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
