module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic

/-!
# The original flag point generates the whole local section

The point residual is transitive on the three nonzero vectors of the seed
plane. Thus any nonzero flag-point coordinate generates that seed, and its
whole local orbit generates U_I/V₁. The original Sylow fixes this generator.
This keeps the original cyclic-generation constraint when analyzing two
natural constituents; the offender inequalities alone do not retain it.

Source: Aschbacher–Smith 14.7.2(1), and U_I = ⟨V^I⟩, printed p.1043.
-/
public noncomputable section
open Subgroup Representation BinaryLinearThree.ParabolicCyclic
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source AlternatingSevenSource
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {I : Subgroup G} {ρ : Representation (ZMod 2) I W}

/-- Every nonzero original seed coordinate is cyclic for the whole local. -/
theorem local_nonzero_seed_cyclic_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (x : W) (hx : x ∈ c.imageSpace V) (hx0 : x ≠ 0) :
    orbitSpan ρ ⊤ x = ⊤ := by
  let P : Subrepresentation ρ := ⟨orbitSpan ρ ⊤ x, fun g w hw =>
    orbitSpan_stable ρ ⊤ x g (mem_top g) w hw⟩
  apply c.generated_image_le V rfl P
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]
    exact Submodule.zero_mem _
  obtain ⟨a,ha⟩ := local_quotient_seed_transitive h hI c (IntertwiningMap.id ρ)
    x ⟨x,hx,rfl⟩ hx0 y ⟨y,hy,rfl⟩ hy0
  exact ha ▸ orbit_mem ρ ⊤ x (inclusion (F.Li_one_le_of_mem_Hz hI) a) (mem_top _)

/-- The actual flag gives a nonzero Sylow-fixed cyclic generator of the
literal original section, with no module-model or cyclicity premise. -/
theorem local_exists_sylow_fixed_cyclic_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ) :
    ∃ x : W, x ∈ c.imageSpace (F.Vi 2) ∧ x ≠ 0 ∧
      orbitSpan ρ ⊤ x = ⊤ ∧
      ∀ t : I, (t : G) ∈ (T : Subgroup G) → ρ t x = x := by
  let : Finite W := Finite.of_surjective (fun v : F.UH I => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hd : Module.finrank (ZMod 2) (c.imageSpace (F.Vi 2)) = 1 := by
    apply c.imageSpace_finrank_of_index (F.Vi 2)
      ((F.le_seed 2).trans (le_conjugateSpanBy V I)) 1
    have hc := relIndex_mul_card_of_le (F.monotone (by decide : 1 ≤ 2))
    rw [F.card 1 (by decide),F.card 2 (by decide)] at hc
    norm_num at hc ⊢
    omega
  have hn : c.imageSpace (F.Vi 2) ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨x,hx,hx0,local_nonzero_seed_cyclic_at h hI c x
    (c.imageSpace_mono (F.le_seed 2) hx) hx0,?_⟩
  intro t ht
  exact local_quotient_plane_sylow_fixed c (IntertwiningMap.id ρ) t ht x ⟨x,hx,rfl⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
