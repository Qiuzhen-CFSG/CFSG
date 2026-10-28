module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Interpretation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Actions

/-!
# Assembling the two Fi22 generator lifts in the Fi23 centralizer

Two explicit compressed words are genuine members of the Fi23 ATLAS carrier.
Once their evaluations agree with the published numerical tables, the checked
commutation identities put them in the literal candidate's centralizer. The
checked coordinate identities then give both exact Fi22 generator actions,
including the additional `none` point.

This is conditional assembly: the two compressed-word evaluation certificates
and the separately owned Fi23 source-map comparisons are still required. This
module does not claim the unconditional generator-lift theorem or the full image
identification, whose owner remains `Fi23Centralizer.Image`.

Source: GLS3 Table 5.3u and `refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1042.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open GeneratorLiftCertificate
open Fi24Prime.Fi23Lift.Certificate (sourceA sourceB)

-- Keep the proof of multiplication compatibility abstract so the kernel does
-- not unfold the original string-decoded generators while checking it.
private theorem centralizes_of_maps {G α : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (hρ : Function.Injective ρ) (t g : G)
    (f k : α → α) (ht : ∀ x, ρ t x = f x) (hg : ∀ x, ρ g x = k x)
    (hc : ∀ x, f (k x) = k (f x)) :
    g ∈ Subgroup.centralizer ({t} : Set G) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply hρ
  apply Equiv.ext
  intro x
  simp only [map_mul, Equiv.Perm.mul_apply, ht, hg]
  exact (hc x).symm

private theorem exists_lifts_of_maps (g h : Carrier)
    (ha : ∀ x, generatorA x = sourceA x)
    (hb : ∀ x, generatorB x = sourceB x)
    (hu : ∀ x, inclusion g x = liftA x)
    (hv : ∀ x, inclusion h x = liftB x) :
    ∃ u v : numerator,
      (∀ i : Option (Fin 3510), inclusion u.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorA i)) ∧
      (∀ i : Option (Fin 3510), inclusion v.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorB i)) := by
  have ht (x : Fin 31671) : inclusion candidate x = candidateMap x :=
    (candidateMap_eq_inclusion_candidate ha hb x).symm
  have huc : g ∈ numerator :=
    centralizes_of_maps inclusion inclusion_injective candidate g candidateMap liftA
      ht hu (fun x => (candidate_checks x).2.1)
  have hvc : h ∈ numerator :=
    centralizes_of_maps inclusion inclusion_injective candidate h candidateMap liftB
      ht hv (fun x => (candidate_checks x).2.2)
  refine ⟨⟨g, huc⟩, ⟨h, hvc⟩, ?_, ?_⟩
  · intro i
    exact (hu _).trans (liftA_points i)
  · intro i
    exact (hv _).trans (liftB_points i)


/-- The exact lower-image witnesses, conditional only on outstanding word and
source-table evaluations. Membership in Fi23 is supplied by the words themselves;
centralization and all 3511 coordinate identities are consequences. -/
theorem exists_generator_lifts_of_word_tables
    (ha : ∀ x, generatorA x = sourceA x)
    (hb : ∀ x, generatorB x = sourceB x)
    (hu : ∀ x, inclusion liftWordA x = liftA x)
    (hv : ∀ x, inclusion liftWordB x = liftB x) :
    ∃ u v : numerator,
      (∀ i : Option (Fin 3510), inclusion u.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorA i)) ∧
      (∀ i : Option (Fin 3510), inclusion v.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorB i)) :=
  exists_lifts_of_maps liftWordA liftWordB ha hb hu hv

end Sporadic.Fischer.Fi23.CentralizerSection
