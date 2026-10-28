module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
public import Theory.GroupTheory.PCorePreimageCentralizer
/-!
# All nontrivial two-subgroup normalizers in even Sp₄

The actual normalizer lies in a conjugate point or plane parabolic by the
fixed-space radical geometry. Each full parabolic has characteristic two,
which passes to its relative normalizer. Since the full normalizer is already
contained there, this proves characteristic two of the original normalizer.
The final theorem lifts through a two-group kernel contained in the radical.

Source application: Aschbacher–Smith, 2.5.3(4), printed p.553.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]

private theorem normalizer_core_of_contained {G : Type*} [Group G] [Finite G]
    (R P : Subgroup G) (hp : IsPGroup 2 R)
    (hle : normalizer (R : Set G) ≤ P)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (normalizer (R : Set G)) : Set (normalizer (R : Set G))) ≤
      pCore 2 (normalizer (R : Set G)) := by
  have hRP : R ≤ P := R.le_normalizer.trans hle
  have hh : centralizer (pCore 2 ((normalizer (R : Set G)).subgroupOf P) :
      Set ((normalizer (R : Set G)).subgroupOf P)) ≤
      pCore 2 ((normalizer (R : Set G)).subgroupOf P) := by
    rw [subgroupOf_normalizer_eq hRP]
    exact Subgroup.normalizer_core_selfCentralizing hc _ hp.comap_subtype
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hle)).mp hh

/-- The actual normalizer of every nontrivial two-subgroup has characteristic two. -/
theorem normalizer_core_selfCentralizing {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (R : Subgroup (Sp F)) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set (Sp F))) :
      Set (normalizer (R : Set (Sp F)))) ≤ pCore 2 (normalizer (R : Set (Sp F))) := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover hF hn (normalizer (R : Set (Sp F)))
    ⟨R,hne,hp,rfl⟩
  rw [map_normalizer_eq_of_bijective R (MulAut.conj g).bijective] at hg
  apply Subgroup.normalizer_core_selfCentralizing_of_equiv (MulAut.conj g) R
  rcases hg with hg | hg
  · exact normalizer_core_of_contained _ _ (hp.map _) hg
      (pointParabolic_selfCentralizing_core hF hn)
  · exact normalizer_core_of_contained _ _ (hp.map _) hg
      (planeParabolic_selfCentralizing_core hF hn)

/-- A two-kernel cover has the same local property when the specified radical
contains the kernel and has nontrivial image in Sp₄. -/
theorem cover_normalizer_core_selfCentralizing
    {E : Type*} [Group E] [Finite E] (f : E →* Sp F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (R : Subgroup E) (hp : IsPGroup 2 R) (hker : f.ker ≤ R)
    (hne : R.map f ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set E)) :
      Set (normalizer (R : Set E))) ≤ pCore 2 (normalizer (R : Set E)) := by
  have hpre : (R.map f).comap f = R := Subgroup.comap_map_eq_self hker
  have hN : normalizer (R : Set E) = (normalizer (R.map f : Set (Sp F))).comap f := by
    rw [comap_normalizer_eq_of_surjective _ hf, hpre]
  let : f.range.Normal := by
    rw [f.range_eq_top_of_surjective hf]
    infer_instance
  rw [hN]
  exact f.centralizer_pCore_comap_of_normal_range hk _
    (normalizer_core_selfCentralizing hF hn (R.map f) (hp.map f) hne)

end Theory.SpecificGroups.SymplecticFour
