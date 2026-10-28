module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage

/-!
# Restricted binary Ree cells and their proposed Weyl representatives

The split normal form descends to the full exceptional fixed matrix group while
retaining its right factor `U ∩ n⁻¹U⁻n`. This restriction is essential for
counting: the unrestricted product `U × W × U` is too large.

The sixteen alternating words below are concrete products of the two fixed
orbit lifts. This module proves their membership in the Weyl subgroup, but
does not assert that they exhaust it. Likewise, `cellExponent` records the
desired cell estimates, not a proved order formula. Exhaustiveness and those
estimates are separate inputs to the counting assembly.

Sources: GLS3 §§2.3.2–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
The carrier is the full binary Ree group, not its simple derived subgroup.
-/

@[expose] public section
noncomputable section

namespace ReeF4.DerivedTits.BruhatBound

open Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage LargeLocalSeeds

/-- The right inversion subgroup, inside the full fixed matrix carrier. -/
def fixedRightUnipotent (n : Model 0) : Subgroup (Model 0) :=
  (rightUnipotent (toSplitGroup 0 n)).comap (toSplitGroup 0)

theorem fixedRightUnipotent_le (n : Model 0) :
    fixedRightUnipotent n ≤ unipotent 0 := by
  intro v hv
  exact hv.1

/-- Fixed-point descent retaining the restricted right inversion factor. -/
theorem exists_restricted_normal_form (g : Model 0) :
    ∃ u ∈ unipotent 0, ∃ n ∈ weylSubgroup 0,
      ∃ v ∈ fixedRightUnipotent n, g = u * n * v := by
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := exists_split_normal_form (toSplitGroup 0 g)
  have hproduct : reeTwist 0 u * reeTwist 0 n * reeTwist 0 v = u * n * v := by
    rw [← map_mul, ← map_mul, ← he, reeTwist_toSplitGroup, he]
  have hnfix : reeTwist 0 n = n := middle_representative_unique
    (reeTwist_mem_splitUnipotent hu) (reeTwist_mem_splitWeylSubgroup hn)
    (reeTwist_mem_rightUnipotent hv) hu hn hv hproduct
  obtain ⟨hufix, hvfix⟩ := fixed_unipotent_factors (reeTwist_toSplitGroup 0 g)
    hnfix hu hv he
  let u₀ : Model 0 := ⟨u, (mem_fixedSubgroup 0 u).mpr hufix⟩
  let n₀ : Model 0 := ⟨n, (mem_fixedSubgroup 0 n).mpr hnfix⟩
  let v₀ : Model 0 := ⟨v, (mem_fixedSubgroup 0 v).mpr hvfix⟩
  have hn₀ : n₀ ∈ weylSubgroup 0 := by
    apply splitWeylSubgroup_comap_le_weylSubgroup
    change toSplitGroup 0 n₀ ∈ splitWeylSubgroup
    simpa only [toSplitGroup_apply] using hn
  have hu₀ : u₀ ∈ unipotent 0 := by
    change toSplitGroup 0 u₀ ∈ splitUnipotent 0
    simpa only [toSplitGroup_apply] using hu
  have hv₀ : v₀ ∈ fixedRightUnipotent n₀ := by
    change toSplitGroup 0 v₀ ∈ rightUnipotent (toSplitGroup 0 n₀)
    simpa only [toSplitGroup_apply] using hv
  refine ⟨u₀, hu₀, n₀, hn₀, v₀, hv₀, ?_⟩
  apply toSplitGroup_injective 0
  simpa only [map_mul, toSplitGroup_apply] using he

/-- Alternating words of relative lengths zero through eight, with the
linear-starting word first at each of lengths one through seven. -/
def relativeWord : Fin 16 → List Side :=
  ![[], [.linear], [.suzuki], [.linear, .suzuki], [.suzuki, .linear],
    [.linear, .suzuki, .linear], [.suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki], [.suzuki, .linear, .suzuki, .linear],
    [.linear, .suzuki, .linear, .suzuki, .linear],
    [.suzuki, .linear, .suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki],
    [.suzuki, .linear, .suzuki, .linear, .suzuki, .linear],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki, .linear],
    [.suzuki, .linear, .suzuki, .linear, .suzuki, .linear, .suzuki],
    [.linear, .suzuki, .linear, .suzuki, .linear, .suzuki, .linear, .suzuki]]

/-- The corresponding words in the four numbered split simple reflections. -/
def splitWord (i : Fin 16) : List (Fin 4) :=
  ((relativeWord i).map sideWord).flatten

/-- Actual fixed matrices represented by the sixteen alternating words. -/
def weylRepresentative (i : Fin 16) : Model 0 :=
  ((relativeWord i).map (weylLift 0)).prod

theorem weylRepresentative_mem (i : Fin 16) :
    weylRepresentative i ∈ weylSubgroup 0 := by
  apply Subgroup.list_prod_mem
  intro n hn
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hn
  exact weylLift_mem_weylSubgroup 0 s

/-- The fixed representative has exactly the stated split matrix word. -/
theorem toSplitGroup_weylRepresentative (i : Fin 16) :
    toSplitGroup 0 (weylRepresentative i) = simpleWord 0 (splitWord i) := by
  have h (l : List Side) :
      toSplitGroup 0 ((l.map (weylLift 0)).prod) =
        simpleWord 0 ((l.map sideWord).flatten) := by
    induction l with
    | nil => simp [simpleWord]
    | cons s l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, toSplitGroup_weylLift,
        List.flatten_cons, FixedWeyl.simpleWord_append, ih]
  exact h (relativeWord i)

/-- Exponents for the cell bounds to be proved, in the order `relativeWord`.
Pairs contribute one binary scalar and B₂ quartets contribute two. -/
def cellExponent : Fin 16 → ℕ :=
  ![0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 8, 9, 9, 10, 11, 12]

/-- Arithmetic of the proposed bounds; this does not assert any cell size. -/
theorem sum_cell_bounds : ∑ i : Fin 16, 2 ^ cellExponent i = 8775 := by
  norm_num [Fin.sum_univ_succ, cellExponent]

end ReeF4.DerivedTits.BruhatBound
