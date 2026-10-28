module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The binary invariant subgroup lattice of the point radical

For the actual point local D and point parabolic P, the center of D embeds as
long root zero. A D-normal subgroup of Q=O₂(D) is central or all of Q:
apply natural binary irreducibility to its join with Z(D), then use [Q,D]=Q
to exclude a proper central supplement. The root torus is transitive on
nonidentity elements of Z(D), so P-invariance leaves exactly 1, Z(D), and Q.
These are arbitrary subgroups, with no closure under defining-field scalars.
The strict chain and its normalization prove both chief factors; the same
lattice excludes every nontrivial invariant direct sum decomposition.

Source: Aschbacher--Smith 11.5.7, assertion (!), refs/quasithin.pdf,
printed pp.782--783. The argument also applies to the smallest nonbinary
field, of order four, through the proved nonbinary commutator calculation.
-/

public noncomputable section
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PointRadicalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

include hcard hn in
/-- The entire local center lies in its explicit radical. -/
theorem center_le_radical : center (pointLocal (F := F)) ≤ pointRadical := by
  rw [← (pointNaturalExtension hcard hn).centralizer_eq]
  exact center_le_centralizer _

omit [Finite F] in
/-- The central coordinate is the literal long-root matrix in family zero. -/
theorem central_element_eq_root (z : F) :
    (pointRadicalElement 0 0 z).val = rootElement 0 z := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, rootElement, rootMatrix, Matrix.single]

include hcard hn in
/-- The embedded local center is exactly the full standard long root. -/
theorem center_eq_root :
    (center (pointLocal (F := F))).map pointLocal.subtype = RootSubgroup.group 0 := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨z, hz⟩ := (pointRadical_mem_center_iff
      (⟨g, center_le_radical hcard hn hg⟩ : pointRadical)).mp hg
    change g = pointRadicalElement 0 0 z at hz
    change g.val ∈ RootSubgroup.group 0
    rw [hz, central_element_eq_root]
    exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨z, rfl⟩
  · intro g hg
    obtain ⟨z, rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
    exact ⟨pointRadicalElement 0 0 z, pointRadicalElement_central z,
      central_element_eq_root z⟩

include hcard hn in
/-- A local-normal subgroup of the radical is central or the entire radical. -/
theorem normal_radical_dichotomy (N : Subgroup (pointLocal (F := F))) [N.Normal]
    (hN : N ≤ pointRadical) : N ≤ center _ ∨ N = pointRadical := by
  have hc := center_le_radical hcard hn
  have he : pointRadical (F := F) ⊓ center (pointLocal (F := F)) = center _ :=
    inf_eq_right.mpr hc
  have hi := (pointNaturalExtension hcard hn).invariant_interval (N ⊔ center _)
    (by rw [he]; exact le_sup_right) (sup_le hN hc)
  rcases hi with hi | hi
  · exact Or.inl (le_sup_left.trans (hi.le.trans inf_le_right))
  · right
    apply le_antisymm hN
    rw [← pointRadical_commutator_eq hcard hn, ← hi]
    apply commutator_sup_le_of_relative_normal ⊤ N (center _) ⊤ N
      (by rw [normalizer_eq_top]) le_top le_top (commutator_le_left _ _)
    simp

/-- Parabolic-invariant subgroups inside the center are trivial or full. -/
theorem root_invariant_dichotomy (A : Subgroup (Sp F))
    (hA : A ≤ RootSubgroup.group 0)
    (hP : pointParabolic ≤ normalizer (A : Set (Sp F))) :
    A = ⊥ ∨ A = RootSubgroup.group 0 := by
  by_cases hz : A = ⊥
  · exact Or.inl hz
  right
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hz
  apply le_antisymm hA
  intro b hb
  by_cases hb1 : b = 1
  · simp [hb1]
  obtain ⟨y, hy, _⟩ := RootTori.regular 0 a b (hA ha) hb ha1 hb1
  have hyp : (y : Sp F) ∈ pointParabolic := by
    rw [← RootNormalizerResidual.normalizer_zero_eq]
    exact RootTori.torus_le_normalizer 0 y.property
  rw [← hy]
  exact (mem_normalizer_iff.mp (hP hyp) a).mp ha

include hcard hn in
/-- The exact invariant subgroup lattice of the ambient embedded two-core. -/
theorem invariant_lattice (A : Subgroup (Sp F))
    (hA : A ≤ (pointLocal (F := F)).pCoreIn 2)
    (hP : pointParabolic ≤ normalizer (A : Set (Sp F))) :
    A = ⊥ ∨ A = (center (pointLocal (F := F))).map pointLocal.subtype ∨
      A = (pointLocal (F := F)).pCoreIn 2 := by
  have hAR : A ≤ (pointRadical (F := F)).map pointLocal.subtype := by
    simpa only [pCoreIn, pointLocal_core_eq hcard hn] using hA
  have hAL : A ≤ pointLocal := hA.trans (pCoreIn_le 2 _)
  let N := A.subgroupOf (pointLocal (F := F))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hAL).mpr
    (pointLocal_le.trans hP)
  have hN : N ≤ pointRadical := by
    intro g hg
    obtain ⟨q, hq, he⟩ := hAR hg
    exact pointLocal.subtype_injective he ▸ hq
  have hmap : N.map pointLocal.subtype = A := map_subgroupOf_eq_of_le hAL
  rcases normal_radical_dichotomy hcard hn N hN with hc | he
  · have hroot : A ≤ RootSubgroup.group 0 := by
      rw [← center_eq_root hcard hn, ← hmap]
      exact map_mono hc
    rcases root_invariant_dichotomy A hroot hP with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl (hz.trans (center_eq_root hcard hn).symm))
  · right; right
    rw [← hmap, he]
    simp only [pCoreIn, pointLocal_core_eq hcard hn]

include hcard hn in
/-- Both factors of the proposed chief series are nontrivial. -/
theorem chief_series :
    ⊥ < (center (pointLocal (F := F))).map pointLocal.subtype ∧
      (center (pointLocal (F := F))).map pointLocal.subtype <
        (pointLocal (F := F)).pCoreIn 2 := by
  constructor
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    have hm : (pointRadicalElement (0 : F) 0 1).val ∈
        (center (pointLocal (F := F))).map pointLocal.subtype :=
      mem_map_of_mem _ (pointRadicalElement_central 1)
    rw [he, mem_bot] at hm
    have hh := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 0)) hm
    exact one_ne_zero hh
  · rw [pCoreIn, pointLocal_core_eq hcard hn]
    apply lt_of_le_of_ne (map_mono (center_le_radical hcard hn))
    intro he
    have hm : (pointRadicalElement (1 : F) 0 0).val ∈
        (pointRadical (F := F)).map pointLocal.subtype :=
      mem_map_of_mem _ (pointRadicalElement_mem 1 0 0)
    rw [← he] at hm
    obtain ⟨x, hx, he⟩ := hm
    have hx' : x = pointRadicalElement (1 : F) 0 0 := Subtype.ext he
    rw [hx'] at hx
    exact one_ne_zero ((pointRadicalElement_mem_center_iff _ _ _).mp hx).1

include hcard hn in
/-- Every nontrivial invariant subgroup of the radical contains the center. -/
theorem center_le_of_invariant_ne_bot (A : Subgroup (Sp F))
    (hA : A ≤ (pointLocal (F := F)).pCoreIn 2)
    (hP : pointParabolic ≤ normalizer (A : Set (Sp F))) (hne : A ≠ ⊥) :
    (center (pointLocal (F := F))).map pointLocal.subtype ≤ A := by
  rcases invariant_lattice hcard hn A hA hP with h | h | h
  · exact (hne h).elim
  · exact h.ge
  · rw [h]
    exact (chief_series hcard hn).2.le

include hcard hn in
/-- The binary radical has no nontrivial decomposition into invariant summands. -/
theorem indecomposable (A B : Subgroup (Sp F))
    (hA : pointParabolic ≤ normalizer (A : Set (Sp F)))
    (hB : pointParabolic ≤ normalizer (B : Set (Sp F)))
    (hjoin : A ⊔ B = (pointLocal (F := F)).pCoreIn 2)
    (hmeet : A ⊓ B = ⊥) : A = ⊥ ∨ B = ⊥ := by
  by_cases ha : A = ⊥
  · exact Or.inl ha
  by_cases hb : B = ⊥
  · exact Or.inr hb
  have haZ := center_le_of_invariant_ne_bot hcard hn A
    (le_sup_left.trans hjoin.le) hA ha
  have hbZ := center_le_of_invariant_ne_bot hcard hn B
    (le_sup_right.trans hjoin.le) hB hb
  have hle := le_inf haZ hbZ
  rw [hmeet] at hle
  exact ((chief_series hcard hn).1.not_ge hle).elim

include hcard hn in
/-- The acting parabolic normalizes both terms of the strict chief series. -/
theorem normalizes_center_and_core :
    pointParabolic ≤ normalizer
      ((center (pointLocal (F := F))).map pointLocal.subtype : Set (Sp F)) ∧
    pointParabolic ≤ normalizer ((pointLocal (F := F)).pCoreIn 2 : Set (Sp F)) := by
  constructor
  · rw [center_eq_root hcard hn, RootNormalizerResidual.normalizer_zero_eq]
  · change pointParabolic ≤ normalizer
      ((pCore 2 (pointLocal (F := F))).map pointLocal.subtype : Set (Sp F))
    rw [pointLocal_core_eq hcard hn, ← pointParabolic_core_map_eq_radical hcard hn]
    exact pointParabolic.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

end Theory.SpecificGroups.SymplecticFour.PointRadicalAction
