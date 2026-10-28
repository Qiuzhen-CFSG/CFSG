module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceGeometry

/-!
# The original crossing moves the component radical image

The original actor t normalizes S and lies outside H. A Sylow two-subgroup
of the actual quotient-action kernel lies in R₂, so normalizing the image
of R₂ would force t to normalize R₂. The source normalizer theorem then
puts t in H, a contradiction. The containing component supplies the required
core bound without any strict-enlargement hypothesis.

Recovered from the checked SourceCrossing calculation of 23 October 2026.
Source: Aschbacher–Smith, original 4.3.3–5 and 4.3.14–15, pp.614–618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open EndgameSieve
section KernelLifting
variable {G H : Type*} [Group G] [Group H] {p : ℕ}

private theorem kernel_intersection_le_of_kernel_sylow
    (f : G →* H) (R S : Subgroup G) (hRS : R ≤ S) (hS : IsPGroup p S)
    (P : Sylow p f.ker) (hP : (P : Subgroup f.ker).map f.ker.subtype ≤ R) :
    f.ker ⊓ S ≤ R := by
  have he : S.subgroupOf f.ker = (P : Subgroup f.ker) := by
    apply P.is_maximal' (hS.comap_subtype)
    intro x hx
    exact hRS (hP (mem_map_of_mem f.ker.subtype hx))
  intro x hx
  have hp : (⟨x,hx.1⟩ : f.ker) ∈ (P : Subgroup f.ker) := by
    rw [←he]
    exact hx.2
  exact hP (mem_map_of_mem f.ker.subtype hp)

variable [Finite G]

private theorem normalizes_of_normalizes_image
    (f : G →* H) (R S : Subgroup G) (hRS : R ≤ S)
    (hker : f.ker ⊓ S ≤ R) (t : G) (htS : t ∈ normalizer (S : Set G))
    (htR : (R.map f).map (MulAut.conj (f t)).toMonoidHom = R.map f) :
    t ∈ normalizer (R : Set G) := by
  apply mem_normalizer_fintype
  intro r hr
  have hS : t*r*t⁻¹ ∈ S :=
    (mem_normalizer_iff.mp htS r).mp (hRS hr)
  have hI : f (t*r*t⁻¹) ∈ R.map f := by
    rw [map_mul,map_mul,map_inv]
    exact htR ▸ mem_map_of_mem (MulAut.conj (f t)).toMonoidHom (mem_map_of_mem f hr)
  obtain ⟨u,hu,he⟩ := hI
  have hk : u⁻¹*(t*r*t⁻¹) ∈ f.ker ⊓ S := by
    constructor
    · change f (u⁻¹*(t*r*t⁻¹)) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    · exact S.mul_mem (S.inv_mem (hRS hu)) hS
  have hh := R.mul_mem hu (hker hk)
  change t*r*t⁻¹ ∈ R
  simpa only [mul_inv_cancel_left] using hh


end KernelLifting
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}
  {n : ℕ} {d : MSData c n}

/-- The original crossing has nontrivial geometry on the literal radical image.
The action kernel is handled by its original Sylow subgroup, not by assuming
it equals the component core. No strict core enlargement appears. -/
theorem source_crossing_moves_radical_image (m : RootCoordinates d) (hn : 1 < n)
    (D : CFSG.Quasithin.Chapter12.Section02.ChosenModule T L V)
    (C : Subgroup (rootNormalizer c)) [C.Normal] (hperf : Group.IsPerfect C)
    (hbound : (C.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c) :
    let f := normalQuotientAction C (pCore 2 C)
    let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
    ((SourceImages.image c C (R₂ c)).map (MulAut.conj (f t)).toMonoidHom) ≠
      SourceImages.image c C (R₂ c) := by
  dsimp
  intro he
  let f := normalQuotientAction C (pCore 2 C)
  let R := (R₂ c).subgroupOf (rootNormalizer c)
  let S₀ := (S c).subgroupOf (rootNormalizer c)
  let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
  have hRS : R ≤ S₀ := subgroupOf_mono _ (radical_le_sylow c)
  obtain ⟨P,hP⟩ := SourceImages.action_kernel_sylow_le c C hperf D hbound
  have hker : f.ker ⊓ S₀ ≤ R := kernel_intersection_le_of_kernel_sylow f R S₀ hRS
    ((T.isPGroup'.to_le (show S c ≤ (T : Subgroup G) from inf_le_left)).comap_subtype) P hP
  have htS : t ∈ normalizer (S₀ : Set (rootNormalizer c)) := by
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ S c ↔ ((t : G) * (x : G) * (t : G)⁻¹) ∈ S c
    exact mem_normalizer_iff.mp c.crossing_normalizes (x : G)

  have htR : t ∈ normalizer (R : Set (rootNormalizer c)) :=
    normalizes_of_normalizes_image f R S₀ hRS hker t htS he
  have hr : R.map (rootNormalizer c).subtype = R₂ c :=
    map_subgroupOf_eq_of_le ((radical_le_sylow c).trans
      (inf_le_left.trans (root_normalized c D)))
  have htRG : c.t ∈ normalizer (R₂ c : Set G) := by
    rw [←hr]
    exact R.le_normalizer_map (rootNormalizer c).subtype
      (mem_map_of_mem (rootNormalizer c).subtype htR)
  exact c.crossing_outside ⟨c.crossing_mem,(m.radical_normalizer_le_original hn D) htRG⟩

/-- Apply the checked source radical bound to the actual containing component;
no enlarged-core or strict-enlargement premise remains. -/
theorem source_crossing_moves_component_radical_image (m : RootCoordinates d) (hn : 1 < n)
    (D : CFSG.Quasithin.Chapter12.Section02.ChosenModule T L V)
    (C : Subgroup (rootNormalizer c)) [C.Normal] (hperf : Group.IsPerfect C)
    (hsec : secondary c ≤ C.map (rootNormalizer c).subtype) :
    let f := normalQuotientAction C (pCore 2 C)
    let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
    ((SourceImages.image c C (R₂ c)).map (MulAut.conj (f t)).toMonoidHom) ≠
      SourceImages.image c C (R₂ c) := by
  dsimp
  apply source_crossing_moves_radical_image m hn D C hperf
  exact m.enlarged_core_le_radical_source hn D _
    (sup_le (hsec.trans le_sup_left) (inf_le_left.trans le_sup_right))


end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
