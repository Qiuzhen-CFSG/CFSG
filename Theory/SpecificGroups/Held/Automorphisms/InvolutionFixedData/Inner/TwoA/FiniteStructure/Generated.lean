module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure.Words
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.CentralizerCertificate
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison
public import Theory.GroupTheory.PerfectTriangle

/-!
# The generated perfect cover in the Held 2A centralizer

The (3,5,7) relations make K = <x,y> perfect. Agreement of its generator
actions with the existing matrix generating pair constructs a surjection
onto PSL3(4). Four distinct central elements lie in its kernel. Hence K
has at least 80640 elements. A checked noncommutation proves K proper in
the literal centralizer of order 161280, forcing index two and K = C'.
The same order calculation exhausts the kernel by those four elements.

The matrix order and generation theorems are proved in the existing licensed
ATLAS port and projective comparison. No discovered order is a premise.
Source: GLS3 Table 5.3p (2A row), printed p.277; `Source/README.md`.
-/

@[expose] public section
open Subgroup
namespace Held.InvolutionFixedData.TwoA.FiniteStructure
open CentralizerCertificate ProjectiveComparison

def candidate : Subgroup centralizer := Subgroup.closure ({x, y} : Set centralizer)
def xK : candidate := ⟨x, Subgroup.subset_closure (Set.mem_insert _ _)⟩
def yK : candidate := ⟨y, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem pair_generates : Subgroup.closure ({xK, yK} : Set candidate) = ⊤ := by
  apply Subgroup.map_injective candidate.subtype_injective
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  change candidate = (⊤ : Subgroup candidate).map candidate.subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

instance candidate_perfect : Group.IsPerfect candidate :=
  Group.isPerfect_closure_pair_of_coprime_triangle x y (by decide) (by decide)
    x_cube y_fifth xy_seventh

def zA : candidate := (xK * yK⁻¹) ^ 3
def zB : candidate := (xK * yK ^ 2) ^ 7

theorem zA_val : zA.val = centralizerGenerator 0 := first_central_word
theorem zB_val : zB.val = qC := second_central_word

theorem zA_center : zA ∈ Subgroup.center candidate := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change g.val * zA.val = zA.val * g.val
  rw [zA_val]
  apply Subtype.ext
  change g.val.val * a = a * g.val.val
  exact Subgroup.mem_centralizer_singleton_iff.mp (centralizer_eq ▸ g.val.property)

theorem zB_center : zB ∈ Subgroup.center candidate := by
  have hq : qC ∈ Subgroup.centralizer (candidate : Set centralizer) := by
    rw [candidate, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact qC_commute_x.symm
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact qC_commute_y.symm
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change g.val * zB.val = zB.val * g.val
  rw [zB_val]
  exact hq g.val g.property

theorem candidate_ne_top : candidate ≠ ⊤ := by
  intro h
  let g : candidate := ⟨centralizerGenerator 1, h.symm ▸ Subgroup.mem_top _⟩
  have he := congrArg Subtype.val (Subgroup.mem_center_iff.mp zB_center g)
  change centralizerGenerator 1 * zB.val = zB.val * centralizerGenerator 1 at he
  rw [zB_val] at he
  exact qC_not_commute he

theorem lifts : ∀ s ∈ ({projectiveA, projectiveB} : Set PSL),
    ∃ g : candidate, ∀ p : PG, g • label p = label (s • p) := by
  intro s hs
  rcases hs with rfl | hs
  · refine ⟨xK, ?_⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveA_point, label_pointEquiv, label_pointEquiv]
    exact x_labels i
  · obtain rfl := Set.mem_singleton_iff.mp hs
    refine ⟨yK, ?_⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveB_point, label_pointEquiv, label_pointEquiv]
    exact y_labels i

noncomputable def leftMap : agreement (G := candidate) (H := PSL) label →* candidate :=
  agreementLeft label
noncomputable def rightMap : agreement (G := candidate) (H := PSL) label →* PSL :=
  agreementRight label

theorem leftMap_bijective : Function.Bijective leftMap := by
  refine ⟨agreementLeft_injective label label_injective, ?_⟩
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← pair_generates, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · refine ⟨⟨(xK, projectiveA), ?_⟩, rfl⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveA_point, label_pointEquiv, label_pointEquiv]
    exact x_labels i
  · obtain rfl := Set.mem_singleton_iff.mp hg
    refine ⟨⟨(yK, projectiveB), ?_⟩, rfl⟩
    intro p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [projectiveB_point, label_pointEquiv, label_pointEquiv]
    exact y_labels i

noncomputable def leftEquiv : agreement (G := candidate) (H := PSL) label ≃* candidate :=
  MulEquiv.ofBijective leftMap leftMap_bijective
noncomputable def candidateProjection : candidate →* PSL :=
  rightMap.comp leftEquiv.symm.toMonoidHom

theorem candidateProjection_surjective : Function.Surjective candidateProjection :=
  (agreementRight_surjective label _ projective_pair_generates lifts).comp leftEquiv.symm.surjective

theorem candidateProjection_agrees (g : candidate) (p : PG) :
    g • label p = label (candidateProjection g • p) := by
  have h := (leftEquiv.symm g).property p
  have hg : (leftEquiv.symm g).val.1 = g := leftEquiv.apply_symm_apply g
  change (leftEquiv.symm g).val.1 • label p = label (candidateProjection g • p) at h
  simpa only [hg] using h

theorem mem_candidateProjection_ker (g : candidate) :
    g ∈ candidateProjection.ker ↔ ∀ p : PG, g • label p = label p := by
  constructor
  · intro hg p
    rw [candidateProjection_agrees, show candidateProjection g = 1 from hg, one_smul]
  · intro h
    change candidateProjection g = 1
    apply eq_of_smul_eq_smul (α := PG)
    intro p
    apply label_injective
    rw [← candidateProjection_agrees, one_smul, h]

def four (i : Fin 4) : candidate := ![1, zA, zB, zA * zB] i

theorem four_val (i : Fin 4) : (four i).val =
    (![1, centralizerGenerator 0, qC, centralizerGenerator 0 * qC] : Fin 4 → centralizer) i := by
  fin_cases i
  · rfl
  · exact zA_val
  · exact zB_val
  · exact congrArg₂ (· * ·) zA_val zB_val

theorem four_injective : Function.Injective four := by
  intro i j h
  apply four_distinct
  simpa only [four_val] using congrArg (fun g : candidate => representation g.val.val 0) h

theorem four_center (i : Fin 4) : four i ∈ Subgroup.center candidate := by
  fin_cases i
  · exact (Subgroup.center candidate).one_mem
  · exact zA_center
  · exact zB_center
  · exact (Subgroup.center candidate).mul_mem zA_center zB_center

theorem four_fix (i : Fin 4) : four i • (25 : Fin 2058) = 25 := by
  have ha : zA • (25 : Fin 2058) = 25 := by
    change representation zA.val.val 25 = 25
    rw [zA_val]
    decide +kernel
  have hb : zB • (25 : Fin 2058) = 25 := by
    change representation zB.val.val 25 = 25
    rw [zB_val]
    exact q_fixed
  fin_cases i
  · exact one_smul _ _
  · exact ha
  · exact hb
  · change (zA * zB) • (25 : Fin 2058) = 25
    rw [mul_smul, hb, ha]

theorem four_ker (i : Fin 4) : four i ∈ candidateProjection.ker := by
  rw [mem_candidateProjection_ker]
  intro p
  have hp := labels_mem_orbit label _ projective_pair_generates lifts (pointEquiv 0) p
  rw [label_pointEquiv, pointLabel_zero] at hp
  obtain ⟨g, hg⟩ := hp
  rw [← hg, ← mul_smul, ← Subgroup.mem_center_iff.mp (four_center i) g,
    mul_smul, four_fix]

theorem kernel_card_lower : 4 ≤ Nat.card candidateProjection.ker := by
  let f : Fin 4 → candidateProjection.ker := fun i => ⟨four i, four_ker i⟩
  have hi : Function.Injective f := fun i j h => four_injective (congrArg Subtype.val h)
  simpa using Nat.card_le_card_of_injective f hi

theorem projection_card : Nat.card candidateProjection.ker * 20160 = Nat.card candidate := by
  have h := candidateProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr candidateProjection_surjective,
    Subgroup.card_top] at h
  have hm : Nat.card PSL = 20160 :=
    (Nat.card_congr modelEquiv.toEquiv).trans Matrix.PSL3Four.card_PSL
  exact (congrArg (Nat.card candidateProjection.ker * ·) hm).symm.trans h

theorem candidate_card_lower : 80640 ≤ Nat.card candidate := by
  exact (Nat.mul_le_mul_right 20160 kernel_card_lower).trans_eq projection_card

theorem candidate_index : candidate.index = 2 := by
  have he := candidate.card_mul_index
  rw [centralizer_card] at he
  have hp := candidate.index_ne_zero_of_finite
  have hn : candidate.index ≠ 1 := fun h => candidate_ne_top (Subgroup.index_eq_one.mp h)
  have hl := candidate_card_lower
  have hu : candidate.index ≤ 2 := by nlinarith
  omega

theorem candidate_eq_derived : candidate = derived :=
  perfect_subgroup_eq_derived_of_index_two candidate candidate_index

theorem candidate_card : Nat.card candidate = 80640 := by
  have h := candidate.card_mul_index
  rw [candidate_index, centralizer_card] at h
  omega

theorem kernel_card : Nat.card candidateProjection.ker = 4 := by
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 20160)
    (projection_card.trans candidate_card)

theorem kernel_central : candidateProjection.ker ≤ Subgroup.center candidate := by
  let f : Fin 4 → candidateProjection.ker := fun i => ⟨four i, four_ker i⟩
  have hi : Function.Injective f := fun i j h => four_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, (Nat.card_fin 4).trans kernel_card.symm⟩).2
  intro g hg
  obtain ⟨i, hi⟩ := hs ⟨g, hg⟩
  have he : four i = g := congrArg Subtype.val hi
  exact he ▸ four_center i

end Held.InvolutionFixedData.TwoA.FiniteStructure
