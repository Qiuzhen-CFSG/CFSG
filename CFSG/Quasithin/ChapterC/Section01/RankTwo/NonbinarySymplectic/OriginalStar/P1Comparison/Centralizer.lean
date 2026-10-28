module
public import Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections.Marked
public import Theory.SpecificGroups.SymplecticFour.RootHyperplaneComparison
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The original marked relative centralizer

For a whole natural kernel and an opposite subgroup with the long-root image,
their commutator is exactly the original natural point line. Their intersection
is the corresponding hyperplane. The point radical moves this hyperplane into
the point line, so the intersection lies in the relative centralizer. The same
point parabolic normalizes that centralizer.

These are the intrinsic containment and invariance clauses for the centralizer
used in Meierfrankenfeld--Stellmacher (1993), (3.7), printed p.877. The relative
order and projection clauses require an additional argument.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

/-- The literal embedding recovered from the whole natural-kernel coordinates. -/
@[expose] def naturalEmbedding : Multiplicative (Vector F) →* G :=
  A.subtype.comp s.natural.symm.toMonoidHom

/-- The natural coordinates retain the entire original kernel. -/
theorem naturalEmbedding_range : (naturalEmbedding s).range = A := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    exact (s.natural.symm v).property
  · intro a ha
    refine ⟨s.natural ⟨a,ha⟩,?_⟩
    exact congrArg Subtype.val (s.natural.symm_apply_apply ⟨a,ha⟩)

/-- The embedding intertwines the same quotient marking. -/
theorem naturalEmbedding_conjugation (g : G) (v : Vector F) :
    naturalEmbedding s (Multiplicative.ofAdd (κ g • v)) =
      g * naturalEmbedding s (Multiplicative.ofAdd v) * g⁻¹ := by
  let : A.Normal := s.kernel ▸ inferInstance
  let x : A := s.natural.symm (Multiplicative.ofAdd v)
  let y : A := ⟨g*x*g⁻¹,(inferInstance : A.Normal).conj_mem _ x.property g⟩
  have h := s.natural_conjugation g x y rfl
  have hy : s.natural y = Multiplicative.ofAdd (κ g • v) := by
    apply Multiplicative.toAdd.injective
    simpa [x] using h
  have hy' := congrArg s.natural.symm hy
  rw [s.natural.symm_apply_apply] at hy'
  exact congrArg Subtype.val hy'.symm

/-- The critical commutator is exactly the distinguished natural point. -/
theorem critical_commutator_image :
    ⁅A,B⁆ = (point F).toAddSubgroup.toSubgroup'.map (naturalEmbedding s) := by
  have he := RootHyperplaneComparison.commutator_eq_displacement_image B A
    (naturalEmbedding s) (naturalEmbedding_range s) (κ.comp B.subtype)
    (fun b v => naturalEmbedding_conjugation s b v)
  have hr : (κ.comp B.subtype).range=RootSubgroup.group 0 := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype,s.root_image]
  rw [hr,PointRadicalAction.root_displacement,commutator_comm] at he
  exact he

/-- The actual intersection is the natural cofixed hyperplane. -/
theorem intersection_coordinate [Finite G] (v : Vector F) :
    naturalEmbedding s (Multiplicative.ofAdd v) ∈ A ⊓ B ↔ coordinate v=0 := by
  have hA : naturalEmbedding s (Multiplicative.ofAdd v) ∈ A :=
    (naturalEmbedding_range s).le (show naturalEmbedding s (Multiplicative.ofAdd v) ∈ (naturalEmbedding s).range from ⟨_,rfl⟩)
  rw [mem_inf,and_iff_right hA]
  change s.natural.symm (Multiplicative.ofAdd v) ∈ B.subgroupOf A ↔ _
  rw [←s.naturalLine_kernel]
  change s.naturalLine (s.natural.symm (Multiplicative.ofAdd v))=1 ↔ _
  change Multiplicative.ofAdd (coordinate (s.natural (s.natural.symm (Multiplicative.ofAdd v))).toAdd)=1 ↔ _
  rw [s.natural.apply_symm_apply]
  rfl

private theorem radical_hyperplane_displacement [CharP F 2]
    (g : Sp F) (hg : g ∈ pointRadicalAmbient) (v : Vector F)
    (hv : coordinate v=0) : g • v-v ∈ point F := by
  obtain ⟨g,hg,rfl⟩ := hg
  rw [pointRadical_eq_element g hg]
  apply (mem_point_iff _).mpr
  have hv' : v (.inr 0)=0 := hv
  constructor
  · simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,hv']
  · intro i
    fin_cases i <;> simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,hv']

include s in
/-- The point-core preimage centralizes the intersection modulo the critical line. -/
theorem intersection_pointCore_commutator [Finite G] [CharP F 2] :
    ⁅A ⊓ B,pointRadicalAmbient.comap κ⁆ ≤ ⁅A,B⁆ := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg x hx
  obtain ⟨v,rfl⟩ := (naturalEmbedding_range s).symm ▸ hx.1
  have hv := (intersection_coordinate s v.toAdd).mp hx
  have hd := radical_hyperplane_displacement (κ g) hg v.toAdd hv
  rw [critical_commutator_image s]
  refine ⟨Multiplicative.ofAdd (κ g • v.toAdd-v.toAdd),hd,?_⟩
  rw [ofAdd_sub,map_div,div_eq_mul_inv,naturalEmbedding_conjugation,commutatorElement_def]
  rfl

include s in
/-- The original intersection belongs to the relative centralizer. -/
theorem intersection_le_relativeCentralizer [Finite G] [CharP F 2] :
    A ⊓ B ≤ commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆ :=
  le_commutatorPreimage (inf_le_left.trans le_sup_left) (intersection_pointCore_commutator s)


include s in
/-- The original point parabolic preserves the relative centralizer. -/
theorem relativeCentralizer_normalized [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    (stabilizer (point F)).comap κ ≤
      normalizer (commutatorPreimage (A ⊔ B) (pointRadicalAmbient.comap κ) ⁅A,B⁆ : Set G) := by
  let : A.Normal := s.kernel ▸ inferInstance
  have hA : (stabilizer (point F)).comap κ ≤ normalizer (A : Set G) :=
    le_normalizer_of_normal
  have hB := s.opposite_normalized
  have hAB : (stabilizer (point F)).comap κ ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hA hg),
      mem_normalizer_iff_map_conj_eq.mp (hB hg)]
  apply commutatorPreimage_normalized
  · exact sup_le (normalizer_commutator_ge_left A B) (normalizer_commutator_ge_right A B)
  · exact (le_inf hA hB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  · have he : stabilizer (point F) = normalizer (pointRadicalAmbient (F := F) : Set (Sp F)) :=
      (pointRadicalAmbient_normalizer hF hn).symm
    rw [he]
    exact (pointRadicalAmbient (F := F)).le_normalizer_comap κ
  · exact hAB

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
