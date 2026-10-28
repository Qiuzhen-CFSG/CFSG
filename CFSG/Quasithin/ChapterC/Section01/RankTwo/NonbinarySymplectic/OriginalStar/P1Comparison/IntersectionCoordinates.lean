module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Centralizer

/-!
# Coordinates on the original hyperplane modulo its critical point

The two middle natural coordinates are a surjective homomorphism on the
actual intersection A∩B. Their kernel is exactly the original commutator
[A,B]. They transform as the natural two-space under the literal point Levi,
and the point radical fixes them. These retain the whole-core natural marking
used by the relative centralizer in MS93 (3.7), printed p.877.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

@[expose] def middleProjection : Vector F →ₗ[F] (Fin 2 → F) :=
  LinearMap.pi (fun i => LinearMap.proj (middleIndex i))

@[expose] def intersectionMiddle : (A ⊓ B : Subgroup G) →* Multiplicative (Fin 2 → F) :=
  middleProjection.toAddMonoidHom.toMultiplicative.comp
    (s.natural.toMonoidHom.comp (Subgroup.inclusion inf_le_left))

theorem naturalEmbedding_injective : Function.Injective (naturalEmbedding s) :=
  Subtype.val_injective.comp s.natural.symm.injective

theorem naturalEmbedding_mem_critical_iff (v : Vector F) :
    naturalEmbedding s (Multiplicative.ofAdd v) ∈ ⁅A,B⁆ ↔ v ∈ point F := by
  rw [critical_commutator_image s]
  exact mem_map_iff_mem (naturalEmbedding_injective s)

theorem intersectionMiddle_onto [Finite G] : Function.Surjective (intersectionMiddle s) := by
  intro v
  let w : Vector F := Sum.elim ![0,v.toAdd 0] ![0,v.toAdd 1]
  have hw : naturalEmbedding s (Multiplicative.ofAdd w) ∈ A ⊓ B :=
    (intersection_coordinate s w).mpr rfl
  refine ⟨⟨naturalEmbedding s (Multiplicative.ofAdd w),hw⟩,?_⟩
  change Multiplicative.ofAdd (middleProjection
    (s.natural (s.natural.symm (Multiplicative.ofAdd w))).toAdd)=v
  rw [s.natural.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

theorem intersectionMiddle_kernel [Finite G] :
    (intersectionMiddle s).ker=⁅A,B⁆.subgroupOf (A ⊓ B) := by
  ext x
  let v := (s.natural ⟨x.val,x.property.1⟩).toAdd
  have he : naturalEmbedding s (Multiplicative.ofAdd v)=x.val :=
    congrArg Subtype.val (s.natural.symm_apply_apply ⟨x.val,x.property.1⟩)
  have hv : coordinate v=0 := (intersection_coordinate s v).mp (he.symm ▸ x.property)
  change intersectionMiddle s x=1 ↔ x.val ∈ ⁅A,B⁆
  rw [←he,naturalEmbedding_mem_critical_iff s]
  change Multiplicative.ofAdd (middleProjection v)=1 ↔ v ∈ point F
  rw [mem_point_iff]
  constructor
  · intro h
    have h0 := congrArg (fun v : Multiplicative (Fin 2→F) => v.toAdd 0) h
    have h1 := congrArg (fun v : Multiplicative (Fin 2→F) => v.toAdd 1) h
    refine ⟨h0,?_⟩
    intro i
    fin_cases i
    · exact hv
    · exact h1
  · rintro ⟨h0,h1⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h0
    · exact h1 1


private theorem middleProjection_levi [CharP F 2]
    (l : Matrix.SpecialLinearGroup (Fin 2) F) (v : Vector F) :
    middleProjection ((pointLevi l).val • v)=l.val.mulVec (middleProjection v) := by
  funext i
  fin_cases i <;>
    simp [middleProjection,middleIndex,pointLevi,pointLeviMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two]

theorem intersectionMiddle_levi_conjugation [CharP F 2]
    (l : Matrix.SpecialLinearGroup (Fin 2) F) (g : G) (hg : κ g=(pointLevi l).val)
    (x y : (A ⊓ B : Subgroup G)) (hy : (y : G)=g*x*g⁻¹) :
    (intersectionMiddle s y).toAdd=l.val.mulVec (intersectionMiddle s x).toAdd := by
  change middleProjection (s.natural ⟨y.val,y.property.1⟩).toAdd =
    l.val.mulVec (middleProjection (s.natural ⟨x.val,x.property.1⟩).toAdd)
  rw [s.natural_conjugation g ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩ hy,hg,middleProjection_levi]

theorem intersection_natural_coordinate [Finite G] (x : (A ⊓ B : Subgroup G)) :
    coordinate (s.natural ⟨x.val,x.property.1⟩).toAdd=0 := by
  apply (intersection_coordinate s _).mp
  change (s.natural.symm (s.natural ⟨x.val,x.property.1⟩)).val ∈ A ⊓ B
  rw [s.natural.symm_apply_apply]
  exact x.property

private theorem middleProjection_radical [CharP F 2]
    (g : Sp F) (hg : g ∈ pointRadicalAmbient) (v : Vector F)
    (hv : coordinate v=0) : middleProjection (g • v)=middleProjection v := by
  obtain ⟨g,hg,rfl⟩ := hg
  rw [pointRadical_eq_element g hg]
  have hv' : v (.inr 0)=0 := hv
  funext i
  fin_cases i <;>
    simp [middleProjection,middleIndex,pointRadicalElement,pointRadicalMatrix,
      Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,hv']

theorem intersectionMiddle_radical_conjugation [Finite G] [CharP F 2]
    (g : G) (hg : κ g ∈ pointRadicalAmbient)
    (x y : (A ⊓ B : Subgroup G)) (hy : (y : G)=g*x*g⁻¹) :
    intersectionMiddle s y=intersectionMiddle s x := by
  apply Multiplicative.toAdd.injective
  change middleProjection (s.natural ⟨y.val,y.property.1⟩).toAdd =
    middleProjection (s.natural ⟨x.val,x.property.1⟩).toAdd
  rw [s.natural_conjugation g ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩ hy]
  exact middleProjection_radical _ hg _ (intersection_natural_coordinate s x)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
