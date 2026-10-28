module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Centralizer

/-!
# Natural coordinates on the original point radical

The two noncentral matrix coordinates pull back along the original quotient
marking. Their kernel is the span of the two marked source factors, and
conjugation by a lift of a point-local matrix is its natural SL₂ action.
These are the radical coordinates in the relative-centralizer argument of
Meierfrankenfeld--Stellmacher (1993), (3.7), printed p.877.
-/

public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G] [CharP F 2]
variable (κ : G →* Sp F)

/-- The original point-core preimage maps to its two natural radical coordinates. -/
@[expose] def radicalCoordinates : (pointRadicalAmbient.comap κ) →*
    Multiplicative (Fin 2 → F) where
  toFun q := Multiplicative.ofAdd ![(κ q).val (.inl 1) (.inr 0),
    (κ q).val (.inr 1) (.inr 0)]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  map_mul' q r := by
    obtain ⟨q', hq', hq⟩ := q.property
    obtain ⟨r', hr', hr⟩ := r.property
    change Multiplicative.ofAdd ![(κ (q * r)).val (.inl 1) (.inr 0),
      (κ (q * r)).val (.inr 1) (.inr 0)] = _
    rw [map_mul, ← hq, ← hr]
    exact pointRadicalVector.map_mul ⟨q', hq'⟩ ⟨r', hr'⟩

@[simp] theorem radicalCoordinates_apply (q : pointRadicalAmbient.comap κ) :
    radicalCoordinates κ q = Multiplicative.ofAdd
      ![(κ q).val (.inl 1) (.inr 0), (κ q).val (.inr 1) (.inr 0)] := rfl

variable {κ} {A B : Subgroup G} (s : MarkedPair κ A B)

omit [CharP F 2] in
include s in
/-- The marked span is the preimage of the literal long-root subgroup. -/
theorem span_eq_root_preimage : A ⊔ B = (RootSubgroup.group (F := F) 0).comap κ := by
  rw [← s.root_image, comap_map_eq, s.kernel, sup_comm]

private theorem central_radical_eq_root (z : F) :
    (pointRadicalElement 0 0 z).val = rootElement 0 z := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, rootElement, rootMatrix, Matrix.single]

include s in
/-- The marked span belongs to the original point-core preimage. -/
theorem span_le_pointCore : A ⊔ B ≤ pointRadicalAmbient.comap κ := by
  rw [span_eq_root_preimage s]
  intro g hg
  obtain ⟨z, hz⟩ := (RootSubgroup.mem_group_iff 0 (κ g)).mp hg
  change κ g ∈ pointRadicalAmbient
  rw [← hz, ← central_radical_eq_root]
  exact mem_map_of_mem _ (pointRadicalElement_mem 0 0 z)

include s in
/-- The two-coordinate map is onto over the original group. -/
theorem radicalCoordinates_onto : Function.Surjective (radicalCoordinates κ) := by
  intro v
  obtain ⟨q, hq⟩ := pointRadicalVector_surjective v
  obtain ⟨g, hg⟩ := s.onto q.val.val
  have hgQ : g ∈ pointRadicalAmbient.comap κ := by
    change κ g ∈ pointRadicalAmbient
    rw [hg]
    exact mem_map_of_mem _ q.property
  refine ⟨⟨g, hgQ⟩, ?_⟩
  rw [radicalCoordinates_apply, hg]
  exact hq

include s in
/-- The coordinate kernel is precisely the original marked span. -/
theorem radicalCoordinates_kernel :
    (radicalCoordinates κ).ker = (A ⊔ B).subgroupOf (pointRadicalAmbient.comap κ) := by
  ext q
  change radicalCoordinates κ q = 1 ↔ (q : G) ∈ A ⊔ B
  rw [span_eq_root_preimage s]
  change radicalCoordinates κ q = 1 ↔ κ q ∈ RootSubgroup.group 0
  constructor
  · intro h
    have hu := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd 0) h
    have hv := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd 1) h
    change (κ q).val (.inl 1) (.inr 0) = 0 at hu
    change (κ q).val (.inr 1) (.inr 0) = 0 at hv
    obtain ⟨r, hr, he⟩ := q.property
    have hr' := pointRadical_eq_element r hr
    have hu' : r.val.val (.inl 1) (.inr 0) = 0 := by simpa only [← he, Subgroup.subtype_apply] using hu
    have hv' : r.val.val (.inr 1) (.inr 0) = 0 := by simpa only [← he, Subgroup.subtype_apply] using hv
    rw [hu', hv'] at hr'
    apply (RootSubgroup.mem_group_iff 0 (κ q)).mpr
    refine ⟨r.val.val (.inl 0) (.inr 0), ?_⟩
    rw [← central_radical_eq_root, ← hr']
    exact he
  · intro h
    obtain ⟨z, hz⟩ := (RootSubgroup.mem_group_iff 0 (κ q)).mp h
    rw [radicalCoordinates_apply, ← hz]
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp [rootElement, rootMatrix, Matrix.single]

/-- The actual point-local lift induces its natural quotient action on radical coordinates. -/
theorem radicalCoordinates_conjugation
    (g : G) (l : pointLocal (F := F)) (hg : κ g = l.val)
    (q q' : pointRadicalAmbient.comap κ) (hq' : (q' : G) = g * q * g⁻¹) :
    radicalCoordinates κ q' = Multiplicative.ofAdd
      ((pointQuotient l).val.mulVec (radicalCoordinates κ q).toAdd) := by
  obtain ⟨r, hr, he⟩ := q.property
  have he' : κ q' = l.val * r.val * l.val⁻¹ := by
    rw [hq', map_mul, map_mul, map_inv, hg, ← he]
    rfl
  have h := pointRadicalVector_conjugate l (⟨r, hr⟩ : pointRadical)
  change Multiplicative.ofAdd
      ![(l.val * r.val * l.val⁻¹).val (.inl 1) (.inr 0),
        (l.val * r.val * l.val⁻¹).val (.inr 1) (.inr 0)] =
    Multiplicative.ofAdd ((pointQuotient l).val.mulVec
      ![r.val.val (.inl 1) (.inr 0), r.val.val (.inr 1) (.inr 0)]) at h
  simpa only [radicalCoordinates_apply, he', ← he, Subgroup.subtype_apply, toAdd_ofAdd] using h

/-- Levi lifts act on the original radical section by the given SL₂ matrix. -/
theorem radicalCoordinates_levi_conjugation
    (g : G) (L : Matrix.SpecialLinearGroup (Fin 2) F) (hg : κ g = (pointLevi L).val)
    (q q' : pointRadicalAmbient.comap κ) (hq' : (q' : G) = g * q * g⁻¹) :
    radicalCoordinates κ q' = Multiplicative.ofAdd
      (L.val.mulVec (radicalCoordinates κ q).toAdd) := by
  simpa only [pointQuotient_pointLevi] using
    radicalCoordinates_conjugation g (pointLevi L) hg q q' hq'

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
