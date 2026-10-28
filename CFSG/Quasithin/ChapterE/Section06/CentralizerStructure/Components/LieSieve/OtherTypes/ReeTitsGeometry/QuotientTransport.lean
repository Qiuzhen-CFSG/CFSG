module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Passing invariant parabolics to the E.6.8 quotient

The component inclusion followed by the actual two-core quotient defines each
parabolic image. Generation and invariance pass through these homomorphisms.
Its full preimage adds precisely the two-core; when that core lies in Q,
adjoining Q recovers the embedded parabolic joined with Q. Thus relative
subnormality and characteristic two can be checked in the correct local group.
A normal subgroup of characteristic two retains that property after adjoining
a normalizing two-group, by the normal extension theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
variable {G : Type*} [Group G] {Q L : Subgroup G}

def parabolicImage (Q L : Subgroup G) (P : Subgroup L) :
    Subgroup (ComponentQuotient Q L) :=
  (P.map (inclusion (show L ≤ componentExtension Q L from le_sup_left))).map (quotientMap Q L)

theorem parabolicImage_le (P : Subgroup L) :
    parabolicImage Q L P ≤ componentImage Q L := by
  apply map_mono
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem parabolicImage_sup (P R : Subgroup L) :
    parabolicImage Q L (P ⊔ R) = parabolicImage Q L P ⊔ parabolicImage Q L R := by
  simp only [parabolicImage, Subgroup.map_sup]

theorem parabolicImage_top : parabolicImage Q L ⊤ = componentImage Q L := by
  unfold parabolicImage componentImage
  congr 1
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, mem_top _, Subtype.ext rfl⟩

/-- The core preimage adds exactly the controlled kernel, which disappears upon adjoining Q. -/
theorem preimage_join_eq (P : Subgroup L)
    (hcore : (componentExtension Q L).pCoreIn 2 ≤ Q) :
    quotientPreimage Q L (parabolicImage Q L P) ⊔ Q = P.map L.subtype ⊔ Q := by
  change (((P.map (inclusion (show L ≤ componentExtension Q L from le_sup_left))).map
    (quotientMap Q L)).comap (quotientMap Q L)).map (componentExtension Q L).subtype ⊔ Q = _
  rw [comap_map_eq, Subgroup.map_sup, map_map]
  have he : (componentExtension Q L).subtype.comp
      (inclusion (show L ≤ componentExtension Q L from le_sup_left)) = L.subtype := rfl
  rw [he]
  have hk : ((quotientMap Q L).ker).map (componentExtension Q L).subtype =
      (componentExtension Q L).pCoreIn 2 := by
    rw [quotientMap, QuotientGroup.ker_mk']
    rfl
  rw [hk, sup_assoc, sup_eq_right.mpr hcore]

theorem parabolicImage_invariant (P : Subgroup L)
    (hinv : componentNormalizer Q L ≤ normalizer (P.map L.subtype : Set G)) :
    sylowImage Q L ≤ normalizer (parabolicImage Q L P : Set (ComponentQuotient Q L)) := by
  rintro _ ⟨a, ha, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    have hm := (mem_normalizer_iff.mp (hinv ha) (p : G)).mp (mem_map_of_mem L.subtype hp)
    obtain ⟨p', hp', he⟩ := hm
    refine ⟨inclusion (show L ≤ componentExtension Q L from le_sup_left) p',
      mem_map_of_mem _ hp', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg (quotientMap Q L)
    exact Subtype.ext he
  · intro hx
    have hia : a⁻¹ ∈ (componentNormalizer Q L).subgroupOf (componentExtension Q L) :=
      ((componentNormalizer Q L).subgroupOf (componentExtension Q L)).inv_mem ha
    obtain ⟨y, ⟨p, hp, rfl⟩, hy⟩ := hx
    have hm := (mem_normalizer_iff.mp (hinv hia) (p : G)).mp (mem_map_of_mem L.subtype hp)
    obtain ⟨p', hp', he⟩ := hm
    refine ⟨inclusion (show L ≤ componentExtension Q L from le_sup_left) p',
      mem_map_of_mem _ hp', ?_⟩
    have hpi : inclusion (show L ≤ componentExtension Q L from le_sup_left) p' =
        a⁻¹ * inclusion (show L ≤ componentExtension Q L from le_sup_left) p * a :=
      Subtype.ext (by simpa using he)
    rw [hpi, map_mul, map_mul, map_inv, hy]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- A normalized local subgroup retains characteristic two after adjoining a two-group. -/
theorem join_characteristicTwo [Finite G] {P Q : Subgroup G}
    (hinv : Q ≤ normalizer (P : Set G)) (hQ : IsPGroup 2 Q)
    (hP : HasCharacteristicTwo P) : HasCharacteristicTwo ↥(P ⊔ Q) := by
  let N := P.subgroupOf (P ⊔ Q)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le P.le_normalizer hinv)
  apply centralizer_pCore_le_of_normal_pGroup_quotient N
  · exact (HasCharacteristicTwo.equiv (subgroupOfEquivOfLe le_sup_left)).mpr hP
  · apply isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf (P ⊔ Q)) hQ.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
