module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.OrthogonalAction
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion.Coordinates
public import Theory.SpecificGroups.SymmetricFourWreath.OrthogonalB.Actors

/-!
# Axis fusion in the contrary case of 13.9.5

The faithful full orthogonal action on the original four-group square makes its
six nonsingular vectors conjugate. The literal wreath involution classes then
identify precisely the involutions supported on one dihedral factor.
Source: Aschbacher--Smith, The Classification of Quasithin Groups, 13.9.5, printed pp.970--971.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

theorem isConj_of_B_nonsingular
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (x y:m.B) (hx:BinaryFourPlus.q (m.BLinearCoordinates (Additive.ofMul x))=1)
    (hy:BinaryFourPlus.q (m.BLinearCoordinates (Additive.ofMul y))=1) : IsConj (x:G) (y:G) := by
  obtain ⟨a,ha⟩ := OrthogonalB.nonsingular_transitive _ _ hx hy
  obtain ⟨g,hg⟩ := m.normalizerIsometryAction_surjective hG hC a
  have he : m.B.normalizerMonoidHom g x=y := by
    apply Additive.ofMul.injective
    apply m.BLinearCoordinates.injective
    rw [←m.normalizerLinearAction_apply]
    change (m.normalizerIsometryAction hG hC g).val _=_
    rw [hg]
    exact ha
  exact isConj_iff.mpr ⟨g,congrArg Subtype.val he⟩

theorem t_fuses_axis_representatives_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (i:Fin 6) (hi:i=1 ∨ i=2) : IsConj m.t (m.embedding (representative i)) := by
  let a:SymmetricFourWreath.B:=⟨representative 1,representative_mem_B 1 (by decide)⟩
  let b:SymmetricFourWreath.B:=⟨representative i,representative_mem_B i (by rcases hi with rfl|rfl <;> decide)⟩
  have ha : BinaryFourPlus.q (OrthogonalB.linearCoordinates (Additive.ofMul a))=1 :=
    (OrthogonalB.nonsingular_iff a).mpr (Or.inl (IsConj.refl _))
  have hb : BinaryFourPlus.q (OrthogonalB.linearCoordinates (Additive.ofMul b))=1 := by
    apply (OrthogonalB.nonsingular_iff b).mpr
    rcases hi with rfl|rfl
    · exact Or.inl (IsConj.refl _)
    · exact Or.inr (IsConj.refl _)
  exact m.isConj_of_B_nonsingular hG hC (m.BModelEquiv a) (m.BModelEquiv b)
    (m.BLinearCoordinates_image a ▸ ha) (m.BLinearCoordinates_image b ▸ hb)

theorem axis_fusion_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (x:G) (hx:x∈m.dihedralBase) (ho:orderOf x=2) :
    IsConj m.t x ↔ x∈m.factorSylow 1 ∨ x∈m.factorSylow turn := by
  rw [←m.range_baseProductEmbedding] at hx
  obtain ⟨⟨a,b⟩,rfl⟩ := hx
  let w:=sylowEmbedding (pair (a,b))
  have hw : orderOf w=2 := (orderOf_injective m.embedding m.embedding_injective w).symm.trans ho
  have hc : IsConj (m.embedding (representative (classIndex w))) (m.baseProductEmbedding (a,b)) :=
    m.embedding.map_isConj ((isConj_representative_iff _ _).mpr ⟨hw,rfl⟩)
  rw [m.baseProductEmbedding_mem_first,m.baseProductEmbedding_mem_second,or_comm]
  constructor
  · intro ht
    by_contra hab
    have hclass : ¬(classIndex w=1 ∨ classIndex w=2) := by
      intro hh
      exact hab ((OrthogonalB.base_class_axes a b).mp hh)
    have hnot5 : classIndex w≠5 := by
      intro h5
      exact OrthogonalB.base_class_not_swap a b h5
    have hclass' : classIndex w=0 ∨ classIndex w=3 ∨ classIndex w=4 :=
      (by decide : ∀i:Fin 6,¬(i=1 ∨ i=2)→i≠5→i=0 ∨ i=3 ∨ i=4)
        (classIndex w) hclass hnot5
    have hz : IsConj m.z (m.baseProductEmbedding (a,b)) := by
      apply (m.conjugate_z_local_classes_iff_of_centralizer_eq hG hC _
        (m.image_le_local _ (mem_map_of_mem m.embedding
          (show w∈J from mem_map_of_mem sylowEmbedding ⟨(a,b),rfl⟩)))).mpr
      have hm := (m.embedding_mem_localInvolutionClass (classIndex w) w).mpr
        ((isConj_representative_iff _ _).mpr ⟨hw,rfl⟩)
      rcases hclass' with he|he|he
      · exact Or.inl (he ▸ hm)
      · exact Or.inr (Or.inl (he ▸ hm))
      · exact Or.inr (Or.inr (he ▸ hm))
    exact m.not_isConj_t_z (ht.trans hz.symm)
  · intro hab
    have hclass : classIndex w=1 ∨ classIndex w=2 := (OrthogonalB.base_class_axes a b).mpr hab
    exact (m.t_fuses_axis_representatives_of_centralizer_eq hG hC (classIndex w) hclass).trans hc

/-- Under the contrary centralizer equality, every base involution lies in one
of the two original marked ambient classes. -/
theorem dihedral_involution_two_classes
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (x:G) (hx:x∈m.dihedralBase) (ho:orderOf x=2) :
    IsConj m.t x ∨ IsConj m.z x := by
  rw [←m.range_baseProductEmbedding] at hx
  obtain ⟨⟨a,b⟩,rfl⟩ := hx
  let w:=sylowEmbedding (pair (a,b))
  have hw : orderOf w=2 := (orderOf_injective m.embedding m.embedding_injective w).symm.trans ho
  have hc : IsConj (m.embedding (representative (classIndex w))) (m.baseProductEmbedding (a,b)) :=
    m.embedding.map_isConj ((isConj_representative_iff _ _).mpr ⟨hw,rfl⟩)
  by_cases hi:classIndex w=1 ∨ classIndex w=2
  · exact Or.inl ((m.t_fuses_axis_representatives_of_centralizer_eq hG hC _ hi).trans hc)
  · right
    have hclass : classIndex w=0 ∨ classIndex w=3 ∨ classIndex w=4 :=
      (by decide : ∀i:Fin 6,¬(i=1 ∨ i=2)→i≠5→i=0 ∨ i=3 ∨ i=4)
        (classIndex w) hi (OrthogonalB.base_class_not_swap a b)
    apply (m.conjugate_z_local_classes_iff_of_centralizer_eq hG hC _
      (m.image_le_local _ (mem_map_of_mem m.embedding
        (show w∈J from mem_map_of_mem sylowEmbedding ⟨(a,b),rfl⟩)))).mpr
    have hm := (m.embedding_mem_localInvolutionClass (classIndex w) w).mpr
      ((isConj_representative_iff _ _).mpr ⟨hw,rfl⟩)
    rcases hclass with he|he|he
    · exact Or.inl (he ▸ hm)
    · exact Or.inr (Or.inl (he ▸ hm))
    · exact Or.inr (Or.inr (he ▸ hm))

end CFSG.Quasithin.Chapter13.Section09.Marking
