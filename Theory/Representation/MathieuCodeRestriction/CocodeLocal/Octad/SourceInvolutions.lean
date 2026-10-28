module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Unconditional native cocode involution ranks

The class representatives in the native cocode calculation are literally those
in the native Mathieu involution classification. The Sylow-central class has
fixed codimension four and pointwise centralizer equal to its cyclic subgroup;
the other class has codimension five. Restriction to the point stabilizer
excludes the fixed-point-free class, proving both conclusions for every M23
involution without an additional conjugacy assumption.

Source: Aschbacher--Smith H.14.4(3) and H.15.2(5), printed pp.397--399.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24ChapterHStabilizers
open Representation.BinaryOffender Theory.GroupTheory
namespace MathieuCode.CocodeOctad.Involutions

lemma sylowCentral_fixedCodim (x : M24) (hx : IsSylowCentralInvolution x) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers x) = 4 :=
  fixedCodim_of_isConj_z x (sylowCentral_class2A hx)

lemma noncentral_fixedCodim (x : M24) (hx : orderOf x = 2)
    (hn : ¬ IsSylowCentralInvolution x) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers x) = 5 :=
  fixedCodim_of_isConj_t x ((not_sylowCentral_iff_class2B x hx).mp hn)

lemma sylowCentral_pointwiseCentralizer (x : M24) (hx : IsSylowCentralInvolution x) :
    subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers x)) ⊤ = Subgroup.zpowers x :=
  pointwiseCentralizer_of_isConj_z x (sylowCentral_class2A hx)

lemma isConj_z_of_fixedPoint (x : M24) (hx : orderOf x = 2)
    (hf : ∃ i : Fin 24, x • i = i) : IsConj z x := by
  rcases M24InvolutionCentralizers.involution_classes x hx with h | h
  · exact h
  · obtain ⟨i, hi⟩ := hf
    have hm : i ∈ fixedPoints x := (mem_fixedPoints x i).mpr hi
    rw [class2B_fixed_empty h] at hm
    exact False.elim (Finset.notMem_empty _ hm)

lemma fixedPointFree_fixedCodim (x : M24) (hx : orderOf x = 2)
    (hf : ∀ i : Fin 24, x • i ≠ i) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers x) = 5 := by
  rcases M24InvolutionCentralizers.involution_classes x hx with h | h
  · have hc := m24Blocks_card _ (class2A_fixed_octad h)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (fixedPoints x).card by omega)
    exact False.elim (hf i ((mem_fixedPoints x i).mp hi))
  · exact fixedCodim_of_isConj_t x h

lemma m23_isConj_z (x : M23) (hx : orderOf x = 2) : IsConj z (pointEmbedding x) := by
  apply isConj_z_of_fixedPoint
  · rw [orderOf_injective pointEmbedding pointEmbedding_injective, hx]
  · refine ⟨0, ?_⟩
    have hm : pointEmbedding x ∈ pointEmbedding.range := ⟨x, rfl⟩
    rw [pointEmbedding_range] at hm
    exact hm

lemma m23_involution_fixedCodim (x : M23) (hx : orderOf x = 2) :
    fixedCodim m23CocodeRepresentation (Subgroup.zpowers x) = 4 :=
  m23_fixedCodim_of_isConj_z x (m23_isConj_z x hx)

lemma m23_involution_pointwiseCentralizer (x : M23) (hx : orderOf x = 2) :
    subspaceKernel m23CocodeRepresentation
      (fixedSpace m23CocodeRepresentation (Subgroup.zpowers x)) ⊤ = Subgroup.zpowers x :=
  m23_pointwiseCentralizer_of_isConj_z x (m23_isConj_z x hx)

end MathieuCode.CocodeOctad.Involutions
