module

public import Theory.Representation.SL3DoubledNaturalOffenders.Model
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Faithfulness and elementary projection bounds for doubled natural SL₃

The two tensor factors intersect trivially: an element in their intersection
is central in SL₃, whose scalar center is trivial in odd binary degree.
Sylow conjugacy and the concrete UT₃ root-plane theorem bound the natural
projection by q². The upper-transvection Sylow bounds the multiplicity
projection by q and supplies an actual special linear coordinate change.
All arguments include the field of order two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
These are the group-theoretic inputs to the tensor-subgroup estimate.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Representation.SL3DoubledNaturalOffenders
open BinaryOffender
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F]

private theorem tensor_eq_one_iff {m : ℕ} (hF : Nat.card F = 2^m) (hm : Odd m)
    (p : SL F × MultiplicitySL F) :
    (tensorRepresentation F).asGroupHom p = 1 ↔ p = 1 := by
  constructor
  · intro hp
    have he : (representation F).asGroupHom p.1 *
        (multiplicityRepresentation F).asGroupHom p.2 = 1 := by
      apply Units.ext
      have hv := congrArg Units.val hp
      change tensorRepresentation F p = 1 at hv
      exact hv
    have he' : (representation F).asGroupHom p.1 =
        (multiplicityRepresentation F).asGroupHom p.2⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left he
    have hg : p.1 ∈ Subgroup.center (SL F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply representation_injective F
      rw [map_mul, map_mul]
      have hc := multiplicity_commutes F p.2⁻¹.val g
      have he'' := congrArg Units.val he'
      change representation F p.1 = multiplicity F p.2⁻¹.val at he''
      rw [he'']
      exact hc.symm
    rw [Matrix.PSL3.OddDegreeProjectiveComparison.center_eq_bot hF hm] at hg
    have hg1 : p.1 = 1 := hg
    have hc1 : p.2 = 1 := by
      have hec : multiplicityRepresentation F p.2 = 1 := by
        have hh := congrArg Units.val he
        change representation F p.1 * multiplicityRepresentation F p.2 = 1 at hh
        simpa only [hg1, map_one, one_mul] using hh
      apply Subtype.ext
      apply multiplicity_injective F
      exact hec.trans (multiplicity_one F).symm
    exact Prod.ext hg1 hc1
  · rintro rfl
    exact map_one _

/-- The literal tensor homomorphism is faithful in odd binary degree. -/
theorem tensor_asGroupHom_injective {m : ℕ} (hF : Nat.card F = 2^m) (hm : Odd m) :
    Function.Injective (tensorRepresentation F).asGroupHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext p
  exact tensor_eq_one_iff hF hm p

/-- An elementary natural projection has order at most the order of a root plane. -/
theorem natural_elementary_card_le {m : ℕ} (hF : Nat.card F = 2^m) (hm : Odd m)
    (hpos : 0 < m) (A : Subgroup (SL F)) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ Nat.card F ^ 2 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let e := Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv hF hm
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  let eP := (Matrix.PSL3.LinearThree.unipotentEquiv F).trans
    ((Matrix.PSL3.LinearThree.unipotentSylow F hpos hF).equiv P)
  have hB : Nat.card B ≤ Nat.card F ^ 2 := by
    rcases Matrix.PSL3Even.UnipotentGeometry.marked_elementary_le_plane F
      (P : Subgroup PSL(3,F)) eP B hP with h | h
    · exact (Subgroup.card_le_of_le h).trans_eq
        (Matrix.PSL3Even.UnipotentGeometry.marked_card_plane₁ F _ eP)
    · exact (Subgroup.card_le_of_le h).trans_eq
        (Matrix.PSL3Even.UnipotentGeometry.marked_card_plane₂ F _ eP)
  change Nat.card (A.map e.toMonoidHom) ≤ _ at hB
  rwa [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hB

/-- A special linear change of multiplicity coordinates places the entire
elementary subgroup in the literal upper-transvection group. -/
theorem multiplicity_conjugate_upper (A : Subgroup (MultiplicitySL F))
    [IsElementaryAbelian 2 A] :
    ∃ c : MultiplicitySL F,
      A.map (MulAut.conj c).toMonoidHom ≤ SpecialLinearGroup.upperUnipotent F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (MultiplicitySL F) P
    (SpecialLinearGroup.upperUnipotentSylow F 2)
  refine ⟨c, ?_⟩
  have he : (P : Subgroup (MultiplicitySL F)).map (MulAut.conj c).toMonoidHom =
      SpecialLinearGroup.upperUnipotent F := congrArg Sylow.toSubgroup hc
  exact he ▸ Subgroup.map_mono hP

/-- The multiplicity projection has order at most the order of the field. -/
theorem multiplicity_elementary_card_le (A : Subgroup (MultiplicitySL F))
    [IsElementaryAbelian 2 A] : Nat.card A ≤ Nat.card F := by
  obtain ⟨c,hc⟩ := multiplicity_conjugate_upper A
  have h := Subgroup.card_le_of_le hc
  rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective,
    SpecialLinearGroup.card_upperUnipotent] at h

end Representation.SL3DoubledNaturalOffenders
