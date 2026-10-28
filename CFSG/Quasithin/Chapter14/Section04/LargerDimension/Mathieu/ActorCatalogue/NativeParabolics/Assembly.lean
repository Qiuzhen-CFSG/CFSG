module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Transport
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.GeneratedHexad
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.PartitionOverlap

/-!
# Native residual parabolics in the Mathieu case

The complete rank-one catalogue puts the supplied point-centralizing Borel
and the remaining parabolic in common pair--hexad and partition coordinates.
Adjoining S recovers these overgroups from their residuals. Their design images
generate the full hexad stabilizer, and cubic survival makes their native join
the full inverse image, retaining the triple cover after dividing by O₂.

An actual lift of the common design conjugator identifies A₁ ∨ A₂ ∨ S with
the conjugated partition preimage. The two marked three-point actions therefore
give an actual S₃ × S₃ quotient, with an explicit formula on representatives.
`exists_native_parabolics` applies all of these constructions to the prescribed
Borel without any extra catalogue, geometric-position, or quotient premise.

Source: Aschbacher--Smith 14.4.12, printed pp.1011--1012; case 14.4.2(6),
printed p.1006; H.12.1, printed pp.393--394. The parent actor-catalogue task
retains transport to H and the independent module geometry proving Y={X₁,X₂}.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics

lemma conjugate_hexad_mem (g : m22DesignAut) : g • m22Hexad123 ∈ m22Blocks := by
  have h : g.val • (m22Blocks : Set (Finset (Fin 22))) = m22Blocks :=
    (Theory.GroupTheory.SteinerSystem.mem_aut_iff _ _).mp g.property
  have hm : g.val • m22Hexad123 ∈ g.val • (m22Blocks : Set (Finset (Fin 22))) :=
    Set.smul_mem_smul_set m22Hexad123_mem
  rw [h] at hm
  exact hm

lemma partition_sup_pair (g : m22DesignAut) :
    Catalogue.partitionAt g ⊔ Catalogue.pairAt g =
      MulAction.stabilizer m22DesignAut (g • m22Hexad123) := by
  rw [Catalogue.partitionAt, Catalogue.pairAt, ← Subgroup.map_sup,
    sup_comm M22ValueBound.Concrete.outerSecond, outerPairHexad_sup_outerSecond,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]

lemma generated_eq_hexadPreimage (S : Sylow 2 Model) (P B : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (hSB : (S : Subgroup Model) ≤ B)
    (g : m22DesignAut) (hP : P.map designProjection = Catalogue.partitionAt g)
    (hB : B.map designProjection = Catalogue.pairAt g) :
    (S : Subgroup Model) ⊔ twoResidual P ⊔ twoResidual B =
      hexadPreimage (g • m22Hexad123) := by
  have hj : (S : Subgroup Model) ⊔ twoResidual P ⊔ twoResidual B = P ⊔ B := by
    calc
      (S : Subgroup Model) ⊔ twoResidual P ⊔ twoResidual B = P ⊔ twoResidual B := by
        rw [sup_comm (S : Subgroup Model), residual_sup_sylow S P hSP]
      _ = (P ⊔ twoResidual B) ⊔ (S : Subgroup Model) :=
        (sup_eq_left.mpr (hSP.trans le_sup_left)).symm
      _ = P ⊔ (twoResidual B ⊔ (S : Subgroup Model)) := sup_assoc _ _ _
      _ = P ⊔ B := congrArg (P ⊔ ·) (residual_sup_sylow S B hSB)
  rw [hj]
  apply eq_hexadPreimage_of_design_image (conjugate_hexad_mem g)
  · exact sup_le (map_le_iff_le_comap.mp (hP ▸ Catalogue.partitionAt_le_hexad g))
      (map_le_iff_le_comap.mp (hB ▸ Catalogue.pairAt_le_hexad g))
  · rw [Subgroup.map_sup, hP, hB, partition_sup_pair]

private lemma index_three_minimal (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (hi : (S : Subgroup Model).relIndex P = 3) :
    (S : Subgroup Model) ⋖ P := by
  have hlt : (S : Subgroup Model) < P := lt_of_le_of_ne hSP (by
    intro he
    rw [← he, relIndex_self] at hi
    omega)
  refine ⟨hlt, ?_⟩
  intro Q hSQ hQP
  have hm := relIndex_mul_relIndex (S : Subgroup Model) Q P hSQ.le hQP.le
  rw [hi] at hm
  rcases Nat.prime_three.eq_one_or_self_of_dvd ((S : Subgroup Model).relIndex Q)
    ⟨Q.relIndex P, hm.symm⟩ with h | h
  · exact hSQ.not_ge (relIndex_eq_one.mp h)
  · have hQP' : Q.relIndex P = 1 := by rw [h] at hm; omega
    exact hQP.not_ge (relIndex_eq_one.mp hQP')

/-- The overlap is a literal full inverse image; its cubic layer is not discarded. -/
theorem overlap_eq_partition_preimage (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (g : m22DesignAut)
    (hP : P.map designProjection = Catalogue.partitionAt g) :
    twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) =
      (Catalogue.partitionAt g).comap designProjection := by
  rw [firstActor_eq_cubic, sup_assoc, residual_sup_sylow S P hSP,
    cubic_sup_eq_full_preimage, hP]

/-- Cubic survival puts the first actor inside the subgroup generated by
the other two actors and S. -/
theorem firstActor_le_generated (S : Sylow 2 Model) (P B : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (hSB : (S : Subgroup Model) ≤ B)
    (g : m22DesignAut) (hP : P.map designProjection = Catalogue.partitionAt g)
    (hB : B.map designProjection = Catalogue.pairAt g) :
    twoResidual (pCore 3 Model) ≤ (S : Subgroup Model) ⊔ twoResidual P ⊔ twoResidual B := by
  rw [firstActor_eq_cubic, generated_eq_hexadPreimage S P B hSP hSB g hP hB]
  exact cubic_le_preimage _

/-- The literal overlap is a subgroup of the identified hexad parabolic. -/
theorem overlap_le_generated (S : Sylow 2 Model) (P B : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (hSB : (S : Subgroup Model) ≤ B)
    (g : m22DesignAut) (hP : P.map designProjection = Catalogue.partitionAt g)
    (hB : B.map designProjection = Catalogue.pairAt g) :
    twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) ≤
      (S : Subgroup Model) ⊔ twoResidual P ⊔ twoResidual B := by
  rw [overlap_eq_partition_preimage S P hSP g hP,
    generated_eq_hexadPreimage S P B hSP hSB g hP hB]
  exact comap_mono (Catalogue.partitionAt_le_hexad g)

/-- An actual native lift of the common design coordinates marks the overlap. -/
theorem overlap_eq_partition_conjugate (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (x : Model)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x)) :
    twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) =
      partitionPreimage.map (MulAut.conj x).toMonoidHom := by
  rw [overlap_eq_partition_preimage S P hSP (designProjection x) hP,
    Catalogue.partitionAt, PartitionOverlap.conjugate_preimage_eq]

/-- Conjugation by the chosen native lift identifies the literal overlap
with the marked partition preimage. -/
noncomputable def overlapToPartition (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (x : Model)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x)) :
    (twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) : Subgroup Model) ≃*
      partitionPreimage :=
  (MulEquiv.subgroupCongr (overlap_eq_partition_conjugate S P hSP x hP)).trans
    (partitionPreimage.equivMapOfInjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).symm

theorem overlapToPartition_apply (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (x : Model)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x))
    (y : (twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) : Subgroup Model)) :
    (overlapToPartition S P hSP x hP y).val = x⁻¹ * y.val * x := by
  let e := partitionPreimage.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective
  have he := congrArg Subtype.val (e.apply_symm_apply
    (MulEquiv.subgroupCongr (overlap_eq_partition_conjugate S P hSP x hP) y))
  apply (MulAut.conj x).injective
  calc
    MulAut.conj x (overlapToPartition S P hSP x hP y).val = y.val := he
    _ = MulAut.conj x (x⁻¹ * y.val * x) := by simp [MulAut.conj_apply, mul_assoc]

/-- The product quotient on exactly A₁ ∨ A₂ ∨ S, in the original native carrier. -/
noncomputable def overlapQuotientEquiv (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (x : Model)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x)) :
    coreQuotient (twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.congr
    (pCore 2 (twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) : Subgroup Model))
    (pCore 2 partitionPreimage) (overlapToPartition S P hSP x hP)
    (pCore_map_iso 2 (overlapToPartition S P hSP x hP))).trans PartitionOverlap.quotientEquiv

/-- Both factors retain the published cubic-coset and three-pair actions. -/
theorem overlapQuotientEquiv_mk (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (x : Model)
    (hP : P.map designProjection = Catalogue.partitionAt (designProjection x))
    (y : (twoResidual (pCore 3 Model) ⊔ twoResidual P ⊔ (S : Subgroup Model) : Subgroup Model)) :
    overlapQuotientEquiv S P hSP x hP (QuotientGroup.mk' _ y) =
      (PartitionOverlap.cubicMap (overlapToPartition S P hSP x hP y),
       PartitionOverlap.pairMap (overlapToPartition S P hSP x hP y)) := rfl

/-- Native group-theoretic calculation in 14.4.12 from the prescribed Borel.
All three residual actors, their common hexad, its retained nonsplit triple
cover, and the actual overlap quotient are constructed. The only inputs are
the nonzero binary point and the Borel containments and relative index.
The parent source assembly supplies this Borel and transports the result to H;
the independent module calculation identifies which moving actors lie in Y. -/
theorem exists_native_parabolics (S : Sylow 2 Model) {v : Space} (hv : v ≠ 0)
    (B : Subgroup Model) (hSB : (S : Subgroup Model) ≤ B)
    (hB : B ≤ pointCentralizer v) (hiB : (S : Subgroup Model).relIndex B = 3) :
    ∃ (P₂ : Subgroup Model) (x : Model),
      (S : Subgroup Model) ≤ P₂ ∧ (S : Subgroup Model).relIndex P₂ = 3 ∧
      (S : Subgroup Model) ⋖ P₂ ∧ Disjoint cubic P₂ ∧
      P₂.map designProjection = Catalogue.partitionAt (designProjection x) ∧
      B.map designProjection = Catalogue.pairAt (designProjection x) ∧
      ThreeExtension ⊤ (S : Subgroup Model) (twoResidual (pCore 3 Model)) ∧
      ThreeExtension ⊤ (S : Subgroup Model) (twoResidual P₂) ∧
      ThreeExtension ⊤ (S : Subgroup Model) (twoResidual B) ∧
      ¬ twoResidual P₂ ≤ pointCentralizer v ∧
      twoResidual B ≤ pointCentralizer v ∧
      twoResidual (pCore 3 Model) ≠ twoResidual P₂ ∧
      twoResidual (pCore 3 Model) ≠ twoResidual B ∧ twoResidual P₂ ≠ twoResidual B ∧
      XFamily ⊤ (S : Subgroup Model) =
        {twoResidual (pCore 3 Model), twoResidual P₂, twoResidual B} ∧
      ∃ hD : (S : Subgroup Model) ⊔ twoResidual P₂ ⊔ twoResidual B =
          hexadPreimage (designProjection x • m22Hexad123),
        IsElementaryAbelian 2 (pCore 2 ((S : Subgroup Model) ⊔ twoResidual P₂ ⊔ twoResidual B : Subgroup Model)) ∧
        Nat.card (pCore 2 ((S : Subgroup Model) ⊔ twoResidual P₂ ⊔ twoResidual B : Subgroup Model)) = 16 ∧
        Function.Surjective (GeneratedHexad.quotientProjection
          (conjugate_hexad_mem (designProjection x)) hD) ∧
        Nat.card (GeneratedHexad.quotientProjection
          (conjugate_hexad_mem (designProjection x)) hD).ker = 3 ∧
        IsQuasisimple (GeneratedHexad.evenSubgroup
          (conjugate_hexad_mem (designProjection x)) hD) ∧
        (∃ e : GeneratedHexad.evenSubgroup (conjugate_hexad_mem (designProjection x)) hD ≃*
            Atlas.Codes.HexEvenAutomorphisms,
          Atlas.Codes.hexEvenCoordinate.comp e.toMonoidHom =
            GeneratedHexad.evenProjection (conjugate_hexad_mem (designProjection x)) hD) ∧
        (¬ ∃ s : alternatingGroup (Fin 6) →*
            GeneratedHexad.evenSubgroup (conjugate_hexad_mem (designProjection x)) hD,
          (GeneratedHexad.evenProjection (conjugate_hexad_mem (designProjection x)) hD).comp s =
            MonoidHom.id _) ∧
        Nonempty (coreQuotient (twoResidual (pCore 3 Model) ⊔ twoResidual P₂ ⊔
          (S : Subgroup Model)) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨P₂, g, hP, hd, hmP, hmB, _, _, heP, hmove, hn₁₂, hn₁₃, hn₂₃, hfamily⟩ :=
    Catalogue.exists_catalogue S hv B hSB hB hiB
  obtain ⟨x, rfl⟩ := designProjection_surjective g
  have hD := generated_eq_hexadPreimage S P₂ B hP.1 hSB (designProjection x) hmP hmB
  have hb := conjugate_hexad_mem (designProjection x)
  exact ⟨P₂, x, hP.1, hP.2, index_three_minimal S P₂ hP.1 hP.2, hd, hmP, hmB,
    firstActor_threeExtension S, heP, residual_threeExtension_of_index_three S B hSB hiB,
    hmove, borelResidual_le_pointCentralizer B hB, hn₁₂, hn₁₃, hn₂₃, hfamily, hD,
    GeneratedHexad.twoCore_elementary hb hD, GeneratedHexad.twoCore_card hb hD,
    GeneratedHexad.quotientProjection_surjective hb hD,
    GeneratedHexad.quotientProjection_kernel_card hb hD,
    GeneratedHexad.evenSubgroup_isQuasisimple hb hD,
    GeneratedHexad.exists_hexacode_equiv hb hD,
    GeneratedHexad.evenProjection_nonsplit hb hD,
    ⟨overlapQuotientEquiv S P₂ hP.1 x hmP⟩⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
