module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Field.Parameters
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Field.Matrices
public import GorensteinWalter.PGammaL2PureSemilinear
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Four field-involution conjugates generate odd PSL₂

Prime fields have no nontrivial coefficient automorphism. In the quadratic
case, the explicit root parameters and determinant-one matrices in the two
supporting modules prove generation for the pure field involution.

Projective semilinear Hilbert 90 conjugates every involution with nonidentity
field coordinate to this pure involution. This includes any putative mixed
diagonal--field case; no assumption is made on its projectively linear
coordinate. The normalizing conjugator may lie in PGL₂. Its actual action on
PSL₂ transports the four conjugators, so the resulting witnesses still lie in
PSL₂ and generate its literal canonical range in PΓL₂.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453. This discharges the
field model premise of `source_outer_four_conjugates_of_models`.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
open GorensteinWalter Subgroup Matrix
variable {F : Type*} [Field F] [Finite F]

private theorem transport_field_conjugates (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (s t : PGammaL2 F) (C : PGL2 F)
    (hC : (SemidirectProduct.inl C)⁻¹ * t * SemidirectProduct.inl C = s)
    (c : Fin 4 → PSL2 F)
    (hc : pGammaL2PSLRange F ≤ Subgroup.closure (Set.range fun i => FieldCalculation.pslInclusion (c i) * s * (FieldCalculation.pslInclusion (c i))⁻¹)) :
    ∃ d : Fin 4 → PSL2 F, pGammaL2PSLRange F ≤
      Subgroup.closure (Set.range fun i => FieldCalculation.pslInclusion (d i) * t * (FieldCalculation.pslInclusion (d i))⁻¹) := by
  let α := pgl2InnerAutPSL2 F hF hcard C
  let D : PGammaL2 F := SemidirectProduct.inl C
  have hα (x : PSL2 F) : FieldCalculation.pslInclusion (α x) = D * FieldCalculation.pslInclusion x * D⁻¹ := by
    change SemidirectProduct.inl (ProjectiveSpecialLinearGroup.toPGL (α x)) = _
    rw [toPGL_pgl2InnerAutPSL2_apply]
    simp only [map_mul, map_inv]
    rfl
  let H := Subgroup.closure (Set.range fun i => FieldCalculation.pslInclusion (α (c i)) * t * (FieldCalculation.pslInclusion (α (c i)))⁻¹)
  have ht : t = D * s * D⁻¹ := by
    change D⁻¹ * t * D = s at hC
    rw [← hC]
    group
  have hm : Subgroup.closure (Set.range fun i => FieldCalculation.pslInclusion (c i) * s * (FieldCalculation.pslInclusion (c i))⁻¹) ≤
      H.comap (MulAut.conj D).toMonoidHom := by
    apply (Subgroup.closure_le (K := H.comap (MulAut.conj D).toMonoidHom)).mpr
    rintro _ ⟨i, rfl⟩
    change D * (FieldCalculation.pslInclusion (c i) * s * (FieldCalculation.pslInclusion (c i))⁻¹) * D⁻¹ ∈ H
    have he : D * (FieldCalculation.pslInclusion (c i) * s * (FieldCalculation.pslInclusion (c i))⁻¹) * D⁻¹ =
        FieldCalculation.pslInclusion (α (c i)) * t * (FieldCalculation.pslInclusion (α (c i)))⁻¹ := by
      rw [hα, ht]
      group
    rw [he]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  refine ⟨fun i => α (c i), ?_⟩
  rintro x ⟨y, rfl⟩
  have hy : FieldCalculation.pslInclusion (α.symm y) ∈ pGammaL2PSLRange F := ⟨α.symm y, rfl⟩
  have hh := hm (hc hy)
  change D * FieldCalculation.pslInclusion (α.symm y) * D⁻¹ ∈ H at hh
  rw [← hα, α.apply_symm_apply] at hh
  exact hh

/-- Every involution with nontrivial field coordinate has four PSL₂ conjugates
whose generated subgroup contains the canonical PSL₂ range. -/
theorem fieldFourGeneration : FieldFourGeneration := by
  intro F _ _ p e hp ho he hcard hlarge t _hout ht hfield
  rcases he with rfl | rfl
  · exact False.elim (hfield (FiniteField.ringAut_eq_one_of_card_prime hp
      (by simpa only [pow_one] using hcard) t.right))
  · have hF : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, ho, by decide, hcard⟩
    have hs : t.right ^ 2 = 1 := by
      simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using congrArg
        (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) ht
    obtain ⟨a, z, hz, hspan⟩ := FieldCalculation.exists_root_span_parameters hp hcard hlarge t.right hs hfield
    obtain ⟨c, hc⟩ := FieldCalculation.generated_of_parameters t.right a (Units.mk0 z hz) hspan
    have htne : t ≠ 1 := by
      intro he
      exact hfield (congrArg SemidirectProduct.right he)
    obtain ⟨C, hC⟩ := projective_semilinear_involution_conj_inr hF t
      (orderOf_eq_prime ht htne) hfield
    exact transport_field_conjugates hF (by omega) _ t C hC c hc

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
