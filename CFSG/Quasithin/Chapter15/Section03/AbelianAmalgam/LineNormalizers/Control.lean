module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Basic
public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Sylow promotion and the elementary line span

Normalizer control promotes the chosen Sylow subgroup of `M_E` to one of
the original `G_E`. Once the span `V_E` is abelian, its conjugate generators
have exponent two, so it is elementary abelian. Its relative normality in
`G_E` then places it in `Q_E`. These are the Sylow and module steps used
before the temporary replacement in the proof of 15.3.67.

The normalizer bound and abelianness are explicit inputs. In the source,
the Thompson argument supplies the former and 15.3.50 supplies the latter
via the product proved in 15.3.66. None of the recognition conclusions of
15.3.67 is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

open Subgroup
variable {G : Type*} [Group G]

private theorem sylow_image_relIndex {p : ℕ} [Fact p.Prime] [Finite G]
    (L : Subgroup G) (P : Sylow p L) :
    ¬ p ∣ ((P : Subgroup L).map L.subtype).relIndex L := by
  change ¬ p ∣ (((P : Subgroup L).map L.subtype).comap L.subtype).index
  rw [comap_map_eq_self_of_injective L.subtype_injective]
  exact P.not_dvd_index

private theorem sylow_promotion {p : ℕ} [Fact p.Prime] [Finite G]
    (Q L C : Subgroup G) (hp : IsPGroup p Q) (hQC : Q ≤ C)
    (hlocal : ¬ p ∣ Q.relIndex L) (hN : normalizer (Q : Set G) ⊓ C ≤ L) :
    ∃ U : Sylow p C, (U : Subgroup C).map C.subtype = Q := by
  have hi := not_dvd_relIndex_of_normalizer_inf_le Q L C hp hQC hlocal hN
  exact ⟨(hp.comap_subtype (K := C)).toSylow hi, map_subgroupOf_eq_of_le hQC⟩

/-- The normalizer control from the Thompson argument promotes the chosen
`T_E` to an actual Sylow subgroup of the original `G_E`. It suffices that
`T` is a two-subgroup; the application takes the fixed Sylow subgroup. -/
theorem lineT_sylow_of_normalizer_control [Finite G]
    (T M E : Subgroup G) (hpT : IsPGroup 2 T)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E)
    (hN : normalizer (lineT T E : Set G) ≤ M) :
    ∃ U : Sylow 2 (lineNormalizer E),
      (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E := by
  have hlocal : ¬ 2 ∣ (lineT T E).relIndex (lineM M E) :=
    hP ▸ sylow_image_relIndex (lineM M E) P
  exact sylow_promotion (lineT T E) (lineM M E) (lineNormalizer E)
    (hpT.to_le (show lineT T E ≤ T from inf_le_left)) inf_le_right hlocal
    (le_inf (inf_le_left.trans hN) inf_le_right)

/-- The conjugate span is normal in the full normalizer, with relative
normality rather than normality in the ambient group. -/
theorem lineV_normal_in_lineNormalizer (V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) : ((lineV V E).subgroupOf (lineNormalizer E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (lineV_le_lineNormalizer V E hEV)).mpr
    (le_normalizer_conjugateSpanBy V (lineNormalizer E))

/-- Conjugate generators of the abelian line span still have exponent two. -/
theorem lineV_elementary_of_abelian (V E : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (lineV V E)] :
    IsElementaryAbelian 2 (lineV V E) := by
  let generators : Set G := {x | ∃ g ∈ lineNormalizer E, ∃ v ∈ V, g * v * g⁻¹ = x}
  let : IsMulCommutative (closure generators) := ‹IsMulCommutative (lineV V E)›
  apply IsElementaryAbelian.closure_of_isMulCommutative generators
  rintro x ⟨g, _, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

/-- The abelian span belongs to the two-core of the original line normalizer. -/
theorem lineV_le_lineQ_of_abelian (V E : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (lineV V E)]
    (hEV : E ≤ V) : lineV V E ≤ lineQ E := by
  let : IsElementaryAbelian 2 (lineV V E) := lineV_elementary_of_abelian V E
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (lineV V E))
    (lineV_le_lineNormalizer V E hEV) (le_normalizer_conjugateSpanBy V (lineNormalizer E))

/-- The quotient centralizer is normal in the temporary group.
Its identification with the temporary two-core is a separate obligation. -/
theorem lineQuotientCentralizer_normal_in_temporary (T V E : Subgroup G) :
    ((lineQuotientCentralizer T V E).subgroupOf
      (temporaryLineNormalizer T V E)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer ?_).mpr inf_le_right
  exact le_inf ((lineQuotientCentralizer_le_lineT T V E).trans inf_le_right) le_normalizer

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
