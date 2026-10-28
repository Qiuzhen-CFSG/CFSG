module
public import Theory.GroupTheory.TwoPerfectCubicNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNormalized

/-!
# The actual Borel normalizer when L₁ is outside a component

For an actual local I and its normal C-component C, suppose L₁ is not
contained in C. The original point group is two-perfect with cubic
O₂-quotient. The quotient by C therefore has two-group kernel on L₁T,
so L₁T preserves its Sylow intersection with C and the intrinsic Sylow
normalizer B₀. This B₀ is solvable, and 14.7.29 places it in N_G(L).
Both B₀ and B = O²(B₀) normalize the original L₁.

The same-G,T theorem uses only Structural1222At and relative normality.
The final original-component application discharges normality using the
existing 14.7.32 theorem and uses the existing 14.7.29 producer. Their
preserved universal earlier-input APIs are specialized only in the forward
direction. No universal premise is constructed from a guarded local one.

We also identify B₀ with the full preimage of the actual Sylow normalizer
in C/O₂(C), through the original component inclusion. This is the Borel
subgroup in the larger-field rows. Its model identification, the equality
B_C = B and the remaining 14.7.41 alternatives are further source steps.

Source: Aschbacher–Smith, opening of 14.7.40 and the outside-component
branch of 14.7.41, printed p.1061, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intrinsic normalizer in C of its original Sylow intersection,
embedded in the original ambient group. -/
@[expose] def componentSylowNormalizer (T : Sylow 2 G) (I : Subgroup G)
    (C : Subgroup I) : Subgroup G :=
  (C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I)).map I.subtype

/-- The literal quotient Borel preimage, with its actual Sylow subgroup. -/
theorem componentSylowNormalizer_quotient (I : Subgroup G)
    (hTI : (T : Subgroup G) ≤ I) (C : Subgroup I) [C.Normal] :
    ∃ P : Sylow 2 C,
      (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C ∧
      componentSylowNormalizer T I C =
        ((normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Set (C ⧸ pCore 2 C))).comap (QuotientGroup.mk' (pCore 2 C))).map
            (I.subtype.comp C.subtype) := by
  let S := T.subtype hTI
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  refine ⟨P,hP,?_⟩
  have hpre : (normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
      Set (C ⧸ pCore 2 C))).comap (QuotientGroup.mk' (pCore 2 C)) =
      normalizer (P : Set C) := by
    change (normalizer (↑((P : Subgroup C).map (QuotientGroup.mk' (pCore 2 C))) :
      Set (C ⧸ pCore 2 C))).comap _ = _
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal P)]
    rfl
  have he : (normalizer (P : Set C)).map C.subtype =
      C ⊓ normalizer ((S : Subgroup I) ⊓ C : Set I) := by
    change (normalizer (↑(P : Subgroup C) : Set C)).map C.subtype =
      C ⊓ normalizer (↑((S : Subgroup I) ⊓ C) : Set I)
    have hi : ((S : Subgroup I) ⊓ C).subgroupOf C = (S : Subgroup I).subgroupOf C := by
      ext x
      exact and_iff_left x.property
    rw [hP, ←hi, ←subgroupOf_normalizer_eq (show (S : Subgroup I) ⊓ C ≤ C from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
  rw [hpre, ←map_map, he]
  rfl

/-- The outside-component branch constructs a solvable L₁T-invariant
Sylow normalizer using only the structural theorem at the same G,T. -/
theorem normal_component_sylow_normalizer_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (componentSylowNormalizer T I C : Set G) ∧
      Group.IsSolvable (componentSylowNormalizer T I C) := by
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  let B := C ⊓ normalizer ((S : Subgroup I) ⊓ C : Set I)
  have hAI := F.Li_one_le_of_mem_Hz hI
  let e := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hn : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (T_normalizes_L₁_at h structural hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hh' := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hh'
  have hnorm := cubic_supplement_normalizes_sylow_normalizer A C S hp hc hn hnot
  have hnorm' := (map_mono (f := I.subtype) hnorm).trans (B.le_normalizer_map I.subtype)
  have hmap : (A ⊔ (S : Subgroup I)).map I.subtype = F.Li L 1 ⊔ (T : Subgroup G) := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAI, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
  rw [hmap] at hnorm'
  refine ⟨hnorm', ?_⟩
  let : Group.IsSolvable B := normal_sylow_normalizer_solvable C S
  exact Group.isSolvable_of_surjective (f := I.subtype.subgroupMap B)
    (I.subtype.subgroupMap_surjective B)

/-- Apply the construction to every actual original component. Source
14.7.32 discharges relative normality; 14.7.29 places the resulting Borel
and its residual in the original normalizer. -/
theorem local_component_borel_of_not_contains_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    let B₀ := componentSylowNormalizer T I C
    let B := (pResidual 2 B₀).map B₀.subtype
    B₀ ≤ C.map I.subtype ∧ Group.IsSolvable B₀ ∧
      F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) ∧
      B₀ ≤ normalizer (L : Set G) ∧ B₀ ≤ normalizer (F.Li L 1 : Set G) ∧
      F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      B ≤ normalizer (L : Set G) ∧ B ≤ normalizer (F.Li L 1 : Set G) ∧
      ∃ P : Sylow 2 C,
        (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C ∧
        B₀ = ((normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Set (C ⧸ pCore 2 C))).comap (QuotientGroup.mk' (pCore 2 C))).map
            (I.subtype.comp C.subtype) := by
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf, comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hn := local_cComponent_normal d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let : C.Normal := by
    simpa only [subgroupOf, comap_map_eq_self_of_injective I.subtype_injective] using hn
  let B₀ := componentSylowNormalizer T I C
  obtain ⟨hBn,hs⟩ := normal_component_sylow_normalizer_at h (structural.at T) I hI C hout
  have hBH : B₀ ≤ F.H := (map_subtype_le _).trans hI.2.1
  have hBM := point_normalized_solvable_le_normalizer d h hab structural previous faithful
    earlier B₀ hBH hs hBn
  have hBA := point_normalized_solvable_normalizes_point d h hab structural previous faithful
    earlier B₀ hBH hs hBn
  have hres : (pResidual 2 B₀).map B₀.subtype ≤ B₀ := map_subtype_le _
  exact ⟨map_mono inf_le_left,hs,hBn,hBM,hBA,
    hBn.trans (normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀)),
    hres.trans hBM,hres.trans hBA,
    componentSylowNormalizer_quotient I (F.sylow_le_of_mem_Hz hI) C⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
