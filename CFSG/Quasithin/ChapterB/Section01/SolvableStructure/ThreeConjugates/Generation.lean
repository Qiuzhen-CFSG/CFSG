module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ImageTransfer
/-!
# The stable generated image is the source quotient

Sylow conjugacy inside H puts every best offender into T. Since M is normal
in H, this proves J(H,V) ≤ M. The commutator hypothesis puts K, and hence
its T-conjugates, in J(H,V), proving equality. Restricting offenders to H
preserves their weight comparisons in both directions.

The nontrivial images of this whole family generate precisely the image of
M acting on U. Its kernel is the two-core inside M. The first isomorphism
theorem therefore identifies M/O₂(M) with that stable generated subgroup,
with an explicit compatibility equation on every quotient representative.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem best_map_subtype (H : Subgroup G) {A : Subgroup H}
    (hA : IsBestOffender (ρ.comp H.subtype) A) : IsBestOffender ρ (A.map H.subtype) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map H.subtype⟩, ?_⟩
  · intro hb
    apply hA.1.1
    apply map_injective H.subtype_injective
    simpa only [Subgroup.map_bot] using hb
  · intro B hB
    have hBA : B.comap H.subtype ≤ A := by
      simpa only [comap_map_eq_self_of_injective H.subtype_injective] using (comap_mono (f := H.subtype) hB)
    have hmap : (B.comap H.subtype).map H.subtype = B :=
      map_comap_eq_self (hB.trans (map_le_range _ _))
    simpa only [weight_comp_map ρ H.subtype H.subtype_injective, hmap] using hA.2 _ hBA

/-- The best-offender subgroup in T is unchanged by passing to its actual overgroup H. -/
theorem localOffenderSubgroup_subgroupOf (K T : Subgroup G) :
    localOffenderSubgroup (localRepresentation ρ K T) (T.subgroupOf (K ⊔ T)) =
      (localOffenderSubgroup ρ T).subgroupOf (K ⊔ T) := by
  let H := K ⊔ T
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    have hb := best_map_subtype ρ H hA.1
    have hAT : A.map H.subtype ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA.2 ha
    have hle : A.map H.subtype ≤ localOffenderSubgroup ρ T :=
      le_iSup_of_le (A.map H.subtype) (le_iSup_of_le ⟨hb, hAT⟩ le_rfl)
    intro a ha
    exact hle (mem_map_of_mem H.subtype ha)
  · have hle : localOffenderSubgroup ρ T ≤
        (localOffenderSubgroup (localRepresentation ρ K T) (T.subgroupOf H)).map H.subtype := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      have hAH : A ≤ H := hA.2.trans le_sup_right
      have hAT : A.subgroupOf H ≤ T.subgroupOf H := comap_mono hA.2
      rw [← map_subgroupOf_eq_of_le hAH]
      exact map_mono (le_iSup_of_le _ (le_iSup_of_le ⟨hA.1.subgroupOf ρ hAH, hAT⟩ le_rfl))
    intro a ha
    obtain ⟨b, hb, he⟩ := hle ha
    exact (Subtype.ext he : b = a) ▸ hb

variable [Finite G]

theorem mixedSubgroup_eq_offenderSubgroup (K : Subgroup G) (T : Sylow 2 G)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆) :
    mixedSubgroup ρ K (T : Subgroup G) =
      (offenderSubgroup (localRepresentation ρ K (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype := by
  let H := K ⊔ (T : Subgroup G)
  let J := offenderSubgroup (localRepresentation ρ K (T : Subgroup G))
  let : J.Normal := offenderSubgroup_normal _
  have hJT : localOffenderSubgroup ρ (T : Subgroup G) ≤ J.map H.subtype := by
    rw [← map_subgroupOf_eq_of_le
      ((localOffenderSubgroup_le ρ (T : Subgroup G)).trans le_sup_right)]
    exact map_mono (localOffenderSubgroup_le_global ρ K (T : Subgroup G))
  have hKJ : K ≤ J.map H.subtype := by
    rw [← map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
    apply map_mono
    rw [local_commutator ρ K (T : Subgroup G) hcomm]
    exact (commutator_mono le_rfl (localOffenderSubgroup_le_global ρ K (T : Subgroup G))).trans
      (commutator_le_right _ _)
  have hnormal : H ≤ normalizer (J.map H.subtype) := by
    apply le_normalizer_iff.mpr
    rintro g hg x ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (inferInstance : J.Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩
  apply le_antisymm
  · exact sup_le hJT (iSup_conjugates_le_of_le_normalizer _ _ _ hKJ
      ((show (T : Subgroup G) ≤ H from le_sup_right).trans hnormal))
  · let M := (mixedSubgroup ρ K (T : Subgroup G)).subgroupOf H
    let : M.Normal := mixedSubgroup_normal ρ K (T : Subgroup G)
    have hJM : J ≤ M := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      let TH : Sylow 2 H := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
      let : IsElementaryAbelian 2 A := hA.1.1.2
      obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S TH
      have hAT : A.map (MulAut.conj g).toMonoidHom ≤ (TH : Subgroup H) := by
        rw [← hg]
        exact map_mono hS
      have hbest := best_map_subtype ρ H (hA.1.map_conj _ g)
      have hle : (A.map (MulAut.conj g).toMonoidHom).map H.subtype ≤
          localOffenderSubgroup ρ (T : Subgroup G) := by
        apply le_iSup_of_le ((A.map (MulAut.conj g).toMonoidHom).map H.subtype)
        refine le_iSup_of_le (show IsBestOffender ρ _ ∧ _ ≤ (T : Subgroup G) from ⟨hbest, ?_⟩) le_rfl
        rintro _ ⟨a, ha, rfl⟩
        exact hAT ha
      intro a ha
      have ham : g * a * g⁻¹ ∈ M :=
        (show localOffenderSubgroup ρ (T : Subgroup G) ≤ mixedSubgroup ρ K (T : Subgroup G)
          from le_sup_left) (hle (mem_map_of_mem H.subtype
            (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)))
      have := (inferInstance : M.Normal).conj_mem (g * a * g⁻¹) ham g⁻¹
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [← map_subgroupOf_eq_of_le (mixedSubgroup_le ρ K (T : Subgroup G))]
    exact map_mono hJM

omit [Finite G] in
/-- Restricting to a normal fixed space is the image under the whole-group action map. -/
theorem fixedSpace_restrictedSubgroup_eq_map (Q : Subgroup G) [Q.Normal] (A : Subgroup G) :
    restrictedSubgroup ρ (fixedSpace ρ Q) A = A.map (fixedSpaceActionHom ρ Q) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, fixedSpace_stable ρ Q (mem_top a)⟩, ha, rfl⟩

omit [Finite G] in
theorem local_restrictedSubgroup_eq_map (K T : Subgroup G) (A : Subgroup (K ⊔ T : Subgroup G)) :
    restrictedSubgroup (localRepresentation ρ K T) (localFixedSpace ρ K T) A =
      A.map (localActionHom ρ K T) :=
  fixedSpace_restrictedSubgroup_eq_map _ _ _

omit [Finite G] in
/-- Discarding trivial images does not change the subgroup generated by the image family. -/
theorem localImageFamily_generated (K T : Subgroup G) :
    generatedBy (localImageFamily ρ K T) ⊤ =
      (offenderSubgroup (localRepresentation ρ K T)).map (localActionHom ρ K T) := by
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun hD => ?_
    obtain ⟨_, A, hA, rfl⟩ := hD.1
    rw [local_restrictedSubgroup_eq_map]
    exact map_mono (le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl))
  · change (⨆ A, ⨆ (_ : IsBestOffender (localRepresentation ρ K T) A ∧ A ≤ ⊤), A).map _ ≤ _
    simp only [Subgroup.map_iSup]
    refine iSup_le fun A => iSup_le fun hA => ?_
    rw [← local_restrictedSubgroup_eq_map]
    by_cases hb : restrictedSubgroup (localRepresentation ρ K T) (localFixedSpace ρ K T) A = ⊥
    · exact hb.le.trans bot_le
    · exact le_iSup_of_le _ (le_iSup_of_le ⟨⟨hb, A, hA.1, rfl⟩, le_top⟩ le_rfl)

/-- The actual action on U restricted to M. -/
noncomputable def mixedActionHom (K T : Subgroup G) :
    mixedSubgroup ρ K T →*
      subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T) :=
  (localActionHom ρ K T).comp (inclusion (mixedSubgroup_le ρ K T))

variable [FiniteDimensional (ZMod 2) V]

/-- The kernel inside M is its intrinsic two-core. -/
theorem mixedActionHom_ker (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    (mixedActionHom ρ K T).ker = pCore 2 (mixedSubgroup ρ K T) := by
  change (localActionHom ρ K T).ker.comap (inclusion (mixedSubgroup_le ρ K T)) = _
  rw [localActionHom_ker ρ hf K T hK hcard hT, mixed_twoCore_eq_comap]

omit [FiniteDimensional (ZMod 2) V] in
/-- The range of the M-action is exactly the generated stable image family. -/
theorem mixedActionHom_range (K : Subgroup G) (T : Sylow 2 G)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆) :
    (mixedActionHom ρ K (T : Subgroup G)).range =
      generatedBy (localImageFamily ρ K (T : Subgroup G)) ⊤ := by
  rw [localImageFamily_generated]
  have hM : (mixedSubgroup ρ K (T : Subgroup G)).subgroupOf (K ⊔ (T : Subgroup G)) =
      offenderSubgroup (localRepresentation ρ K (T : Subgroup G)) := by
    apply map_injective (K ⊔ (T : Subgroup G)).subtype_injective
    rw [map_subgroupOf_eq_of_le (mixedSubgroup_le ρ K (T : Subgroup G))]
    exact mixedSubgroup_eq_offenderSubgroup ρ K T hcomm
  rw [mixedActionHom, MonoidHom.range_comp, inclusion_range, hM]

/-- The quotient in the source is the subgroup generated by the actual image family. -/
noncomputable def mixedActionQuotientEquiv (hf : Function.Injective ρ)
    (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆) :
    (mixedSubgroup ρ K (T : Subgroup G) ⧸ pCore 2 (mixedSubgroup ρ K (T : Subgroup G))) ≃*
      generatedBy (localImageFamily ρ K (T : Subgroup G)) ⊤ :=
  (QuotientGroup.quotientMulEquivOfEq
    (mixedActionHom_ker ρ hf K (T : Subgroup G) hK hcard T.isPGroup').symm).trans
    ((QuotientGroup.quotientKerEquivRange (mixedActionHom ρ K (T : Subgroup G))).trans
      (MulEquiv.subgroupCongr (mixedActionHom_range ρ K T hcomm)))

@[simp] theorem mixedActionQuotientEquiv_mk (hf : Function.Injective ρ)
    (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆)
    (m : mixedSubgroup ρ K (T : Subgroup G)) :
    (mixedActionQuotientEquiv ρ hf K T hK hcard hcomm
      (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K (T : Subgroup G))) m) :
        subspaceActionImage (localRepresentation ρ K (T : Subgroup G))
          (localFixedSpace ρ K (T : Subgroup G))) = mixedActionHom ρ K (T : Subgroup G) m := by
  simp [mixedActionQuotientEquiv, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivRange]
  rfl

end CFSG.Quasithin.ChapterB.ThreeConjugates
