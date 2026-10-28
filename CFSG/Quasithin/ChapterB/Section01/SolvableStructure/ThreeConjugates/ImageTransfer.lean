module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Target
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# The structural theorem applied to the fixed-space image

The commutator identity prevents all local best offenders from lying in the
relative two-core: otherwise their commutators with K put the order-three
subgroup in a two-group. The proved fixed-space kernel identity therefore
supplies a best offender acting nontrivially on U. Restriction transfers it,
and transfers stability of the whole best-offender family.

This discharges every hypothesis needed to apply the explicitly conditional
universal B.1.8 theorem to Aut_H(U). The selected-factor equality concerns
the generated image family, not the false printed family-saturation equality.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The source local commutator identity, inside its relative overgroup. -/
theorem local_commutator (K T : Subgroup G)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    K.subgroupOf (K ⊔ T) =
      ⁅K.subgroupOf (K ⊔ T), (localOffenderSubgroup ρ T).subgroupOf (K ⊔ T)⁆ := by
  apply Subgroup.map_injective (K ⊔ T).subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le (show K ≤ K ⊔ T from le_sup_left),
    map_subgroupOf_eq_of_le ((localOffenderSubgroup_le ρ T).trans le_sup_right)]
  exact hcomm

/-- Local best offenders remain best offenders after restricting the actor to H. -/
theorem localOffenderSubgroup_le_global (K T : Subgroup G) :
    (localOffenderSubgroup ρ T).subgroupOf (K ⊔ T) ≤
      offenderSubgroup (localRepresentation ρ K T) := by
  have hle : localOffenderSubgroup ρ T ≤
      (offenderSubgroup (localRepresentation ρ K T)).map (K ⊔ T).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    have hAH : A ≤ K ⊔ T := hA.2.trans le_sup_right
    rw [← map_subgroupOf_eq_of_le hAH]
    exact map_mono (le_iSup_of_le (A.subgroupOf (K ⊔ T))
      (le_iSup_of_le ⟨hA.1.subgroupOf ρ hAH, le_top⟩ le_rfl))
  intro x hx
  obtain ⟨y, hy, he⟩ := hle hx
  exact (Subtype.ext he : y = x) ▸ hy

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem local_three_not_le_twoCore (K T : Subgroup G) (hcard : Nat.card K = 3) :
    ¬ K.subgroupOf (K ⊔ T) ≤ pCore 2 (K ⊔ T : Subgroup G) := by
  intro hle
  have hp : IsPGroup 2 (K.subgroupOf (K ⊔ T)) := pCore_isPGroup.to_le hle
  have hcard' : Nat.card (K.subgroupOf (K ⊔ T)) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show K ≤ K ⊔ T from le_sup_left)).toEquiv).trans hcard
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hcard'] at hn
  have hdiv : 2 ∣ 3 := by
    cases n with
    | zero => norm_num at hn
    | succ n => rw [hn, pow_succ]; exact dvd_mul_left _ _
  norm_num at hdiv

/-- Some best offender of H acts nontrivially on the fixed space of O₂(H). -/
theorem exists_local_best_noncentral (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    ∃ A : Subgroup (K ⊔ T : Subgroup G), IsBestOffender (localRepresentation ρ K T) A ∧
      ¬ localFixedSpace ρ K T ≤ fixedSpace (localRepresentation ρ K T) A := by
  classical
  by_contra hn
  push Not at hn
  have hJ : offenderSubgroup (localRepresentation ρ K T) ≤
      (localActionHom ρ K T).ker := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    apply (fixedSpaceActionHom_ker (localRepresentation ρ K T)
      (pCore 2 (K ⊔ T : Subgroup G))).ge
    exact ⟨mem_top a, fun v hv => hn A hA.1 hv ⟨a, ha⟩⟩
  rw [localActionHom_ker ρ hf K T hK hcard hT] at hJ
  apply local_three_not_le_twoCore K T hcard
  rw [local_commutator ρ K T hcomm]
  exact (commutator_mono le_rfl ((localOffenderSubgroup_le_global ρ K T).trans hJ)).trans
    (commutator_le_right _ _)

/-- The precise nontrivial image family used in B.1.12. -/
noncomputable def localImageFamily (K T : Subgroup G) :=
  restrictedFamily (localRepresentation ρ K T) (localFixedSpace ρ K T)
    {A | IsBestOffender (localRepresentation ρ K T) A}

theorem localImageFamily_stable (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    IsStable (subspaceImageRepresentation (localRepresentation ρ K T) (localFixedSpace ρ K T))
      (localImageFamily ρ K T) := by
  have hn := exists_local_best_noncentral ρ hf K T hK hcard hT hcomm
  have hff : IsFFModule (localRepresentation ρ K T) :=
    (isFFModule_iff_exists_bestOffender _).mpr ⟨hn.choose, hn.choose_spec.1⟩
  exact (isStable_bestOffenders _ hff).restrictedFamily _ _
    (fun _ _ => le_top.trans (fixedSpace_stable _ _)) hn

theorem localImage_isFFModule (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    IsFFModule (subspaceImageRepresentation (localRepresentation ρ K T) (localFixedSpace ρ K T)) := by
  have hs := localImageFamily_stable ρ hf K T hK hcard hT hcomm
  obtain ⟨A, hA⟩ := hs.1
  exact (isFFModule_iff_exists_bestOffender _).mpr ⟨A, hs.2.1 A hA⟩

/-- Apply the universal structural theorem to the actual faithful fixed-space action. -/
theorem localImage_structure (structureTheorem : SolvableFFTheorem.{v, v})
    (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    Nonempty (SolvableFFStructure
      (subspaceImageRepresentation (localRepresentation ρ K T) (localFixedSpace ρ K T))) := by
  exact structureTheorem _ _ _ (localActionImage_solvable ρ K T hK hcard hT)
    (localActionImage_twoCore ρ hf K T hK hcard hT)
    (subspaceImageRepresentation_injective _ _)
    (localImage_isFFModule ρ hf K T hK hcard hT hcomm)

/-- The actual stable image family generates selected whole B.1.8 factors. -/
theorem localImage_selected_factors (structureTheorem : SolvableFFTheorem.{v, v})
    (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (hcomm : K = ⁅K, localOffenderSubgroup ρ T⁆) :
    ∃ d : SolvableFFStructure
        (subspaceImageRepresentation (localRepresentation ρ K T) (localFixedSpace ρ K T)),
      ∃ I : Set (Fin d.count),
        generatedBy (localImageFamily ρ K T) ⊤ = ⨆ i ∈ I, d.factor i := by
  obtain ⟨d⟩ := localImage_structure ρ structureTheorem hf K T hK hcard hT hcomm
  obtain ⟨I, hI⟩ := d.stable_product _ (localImageFamily_stable ρ hf K T hK hcard hT hcomm)
  exact ⟨d, I, hI⟩

end CFSG.Quasithin.ChapterB.ThreeConjugates
