module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionDefs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.AlternatingSixRadicalNormality
public import Theory.Representation.BinaryAlternatingSixNaturalNormalizer

/-!
# Normality and natural-action transport for the terminal A₆ component

The A₆ radical quotient forces the lifted C-component to be normal in
the actual point normalizer. This proves Sylow normalization independently
of the terminal module classification or any radical/two-core equality.
The canonical radical quotient is equivariant for the literal terminal
conjugation action. One or two actual natural-module copies therefore
supply the published natural-action record, in any chosen A₆ marking.

Recognition of those module coordinates from the original flag geometry
remains an explicit premise; this is not the full source G.11.2 recognition.
The tensor row restricts to two copies, so its outer transpositions are
retained. Source: Aschbacher--Smith G.11.2(2),(10) and 14.3.15,
printed pp.364--367,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}

/-- The action on the radical quotient agrees with conjugation in the terminal
image, through the canonical quotient marking. -/
theorem ComponentLift.alternatingSixAction_eq_image_action
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    [hi : (F.terminalDot K).Normal] (t : T) :
    hK.alternatingSixAction e6 hn t = MulAut.congr e6
      (MulAut.conjNormal (QuotientGroup.mk' F.terminalHatAction.ker
        ⟨t, F.invariant 1 t.property⟩)) := by
  let := hi
  apply MulEquiv.ext
  intro a
  obtain ⟨k,rfl⟩ := hK.alternatingSixMap_surjective e6 a
  rw [hK.alternatingSixAction_equivariant e6 hn]
  apply e6.symm.injective
  simp only [ComponentLift.alternatingSixMap, ComponentLift.alternatingSixRadicalEquiv,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    MulAut.congr_apply, e6.symm_apply_apply]
  apply Subtype.ext
  change (hK.radicalQuotientEquiv (Or.inr ⟨e6⟩)
    (QuotientGroup.mk' (solvableRadical K)
      (K.normalizerMonoidHom ⟨t,hn t.property⟩ k)) : F.TerminalHdot) = _
  rw [MulAut.conjNormal_apply]
  change QuotientGroup.mk' F.terminalHatAction.ker
      ⟨(t : G) * (k : G) * (t : G)⁻¹, _⟩ =
    QuotientGroup.mk' F.terminalHatAction.ker ⟨t,F.invariant 1 t.property⟩ *
      QuotientGroup.mk' F.terminalHatAction.ker ⟨k,hK.le_pointNormalizer k.property⟩ *
    (QuotientGroup.mk' F.terminalHatAction.ker ⟨t,F.invariant 1 t.property⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

/-- A₆ forces relative normality in the actual point normalizer before any
identification of its radical with its two-core. -/
theorem ComponentLift.alternatingSix_normal_in_pointNormalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) [IsElementaryAbelian 2 V]
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    (K.subgroupOf F.H).Normal := by
  let c := subgroupOfEquivOfLe hK.le_pointNormalizer
  let d := QuotientGroup.congr _ _ c (map_solvableRadical_equiv c)
  exact Chapter1.Section02.normal_of_alternatingSix_radical_quotient
    (Recognition.pointNormalizer_sqtk hG F (by decide)) hK.component
    (d.trans (hK.alternatingSixRadicalEquiv e6))

/-- The original Sylow normalizes K, not merely its conjugate span. -/
theorem ComponentLift.alternatingSix_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) [IsElementaryAbelian 2 V]
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    (T : Subgroup G) ≤ normalizer (K : Set G) :=
  (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hK.le_pointNormalizer).mp
    (hK.alternatingSix_normal_in_pointNormalizer hG e6))

/-- The same normality descends along the literal terminal quotient map. -/
theorem ComponentLift.alternatingSix_image_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) [IsElementaryAbelian 2 V]
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6)) :
    (F.terminalDot K).Normal :=
  Normal.map (hK.alternatingSix_normal_in_pointNormalizer hG e6)
    (QuotientGroup.mk' F.terminalHatAction.ker)
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)

/-- Recognition of the actual restricted module is the remaining source input.
Both the natural module and its tensor with the two-dimensional Z₃ module
have the required natural automorphism action. -/
theorem ComponentLift.alternatingSixNaturalAction_of_coordinates
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 F.Uhat]
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hc : Representation.BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp (F.terminalDot K).subtype)) :
    hK.AlternatingSixNaturalAction e6 := by
  have hn := hK.alternatingSix_normalizes hG e6
  let := hK.alternatingSix_image_normal hG e6
  refine ⟨hn, fun t => ?_⟩
  rw [hK.alternatingSixAction_eq_image_action e6 hn]
  let a := QuotientGroup.mk' F.terminalHatAction.ker ⟨t, F.invariant 1 t.property⟩
  let ρ := F.terminalRepresentation
  apply Representation.BinaryAlternatingSixNaturalNormalizer.natural_of_coordinates
    (ρ.comp (F.terminalDot K).subtype) hc e6 (MulAut.conjNormal a)
    (LinearEquiv.ofBijective (ρ a) (Representation.apply_bijective ρ a))
  intro x v
  change ρ a (ρ (x : F.TerminalHdot) v) =
    ρ (a * (x : F.TerminalHdot) * a⁻¹) (ρ a v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
