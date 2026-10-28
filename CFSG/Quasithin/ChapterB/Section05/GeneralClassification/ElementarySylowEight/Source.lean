module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ElementarySylowEight.Adequate
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Representation.NormalComponentConstituents
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Image

/-!
# Normality of the actual A5 in a small elementary-Sylow FF image

Complete B.5 is applied to the literal normal offender subgroup. The retained
A5 becomes a component there. Two distinct conjugate A5 components would
have elementary two-rank four, contradicting the original Sylow bound.
Thus its actual fixed space is invariant under the whole actor; faithful
irreducibility forces that fixed space to vanish.

This is the source-specific actor reduction for the opposite plane in
Aschbacher--Smith 12.7.5, p.841. No ambient centralizer kernel is identified
with an elementary plane, and no universal MS-pair conclusion is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The actual A5 in the normal offender subgroup is normal in the entire
faithful actor, with its original cover and Sylow bounds unchanged. -/
theorem normal_from_source
    (hf : Function.Injective ρ) (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D) (hb : Bound D)
    (C : Subgroup D) (hCJ : C ≤ offenderSubgroup ρ)
    (eC : C ≃* alternatingGroup (Fin 5)) : C.Normal := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  let c := offenderSubgroup_adequateAlternative ρ hf hcore cover
  let a := (subgroupOfEquivOfLe hCJ).trans eC
  let : (C.subgroupOf J).Normal := normal_of_adequate
    (hb.of_injective J.subtype J.subtype_injective) c a
  have hs : C.IsSubnormal := IsSubnormal.trans hCJ
    (inferInstance : (C.subgroupOf J).Normal).isSubnormal
    (inferInstance : J.Normal).isSubnormal
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup C := eC.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  have hz : center C = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  let : IsQuasisimple C := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : IsComponent D C := ⟨hs,inferInstance⟩
  have hrD : primeRank 2 D ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le D).mpr
    intro E he
    let : IsElementaryAbelian 2 E := he
    obtain ⟨P,hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
    exact (card_le_of_le hEP).trans (hb.sylow P).2
  have hrC : 2 ≤ primeRank 2 C := by
    let P : Sylow 2 C := default
    let : IsElementaryAbelian 2 P :=
      ((hb.of_injective C.subtype C.subtype_injective).sylow P).1
    have hcard : Nat.card C = 60 := by
      rw [Nat.card_congr eC.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hp : Nat.card P = 2 ^ 2 := by
      rw [P.card_eq_multiplicity,hcard]
      decide +kernel
    exact IsElementaryAbelian.primeRank_ge_of_card (P : Subgroup C) hp
  exact hc.normal_of_centerless_of_primeRank hz 2 (by omega)

/-- Faithful irreducibility kills the actual A5-fixed space. The only
membership condition is in the literal normal offender subgroup. -/
theorem fixedSpace_eq_bot_from_source
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D) (hb : Bound D)
    (C : Subgroup D) (hCJ : C ≤ offenderSubgroup ρ)
    (eC : C ≃* alternatingGroup (Fin 5)) : fixedSpace ρ C = ⊥ := by
  let : IsIrreducible ρ := hi
  have hcore := Representation.QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible ρ hf
  let : C.Normal := normal_from_source ρ hf hcore cover hb C hCJ eC
  apply fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi C
  intro he
  have hc : Nat.card C = 60 := by
    rw [Nat.card_congr eC.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [he] at hc
  norm_num at hc

end CFSG.Quasithin.ChapterB.SourceInduction.ElementarySylowEight
