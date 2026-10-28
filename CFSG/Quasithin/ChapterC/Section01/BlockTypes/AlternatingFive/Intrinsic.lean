module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Constructing an A₅ block from its intrinsic core action

A marking of X/O₂(X) by A₅ and of its actual core by the five-point binary
augmentation module supplies the whole block structure. Faithfulness makes the
core self-centralizing, hence equal to the generalized Fitting subgroup.
Irreducibility gives [O₂(X),X]=O₂(X) and trivial central fixed layer. The literal
block quotient is then identified with the natural deleted-permutation module
through the original coordinates, retaining conjugation and the quotient map.

Only finiteness, two-perfection, and the marked core action are assumed. The
normalizer-action wrapper is the intrinsic consumer used after the original
core-collapse argument in 13.5.15. No fitting, faithfulness, irreducibility,
commutator-generation, or block-model premise is added.

Source: Aschbacher--Smith, definitions C.1.7 and C.1.12, printed pp.123--124;
the intrinsic construction after core collapse in G.2.4(8), pp.334--335;
and the selected A₅ block in 13.5.15.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.AlternatingFiveIntrinsic
variable {X : Type*} [Group X]
variable (eQ : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (eV : pCore 2 X ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (x : X) (v : pCore 2 X),
      (eV (MulAut.conjNormal x v)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 X) x)) (eV v).toAdd)

private abbrev naturalEquiv : pCore 2 X ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  eV.trans (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative

include eV he

private theorem natural_equivariant (x : X) (v : pCore 2 X) :
    (naturalEquiv eV (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
        (eQ (QuotientGroup.mk' (pCore 2 X) x)) (naturalEquiv eV v).toAdd := by
  change BinaryPermutation.coreEquivNatural (Fin 5) (by decide) (eV (MulAut.conjNormal x v)).toAdd = _
  rw [he]
  exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) _ _

/-- Faithfulness of the marked five-letter module makes the original core self-centralizing. -/
theorem core_selfCentralizing : centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  intro x hx
  have ha : eQ (QuotientGroup.mk' (pCore 2 X) x) = 1 := by
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := (naturalEquiv eV).surjective (Multiplicative.ofAdd v)
    have hc : MulAut.conjNormal x w = w := by
      apply Subtype.ext
      change x * (w : X) * x⁻¹ = w
      rw [← hx w w.property, mul_inv_cancel_right]
    have hh := natural_equivariant eQ eV he x w
    rw [hc,hw] at hh
    change v = BinaryPermutation.naturalRepresentation (Fin 5)
      (eQ (QuotientGroup.mk' (pCore 2 X) x)).val v at hh
    simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hh.symm
  have hq : QuotientGroup.mk' (pCore 2 X) x = 1 := eQ.injective (ha.trans eQ.map_one.symm)
  exact (QuotientGroup.eq_one_iff x).mp hq

omit he eQ in
/-- The marked additive core is intrinsically elementary abelian. -/
theorem core_elementary : IsElementaryAbelian 2 (pCore 2 X) := by
  have hm : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.core (Fin 5))) := {
    is_comm := ⟨mul_comm⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      apply Subtype.ext
      ext i
      exact CharTwo.add_self_eq_zero _) }
  let := hm
  exact IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective

/-- Normal subgroups inside the full core are trivial or the full core. -/
theorem invariant_core (N : Subgroup X) (hn : N.Normal) (hN : N ≤ pCore 2 X) :
    N = ⊥ ∨ N = pCore 2 X := by
  let e := naturalEquiv eV
  let S : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 5)) := {
    carrier := {v | (e.symm (Multiplicative.ofAdd v)).val ∈ N}
    zero_mem' := by change (e.symm 1).val ∈ N; rw [map_one]; exact N.one_mem
    add_mem' := by
      intro v w hv hw
      change (e.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w)).val ∈ N
      rw [map_mul]
      exact N.mul_mem hv hw
    smul_mem' := by
      intro c v hv
      fin_cases c
      · change (e.symm (Multiplicative.ofAdd ((0 : ZMod 2) • v))).val ∈ N
        rw [zero_smul]
        change (e.symm 1).val ∈ N
        rw [map_one]; exact N.one_mem
      · change (e.symm (Multiplicative.ofAdd ((1 : ZMod 2) • v))).val ∈ N
        rw [one_smul]
        exact hv }
  let W : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) :=
    ⟨S, by
      intro a v hv
      obtain ⟨z,hz⟩ := eQ.surjective a
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
      let u := e.symm (Multiplicative.ofAdd v)
      have heq : e.symm (Multiplicative.ofAdd
          (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) a v)) =
          MulAut.conjNormal x u := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [MulEquiv.apply_symm_apply]
        have hh := natural_equivariant eQ eV he x u
        change _ = BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 X) x)) (e (e.symm (Multiplicative.ofAdd v))).toAdd at hh
        rw [hz,MulEquiv.apply_symm_apply] at hh
        exact hh.symm
      change (e.symm (Multiplicative.ofAdd _)).val ∈ N
      rw [heq]
      exact hn.conj_mem _ hv x⟩
  let : IsIrreducible (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) :=
    BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply bot_unique
    intro x hx
    let u : pCore 2 X := ⟨x,hN hx⟩
    have hv : (e u).toAdd ∈ W := by
      change (e.symm (Multiplicative.ofAdd (e u).toAdd)).val ∈ N
      simpa using hx
    rw [hb] at hv
    have he1 : e u = e 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective hv
    exact congrArg Subtype.val (e.injective he1)
  · right
    apply le_antisymm hN
    intro x hx
    let u : pCore 2 X := ⟨x,hx⟩
    have hv : (e u).toAdd ∈ W := ht ▸ Submodule.mem_top
    change (e.symm (Multiplicative.ofAdd (e u).toAdd)).val ∈ N at hv
    simpa using hv

/-- The source commutator layer is the full intrinsic core. -/
theorem blockU_eq_core : blockU X = pCore 2 X := by
  rcases invariant_core eQ eV he (blockU X) inferInstance blockU_le_core with hb | ht
  · exfalso
    have hc : pCore 2 X ≤ center X := commutator_top_right_eq_bot_iff_le_center.mp hb
    have htcore : (⊤ : Subgroup X) ≤ pCore 2 X :=
      (by rw [centralizer_center] : (⊤ : Subgroup X) ≤ centralizer (center X : Set X)).trans
        ((centralizer_le hc).trans (core_selfCentralizing eQ eV he))
    have hall (a : alternatingGroup (Fin 5)) : a = 1 := by
      obtain ⟨z,rfl⟩ := eQ.surjective a
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
      have hx : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (htcore (mem_top x))
      rw [hx,map_one]
    obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    exact ha (hall a)
  · exact ht

/-- No nonidentity central element lies in the commutator layer. -/
theorem blockU_inf_center : blockU X ⊓ center X = ⊥ := by
  rcases invariant_core eQ eV he (blockU X ⊓ center X) inferInstance
    (inf_le_left.trans blockU_le_core) with hb | ht
  · exact hb
  · have hc : pCore 2 X ≤ center X := ht.symm ▸ inf_le_right
    have hb : blockU X = ⊥ := commutator_top_right_eq_bot_iff_le_center.mpr hc
    have hc0 : pCore 2 X = ⊥ := (blockU_eq_core eQ eV he).symm.trans hb
    let : Nontrivial (BinaryPermutation.core (Fin 5)) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
        rw [BinaryPermutation.finrank_core]; decide)
    let : Nontrivial (pCore 2 X) := eV.toEquiv.nontrivial
    exact ((nontrivial_iff_ne_bot (pCore 2 X)).mp inferInstance hc0).elim

/-- The literal central denominator is trivial. -/
theorem blockFixed_eq_bot : blockFixed X = ⊥ := by
  apply map_injective (blockU X).subtype_injective
  rw [blockFixed_map, blockU_inf_center eQ eV he, Subgroup.map_bot]

/-- All short-group conditions follow from the actual quotient and core action. -/
theorem short [Finite X] (hperfect : IsPPerfect 2 X) : IsShort X := by
  let : IsElementaryAbelian 2 (pCore 2 X) := core_elementary eV
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hne : pCore 2 X ≠ ⊥ := by
    let : Nontrivial (BinaryPermutation.core (Fin 5)) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
        rw [BinaryPermutation.finrank_core]; decide)
    let : Nontrivial (pCore 2 X) := eV.toEquiv.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  refine {
    finite := inferInstance
    twoPerfect := hperfect
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (core_selfCentralizing eQ eV he)
    elementary := ?_
    central := ?_
    quotient := Or.inl (IsQuasisimple.of_mulEquiv eQ.symm)
    irreducible := ?_ }
  · rw [blockU_eq_core eQ eV he]
    infer_instance
  · rw [blockU_eq_core eQ eV he]
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : pCore 2 X) ⟨x,hx⟩)
  · rw [BlockModuleIrreducible, blockU_inf_center eQ eV he, blockU_eq_core eQ eV he]
    exact ⟨bot_lt_iff_ne_bot.mpr hne,fun N hn _ hN => invariant_core eQ eV he N hn hN⟩

/-- The block layer uses the supplied full-core coordinates. -/
private def layerIso : blockU X ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  (MulEquiv.subgroupCongr (blockU_eq_core eQ eV he)).trans (naturalEquiv eV)

/-- The marked natural module of the literal block quotient. -/
def moduleIso : BlockModule X ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  (((QuotientGroup.quotientMulEquivOfEq (blockFixed_eq_bot eQ eV he)).trans
    QuotientGroup.quotientBot).trans (layerIso eQ eV he))

/-- The block module map agrees with the original core coordinates on representatives. -/
theorem moduleIso_mk (u : blockU X) :
    moduleIso eQ eV he (QuotientGroup.mk' (blockFixed X) u) =
      Multiplicative.ofAdd (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
        (eV ⟨u,blockU_le_core u.property⟩).toAdd) := by rfl

/-- The quotient and module identifications retain the original conjugation action. -/
def blockModel : BlockModuleModel X
    ((BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) where
  quotientIso := eQ
  moduleIso := moduleIso eQ eV he
  intertwining x u := by
    apply Multiplicative.toAdd.injective
    rw [moduleIso_mk, moduleIso_mk]
    have h := natural_equivariant eQ eV he x ⟨u,blockU_le_core u.property⟩
    exact h

/-- Raw A₅ quotient and core coordinates construct the block without extra structural premises. -/
theorem alternatingBlock [Finite X] (hperfect : IsPPerfect 2 X) : IsAlternatingBlock X 5 := by
  refine ⟨by decide,short eQ eV he hperfect,
    (BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype,
    ⟨blockModel eQ eV he⟩,fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterC.AlternatingFiveIntrinsic

namespace CFSG.Quasithin.ChapterC
variable {X : Type*} [Group X] [Finite X]

/-- Source constructor in the original normalizer-action convention, as used after
identifying the selected component's actual core in 13.5.15. -/
theorem isAlternatingBlock_five_of_core_coordinates (hperfect : IsPPerfect 2 X)
    (eQ : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (eV : pCore 2 X ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (x : X) (v : pCore 2 X),
      (eV ((pCore 2 X).normalizerMonoidHom
        ⟨x,(pCore 2 X).normalizer_eq_top ▸ mem_top x⟩ v)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 X) x)) (eV v).toAdd) :
    IsAlternatingBlock X 5 :=
  AlternatingFiveIntrinsic.alternatingBlock eQ eV he hperfect

end CFSG.Quasithin.ChapterC
