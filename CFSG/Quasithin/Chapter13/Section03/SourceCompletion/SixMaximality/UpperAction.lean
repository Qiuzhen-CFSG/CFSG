module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupAction.QuotientConjugation
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The literal A₇ upper action and the original A₆ four-space

The original module V meets O₂(I) nontrivially by the16/32 core bounds,
and L-transitivity makes this intersection all V. Actual conjugation on
O₂(I) descends through the specified I/O₂(I)≃A₇ equivalence. The image
of L has order360: its quotient by its two-core is A₆, while its order
divides2520. The original V is therefore an irreducible four-dimensional
subrepresentation of that exact lower image. The proved C_T(L)=1 makes
its fixed space on the whole upper core zero.

These are the actual inputs to the small A₇ module argument for the
normal A₆ consumer of13.3.2 and13.5.15. No normalization of V by I is
assumed. Source: Aschbacher–Smith13.3.2 and13.5.15, pp.884–885,920–921.
-/


public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem module_le_upper_core {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) : D.V ≤ I.pCoreIn 2 := by
  let W := I.pCoreIn 2
  have hWQ : W ≤ D.LT.pCoreIn 2 :=
    UpperCore.upper_core_le_original d hI.maximal_faithful.1.1 hLI
  have hWc : W ≤ centralizer (D.V : Set G) :=
    hWQ.trans (h.sylow_centralizer.symm.le.trans inf_le_right)
  have hWcard : Nat.card W = 16 ∨ Nat.card W = 32 := by
    have hc : Nat.card W = Nat.card (pCore 2 I) :=
      card_map_of_injective I.subtype_injective
    rw [hc]
    exact UpperCore.upper_core_card d h e hseed hn hU hI hLI
  let : IsElementaryAbelian 2 D.V := h.elementary
  have hVQ : D.V ≤ D.LT.pCoreIn 2 := by
    rw [← h.sylow_centralizer]
    exact le_inf h.V_le_T (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hne : D.V ⊓ W ≠ ⊥ := by
    intro hz
    have hp := card_sup_eq_mul_of_normalizes_of_disjoint D.V W
      (hWc.trans (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hz)
    have hb := (card_le_of_le (sup_le hVQ hWQ)).trans
      (UpperCore.original_core_elementary_bound d h e hseed hn hU).2
    rw [hp,ReturningPlane.module_card d] at hb
    rcases hWcard with hc | hc <;> rw [hc] at hb <;> omega
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hLW : D.L ≤ normalizer (W : Set G) :=
    (hLI.trans I.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  obtain ⟨l,hl,heq⟩ := Section07.natural_nonzero_transitive d x.property.1 hv
    (fun he => hx (Subtype.ext he)) hv1
  rw [← heq]
  exact (mem_normalizer_iff.mp (hLW hl) x).1 x.property.2

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

def sevenMap {I : Subgroup G} (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    I →* alternatingGroup (Fin 7) :=
  eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))

def lowerSevenMap {I : Subgroup G} (hLI : D.L ≤ I)
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    D.L →* alternatingGroup (Fin 7) := (sevenMap eI).comp (inclusion hLI)

include e in
theorem lowerSevenMap_card {I : Subgroup G} (hLI : D.L ≤ I)
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    Nat.card (lowerSevenMap hLI eI).range = 360 := by
  let f := lowerSevenMap hLI eI
  have hk : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have heq : f.ker = (pCore 2 I).comap (inclusion hLI) := by
      ext l
      change eI (QuotientGroup.mk' (pCore 2 I) (inclusion hLI l)) = 1 ↔ _
      rw [eI.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff _
    rw [heq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLI)
  let c := (f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hk).symm.trans e
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = 360 := by
    rw [Nat.card_congr c.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hprod := card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range)
  obtain ⟨k,hkcard⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  rw [hc,hkcard] at hprod
  have hdiv := f.range.card_subgroup_dvd_card
  rw [hprod,nat_card_alternatingGroup] at hdiv
  norm_num [Nat.factorial] at hdiv
  have hkdiv : 2 ^ k ∣ 7 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 360)).mp hdiv
  have hk0 : k = 0 := by
    by_contra hk0
    have hh : 2 ∣ 7 := (show 2 ^ 1 ∣ 2 ^ k from pow_dvd_pow 2 (by omega)).trans hkdiv
    norm_num at hh
  simpa [hk0] using hprod

def coreSevenRepresentation {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    Representation (ZMod 2) (alternatingGroup (Fin 7)) (Additive (pCore 2 I)) :=
  Representation.elementaryRepresentation (p := 2)
    ((MulAut.quotientConjNormal (pCore 2 I) (pCore 2 I) (pCore 2 I).le_centralizer).comp
      eI.symm.toMonoidHom)

omit [Finite G] in
theorem coreSevenRepresentation_map {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) (i : I)
    (v : Additive (pCore 2 I)) :
    ((coreSevenRepresentation eI (sevenMap eI i) v).toMul.val : G) =
      (i : G) * (v.toMul.val : G) * (i : G)⁻¹ := by
  change ((MulAut.quotientConjNormal (pCore 2 I) (pCore 2 I) (pCore 2 I).le_centralizer
    (eI.symm (eI (QuotientGroup.mk' (pCore 2 I) i))) v.toMul).val : G) = _
  rw [eI.symm_apply_apply]
  rfl

def lowerModule {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    Subrepresentation ((coreSevenRepresentation eI).comp (lowerSevenMap hLI eI).range.subtype) where
  toSubmodule := AddSubgroup.toZModSubmodule 2
    ((D.V.comap (I.subtype.comp (pCore 2 I).subtype)).toAddSubgroup)
  apply_mem_toSubmodule := by
    intro a v hv
    obtain ⟨l,hl⟩ := a.property
    change (((coreSevenRepresentation eI) a.val v).toMul.val : G) ∈ D.V
    rw [← hl]
    change (((coreSevenRepresentation eI) (sevenMap eI (inclusion hLI l)) v).toMul.val : G) ∈ D.V
    rw [coreSevenRepresentation_map]
    exact (mem_normalizer_iff.mp (d.normalizes_V (mem_sup_left l.property)) _).1 hv

def lowerModuleEquiv {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (hVW : D.V ≤ I.pCoreIn 2) :
    (lowerModule d hLI eI).toSubmodule ≃ Additive D.V where
  toFun v := Additive.ofMul ⟨v.val.toMul.val.val,v.property⟩
  invFun v :=
    let x : I := ⟨v.toMul,(hVW.trans (pCoreIn_le 2 I)) v.toMul.property⟩
    have hx : x ∈ pCore 2 I := by
      obtain ⟨y,hy,he⟩ := hVW v.toMul.property
      exact (Subtype.ext he : y = x) ▸ hy
    ⟨Additive.ofMul ⟨x,hx⟩,v.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lowerModule_finrank {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (hVW : D.V ≤ I.pCoreIn 2) :
    Module.finrank (ZMod 2) (lowerModule d hLI eI).toSubmodule = 4 := by
  have hc : Nat.card (lowerModule d hLI eI).toSubmodule = 16 :=
    (Nat.card_congr (lowerModuleEquiv d hLI eI hVW)).trans (ReturningPlane.module_card d)
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := (lowerModule d hLI eI).toSubmodule)
  rw [hc,Nat.card_zmod] at hd
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hd.symm

theorem lowerModule_transitive {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    {v w : (lowerModule d hLI eI).toSubmodule} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a : (lowerSevenMap hLI eI).range,
      (lowerModule d hLI eI).toRepresentation a v = w := by
  have hv1 : (v.val.toMul.val : G) ≠ 1 := by
    intro hv1
    apply hv
    exact Subtype.ext (congrArg Additive.ofMul (Subtype.ext (Subtype.ext hv1)))
  have hw1 : (w.val.toMul.val : G) ≠ 1 := by
    intro hw1
    apply hw
    exact Subtype.ext (congrArg Additive.ofMul (Subtype.ext (Subtype.ext hw1)))
  obtain ⟨l,hl,he⟩ := Section07.natural_nonzero_transitive d v.property w.property hv1 hw1
  refine ⟨⟨lowerSevenMap hLI eI ⟨l,hl⟩,⟨⟨l,hl⟩,rfl⟩⟩,?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  exact (coreSevenRepresentation_map eI (inclusion hLI ⟨l,hl⟩) v.val).trans he

theorem lowerModule_irreducible {I : Subgroup G} [IsElementaryAbelian 2 (pCore 2 I)]
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (hVW : D.V ≤ I.pCoreIn 2) : (lowerModule d hLI eI).toRepresentation.IsIrreducible := by
  let : Nontrivial (lowerModule d hLI eI).toSubmodule :=
    Module.nontrivial_of_finrank_pos (by rw [lowerModule_finrank d hLI eI hVW]; decide)
  classical
  refine ⟨fun S => ?_⟩
  by_cases hs : S.toSubmodule = ⊥
  · exact .inl (Subrepresentation.toSubmodule_injective hs)
  right
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ S.toSubmodule.zero_mem
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  obtain ⟨a,rfl⟩ := lowerModule_transitive d hLI eI hv0 hw
  exact S.apply_mem_toSubmodule a hv

include d h e hseed hn hU in
theorem coreSevenRepresentation_fixed_eq_bot {I : Subgroup G}
    [IsElementaryAbelian 2 (pCore 2 I)]
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    Representation.OneCohomology.fixed
      ((coreSevenRepresentation eI).comp (lowerSevenMap hLI eI).range.subtype) = ⊥ := by
  apply bot_unique
  intro v hv
  have hvt : (v.toMul.val : G) ∈ (D.T : Subgroup G) :=
    (UpperCore.upper_core_le_original d hI.maximal_faithful.1.1 hLI).trans
      (h.sylow_centralizer.symm.le.trans inf_le_left)
      (mem_map_of_mem I.subtype v.toMul.property)
  have hvc : (v.toMul.val : G) ∈ centralizer (D.L : Set G) := by
    intro l hl
    have hf := hv (⟨lowerSevenMap hLI eI ⟨l,hl⟩,⟨⟨l,hl⟩,rfl⟩⟩ :
      (lowerSevenMap hLI eI).range)
    have hg := congrArg (fun w : Additive (pCore 2 I) => (w.toMul.val : G)) hf
    change (((coreSevenRepresentation eI) (sevenMap eI (inclusion hLI ⟨l,hl⟩)) v).toMul.val : G) = (v.toMul.val : G) at hg
    rw [coreSevenRepresentation_map] at hg
    exact mul_inv_eq_iff_eq_mul.mp hg
  have hz := (SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core
    d h e hseed hn hU).le ⟨hvt,hvc⟩
  change v = 0
  apply Additive.toMul.injective
  exact Subtype.ext (Subtype.ext (mem_bot.mp hz))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction