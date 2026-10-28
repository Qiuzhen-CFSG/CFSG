module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.PResidual.ThreeFree
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The endomorphism-field argument for a normal short subgroup

Conjugation on X restricts to U(X) and descends to the literal quotient
U(X)/C_U(X). If Y centralizes X/O₂(X), its quotient action commutes with
the original representation of X/O₂(X), so it defines a homomorphism into
(BlockEndRing hX)ˣ. This is the actual intertwining ring from `Defs`.

The unit group is abelian and has precisely the prime support used in
`blockEndPrimes`. Thus O^π(Y) and [Y,Y] both act trivially. This argument
also covers empty π. The three-subgroup lemma and [U(X),X] = U(X) lift
fixation to U(X); two-perfection of Y then gives fixation of all of X via
the group-theoretic result in `Centralizer`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma C.1.10, printed p.124.
-/

public section

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.ModuleCentralizer
variable {L : Type*} [Group L]

/-- Automorphisms of X preserve the actual subgroup C_U(X). -/
private theorem fixed_map (a : MulAut L) :
    (blockFixed L).map (MulAut.characteristic (blockU L) a).toMonoidHom = blockFixed L := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (characteristic_iff_map_le.mp (inferInstance : (center L).Characteristic) a)
      (mem_map_of_mem a.toMonoidHom hu)
  · intro u hu
    refine ⟨MulAut.characteristic (blockU L) a⁻¹ u, ?_, ?_⟩
    · exact (characteristic_iff_map_le.mp (inferInstance : (center L).Characteristic) a⁻¹)
        (mem_map_of_mem a⁻¹.toMonoidHom hu)
    · change MulAut.characteristic (blockU L) a
        (MulAut.characteristic (blockU L) a⁻¹ u) = u
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

private def moduleAut : MulAut L →* MulAut (BlockModule L) where
  toFun a := QuotientGroup.congr (blockFixed L) (blockFixed L)
    (MulAut.characteristic (blockU L) a) (fixed_map a)
  map_one' := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) v
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) v
    rfl

private theorem moduleAut_mk (a : MulAut L) (u : blockU L) :
    moduleAut a (QuotientGroup.mk' (blockFixed L) u) =
    QuotientGroup.mk' (blockFixed L) (MulAut.characteristic (blockU L) a u) := rfl

variable {H : Type*} [Group H] (X : Subgroup H) [X.Normal]

private def ambientModuleAction : H →* MulAut (BlockModule X) :=
  moduleAut.comp MulAut.conjNormal

private def ambientUAction : H →* MulAut (blockU X) :=
  (MulAut.characteristic (blockU X)).comp MulAut.conjNormal

private theorem ambientModuleAction_mk (g : H) (u : blockU X) :
    ambientModuleAction X g (QuotientGroup.mk' (blockFixed X) u) =
    QuotientGroup.mk' (blockFixed X) (ambientUAction X g u) := rfl

private theorem ambientUAction_apply (g : H) (u : blockU X) :
    ((ambientUAction X g u : X) : H) = g * (u : X) * g⁻¹ := rfl

variable (hX : IsShort X)

include hX in
private theorem core_le_ker : (pCore 2 X).map X.subtype ≤ (ambientModuleAction X).ker := by
  rintro _ ⟨x, hx, rfl⟩
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed X) v
  rw [ambientModuleAction_mk]
  have he : ambientUAction X (x : H) u = u := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ambientUAction_apply]
    have hc := mem_centralizer_iff.mp (hX.core_centralizes_blockU hx) u u.property
    exact congrArg (fun z : X => (z : H)) (by
      simpa only [mul_inv_cancel_right] using congrArg (fun z : X => z * x⁻¹) hc.symm)
  change QuotientGroup.mk' (blockFixed X) (ambientUAction X (x : H) u) =
    QuotientGroup.mk' (blockFixed X) u
  rw [he]

end CFSG.Quasithin.ChapterC.ModuleCentralizer

namespace CFSG.Quasithin.ChapterC.ModuleCentralizer
open ExceptionalRestrictions
variable {H : Type*} [Group H] (X Y : Subgroup H) [X.Normal]
variable (hX : IsShort X)
variable [IsElementaryAbelian 2 (blockU X)] [IsElementaryAbelian 2 (BlockModule X)]

private def ambientRepresentation : Representation (ZMod 2) H (Additive (BlockModule X)) where
  toFun g := (ambientModuleAction X g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (ambientModuleAction X 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' g j := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (ambientModuleAction X (g * j) v.toMul) = _
    rw [map_mul]
    rfl

private theorem representation_restrict (x : X) :
    ambientRepresentation X (x : H) =
      moduleRepresentation hX (QuotientGroup.mk' (pCore 2 X) x) := by
  apply LinearMap.ext
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (blockFixed X) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (blockFixed X) u) := hu.symm
  rw [hv]
  change Additive.ofMul (ambientModuleAction X (x : H) (QuotientGroup.mk' (blockFixed X) u)) = _
  rw [ambientModuleAction_mk]
  exact congrArg Additive.ofMul (hX.exists_quotient_moduleAction.choose_spec x u).symm

private theorem ambient_commutes
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype) (y : Y)
    (g : X ⧸ pCore 2 X) (v : Additive (BlockModule X)) :
    ambientRepresentation X y (moduleRepresentation hX g v) =
      moduleRepresentation hX g (ambientRepresentation X y v) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) g
  rw [← representation_restrict X hX x]
  have he : ⁅ambientModuleAction X (y : H), ambientModuleAction X (x : H)⁆ = 1 := by
    rw [← map_commutatorElement]
    exact core_le_ker X hX (hcore (commutator_mem_commutator y.property x.property))
  have hh := DFunLike.congr_fun (commutatorElement_eq_one_iff_mul_comm.mp he) v.toMul
  exact congrArg Additive.ofMul hh

/-- The actual conjugation action, valued in the original endomorphism units. -/
private noncomputable def unitAction
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype) :
    Y →* (IntertwiningMap (moduleRepresentation hX) (moduleRepresentation hX))ˣ :=
  (CentralizerField.centralizerUnitsEquiv (moduleRepresentation hX)).toMonoidHom.comp
    (((ambientRepresentation X).asGroupHom.comp Y.subtype).codRestrict
      (CentralizerField.linearCentralizer (moduleRepresentation hX)) (fun y => by
        apply (CentralizerField.mem_linearCentralizer_iff _ _).mpr
        exact ambient_commutes X Y hX hcore y))

private theorem unitAction_apply
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype) (y : Y)
    (v : Additive (BlockModule X)) :
    (unitAction X Y hX hcore y).val v = ambientRepresentation X y v := rfl

end CFSG.Quasithin.ChapterC.ModuleCentralizer

namespace CFSG.Quasithin.ChapterC.ModuleCentralizer
variable {H : Type*} [Group H] [Finite H] (X Y : Subgroup H) [X.Normal]
variable (hX : IsShort X)

omit [Finite H] [X.Normal] in
/-- Both factors in the source residual condition lie in the action kernel. -/
private theorem units_trivial
    (hπ : piResidual (blockEndPrimes hX) Y ⊔ commutator Y = ⊤)
    (f : Y →* (BlockEndRing hX)ˣ) : ∀ y, f y = 1 := by
  let := blockEndRing_finite hX
  let : IsMulCommutative (BlockEndRing hX)ˣ :=
    ⟨⟨fun u v => Units.ext ((blockEndRing_isField hX).mul_comm u.val v.val)⟩⟩
  have hp : IsPiGroup (blockEndPrimes hX) f.range := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    exact hp.trans (card_subgroup_dvd_card f.range)
  have hk : (⊤ : Subgroup Y) ≤ f.ker := by
    rw [← hπ]
    exact sup_le (piResidual_le_ker_of_range _ f hp)
      (Abelianization.commutator_subset_ker f)
  intro y
  exact hk (mem_top y)

omit [Finite H] in
include hX in
/-- The source three-subgroup argument lifts fixation from U/C_U(X) to U. -/
private theorem centralizes_of_module_fixed
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype)
    (hfix : ∀ (y : Y) (u : blockU X),
      QuotientGroup.mk' (blockFixed X) (ambientUAction X y u) =
        QuotientGroup.mk' (blockFixed X) u) :
    Y ≤ centralizer ((blockU X).map X.subtype : Set H) := by
  let U := (blockU X).map X.subtype
  let Z := (center X).map X.subtype
  have hYU : ⁅Y, U⁆ ≤ Z := by
    apply commutator_le.mpr
    intro y hy u hu
    obtain ⟨v, hv, rfl⟩ := hu
    let vU : blockU X := ⟨v, hv⟩
    have hm : ambientUAction X y vU / vU ∈ blockFixed X :=
      QuotientGroup.eq_iff_div_mem.mp (hfix ⟨y, hy⟩ vU)
    refine ⟨(ambientUAction X y vU : X) / v, hm, ?_⟩
    change y * (v : H) * y⁻¹ / v = ⁅y, (v : H)⁆
    simp only [div_eq_mul_inv, commutatorElement_def]
  have hZX : ⁅Z, X⁆ = ⊥ := by
    have he : (⊤ : Subgroup X).map X.subtype = X := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [← he, ← map_commutator, commutator_center_left, Subgroup.map_bot]
  have hPU : ⁅(pCore 2 X).map X.subtype, U⁆ = ⊥ := by
    rw [← map_commutator,
      commutator_eq_bot_iff_le_centralizer.mpr hX.core_centralizes_blockU, Subgroup.map_bot]
  have h1 : ⁅⁅X, Y⁆, U⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [commutator_comm X Y]
    exact (commutator_mono hcore le_rfl).trans_eq hPU
  have h2 : ⁅⁅Y, U⁆, X⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hYU le_rfl).trans_eq hZX)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hUX : ⁅U, X⁆ = U := by
    have he : (⊤ : Subgroup X).map X.subtype = X := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [← he, ← map_commutator, ExceptionalRestrictions.short_commutator hX]
  rw [hUX, commutator_comm] at h3
  exact commutator_eq_bot_iff_le_centralizer.mp h3

end CFSG.Quasithin.ChapterC.ModuleCentralizer

namespace CFSG.Quasithin.ChapterC
open ModuleCentralizer
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The field-action and three-subgroup steps of C.1.10. This part does not
require two-perfection of Y, and allows an empty set of field-unit primes. -/
theorem IsShort.centralizes_blockU_of_coreQuotient (X Y : Subgroup H) [X.Normal]
    (hX : IsShort X)
    (hπ : piResidual (blockEndPrimes hX) Y ⊔ commutator Y = ⊤)
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype) :
    Y ≤ centralizer ((blockU X).map X.subtype : Set H) := by
  let := hX.elementary
  let := hX.module_elementary
  have hf := units_trivial X Y hX hπ (unitAction X Y hX hcore)
  apply centralizes_of_module_fixed X Y hX hcore
  intro y u
  have he := congrArg (fun z : (BlockEndRing hX)ˣ =>
    z.val (Additive.ofMul (QuotientGroup.mk' (blockFixed X) u))) (hf y)
  change Additive.ofMul (ambientModuleAction X y
      (QuotientGroup.mk' (blockFixed X) u)) =
    Additive.ofMul (QuotientGroup.mk' (blockFixed X) u) at he
  exact congrArg Additive.toMul he

/-- C.1.10: a two-perfect actor with the specified residual condition that
centralizes X/O₂(X) centralizes the entire normal short subgroup X. -/
theorem IsShort.centralizes_of_coreQuotient (X Y : Subgroup H) [X.Normal]
    (hX : IsShort X) (hY : IsPPerfect 2 Y)
    (hπ : piResidual (blockEndPrimes hX) Y ⊔ commutator Y = ⊤)
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype) :
    Y ≤ centralizer (X : Set H) :=
  hX.centralizes_of_coreQuotient_and_blockU X Y hY hcore
    (hX.centralizes_blockU_of_coreQuotient X Y hπ hcore)

end CFSG.Quasithin.ChapterC
