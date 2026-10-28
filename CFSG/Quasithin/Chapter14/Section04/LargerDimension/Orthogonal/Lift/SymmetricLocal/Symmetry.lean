module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Core
public import Theory.GroupTheory.CentralizerResidualProducts
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Identifying the exchanged orthogonal lift

Conjugation carries C_G(z), its two-core and the embedded center to
C_G(i), U^x and ⟨i⟩. The joint centralizer is unchanged on exchanging z
and i, hence so is its two-residual. Applying the elementary-lift theorem
to the exchanged moved section constructs an elementary subgroup of
order 64 normal in that joint centralizer. Once D is its two-core, equal
orders identify the two lifts and give normalization and the fixed line.

The exchanged moved rank and irreducibility remain explicit premises.
They require the source component-interchange argument; this file does
not infer them from a symmetry certificate or assert the full source result.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem conjugate_centralizer (z x : G) :
    conjugateCore (centralizer ({z} : Set G)) x =
      centralizer ({conjugateElement z x} : Set G) := by
  exact Theory.GroupTheory.map_centralizer_singleton (MulAut.conj x⁻¹) z

omit [Finite G] in
theorem diagonalResidual_symmetric (z x : G) :
    diagonalResidual (conjugateCore (centralizer ({z} : Set G)) x) z =
      diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) := by
  rw [conjugate_centralizer]
  unfold diagonalResidual
  rw [inf_comm]

omit [Finite G] in
theorem conjugateCore_eq_core (U : Subgroup G) (z x : G)
    (hU : (centralizer ({z} : Set G)).pCoreIn 2 = U) :
    (centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 = conjugateCore U x := by
  rw [← conjugate_centralizer, conjugateCore,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj x⁻¹).injective, hU]
  rfl


omit [Finite G] in
private theorem outside_of_moved_card
    (U : Subgroup G) [IsExtraspecial 2 U] (i : G)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16) : i ∉ U := by
  intro hi
  have hB : (⁅U,zpowers i⁆).subgroupOf U ≤ center U := by
    have hUU : ⁅U,U⁆ ≤ (center U).map U.subtype := by
      have hh := map_mono (f := U.subtype)
        (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
      simpa only [map_subtype_commutator] using hh
    intro u hu
    have hh := hUU ((commutator_mono le_rfl (zpowers_le.mpr hi)) hu)
    exact (mem_map_iff_mem U.subtype_injective).mp hh
  have he : ((⁅U,zpowers i⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using hB
  rw [he, Nat.card_unique] at hmoved
  norm_num at hmoved

omit [Finite G] in
theorem conjugateCore_center (U : Subgroup G) (z x : G)
    (hZ : (center U).map U.subtype = zpowers z) :
    (center (conjugateCore U x)).map (conjugateCore U x).subtype =
      zpowers (conjugateElement z x) := by
  rw [conjugateCore, ← map_embeddedCenter U _ (MulAut.conj x⁻¹).injective,
    hZ, MonoidHom.map_zpowers]
  rfl

/-- Once the exchanged moved section is constructed, the common intrinsic
core identifies the two lifts. In particular the conjugate-core normalization
and fixed line are deductions, not symmetry certificates. -/
theorem symmetric_lift_of_exchanged_moved_section
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓ centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
      centralizerLift U z (conjugateElement z x))
    (hmoved : Nat.card (((⁅conjugateCore U x,zpowers z⁆).subgroupOf (conjugateCore U x)).map
      (QuotientGroup.mk' (center (conjugateCore U x)))) = 16)
    (hirr : ∀ E : Subgroup G, zpowers (conjugateElement z x) ≤ E →
      E ≤ liftBase (conjugateCore U x) (conjugateElement z x) z →
      diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
        normalizer (E : Set G) →
      E = zpowers (conjugateElement z x) ∨
        E = liftBase (conjugateCore U x) (conjugateElement z x) z) :
    centralizerLift (conjugateCore U x) (conjugateElement z x) z =
      centralizerLift U z (conjugateElement z x) ∧
    conjugateCore U x ≤ normalizer (centralizerLift U z (conjugateElement z x) : Set G) ∧
    centralizerLift U z (conjugateElement z x) ⊓ centralizer (conjugateCore U x : Set G) =
      zpowers (conjugateElement z x) := by
  let V := conjugateCore U x
  let i := conjugateElement z x
  let K := diagonalResidual (centralizer ({z} : Set G)) i
  let C := centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)
  let D' := centralizerLift V i z
  let D := centralizerLift U z i
  let : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv
    (U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective)
    inferInstance
  have hi : orderOf i = 2 := by
    simpa only [i, conjugateElement, MulEquiv.orderOf_eq] using hz
  have hZi : (center V).map V.subtype = zpowers i := conjugateCore_center U z x hZ
  have hVi : (centralizer ({i} : Set G)).pCoreIn 2 = V := conjugateCore_eq_core U z x hUcore
  have hiV : centralizer ({i} : Set G) ≤ normalizer (V : Set G) := by
    rw [← hVi]
    exact (centralizer ({i} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (centralizer ({i} : Set G))))
  have hzi : z ∈ centralizer ({i} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
  have hzV : z ∈ normalizer (V : Set G) := hiV hzi
  have hKC : K ≤ C := map_subtype_le (pResidual 2 C)
  have hKV : K ≤ normalizer (V : Set G) := (hKC.trans inf_le_right).trans hiV
  have hKz : K ≤ centralizer ({z} : Set G) := hKC.trans inf_le_left
  obtain ⟨hD',hD'card,_,hA'card⟩ := centralizerLift_elementary_and_card V K i z hi hz
    hZi hzV hzi (outside_of_moved_card V z hmoved) hKV hKz hmoved hirr
  let : IsElementaryAbelian 2 D' := hD'
  have hD'C : D' ≤ C := by
    apply le_inf
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr
        ((D'.le_centralizer hd) z
          ((show zpowers z ≤ D' from le_sup_right.trans le_sup_left) (mem_zpowers z))).symm
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr
        ((D'.le_centralizer hd) i (mem_sup_right (mem_zpowers i))).symm
  have hCD' : C ≤ normalizer (D' : Set G) :=
    le_sup_left.trans (lift_normalized_by_residual_join_core V C i z hZi hzV
      (inf_le_right.trans hiV) inf_le_left hmoved)
  have hle : D' ≤ D := (le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D') hD'C hCD').trans (le_of_eq hDcore)
  have he : D' = D := eq_of_le_of_card_ge hle (by rw [hD'card, hDcard])
  refine ⟨he, ?_, ?_⟩
  · change V ≤ normalizer (D : Set G)
    rw [← he]
    exact le_sup_right.trans (lift_normalized_by_residual_join_core V K i z
      hZi hzV hKV hKz hmoved)
  · change D ⊓ centralizer (V : Set G) = zpowers i
    rw [← he]
    exact centralizerLift_fixed_line V i z hi hz hZi hzV hD' hA'card

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
