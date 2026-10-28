module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Core
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.Symmetry
public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# Joint-core restrictions on the exchanged involution

The centralizer of z in Uˣ is a normal two-subgroup of the common
centralizer and hence lies in D. If z belonged to Uˣ, the class-two
commutator map would force that centralizer to have order at least 256,
contradicting |D|=64. Since z lies in D, the containment is strict.
Orbit-stabilizer, followed by quotienting the commutator by the center,
then shows that the exchanged moved image has more than four elements.

These deductions use only the genuine common-core identity and the two
orders. They exclude the identity action and the rank-two swap, but do
not assert component interchange or irreducibility.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exchanged_centralizer_le_joint_core
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U) :
    conjugateCore U x ⊓ centralizer ({z} : Set G) ≤
      (centralizer ({z} : Set G) ⊓
        centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 := by
  let V := conjugateCore U x
  let i := conjugateElement z x
  let C := centralizer ({z} : Set G) ⊓ centralizer ({i} : Set G)
  have hVi : (centralizer ({i} : Set G)).pCoreIn 2 = V :=
    conjugateCore_eq_core U z x hUcore
  have hVCi : V ≤ centralizer ({i} : Set G) := hVi ▸ pCoreIn_le 2 _
  have hCiV : centralizer ({i} : Set G) ≤ normalizer (V : Set G) := by
    rw [← hVi]
    exact (centralizer ({i} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply le_pCoreIn_of_normalizes
    (((IsExtraspecial.isPGroup 2 U).map (MulAut.conj x⁻¹).toMonoidHom).to_le
      inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans hVCi))
  exact (le_inf (inf_le_right.trans hCiV)
    (inf_le_left.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

private theorem extraspecial_inner_centralizer_card_bound
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P] (a : P) :
    Nat.card P ≤ 2 * Nat.card (centralizer ({a} : Set P)) := by
  have hc : _root_.commutator P ≤ center P :=
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
  have hle : ⁅zpowers a, (⊤ : Subgroup P)⁆ ≤ center P :=
    (commutator_mono le_top le_rfl).trans hc
  have hb := card_le_of_le hle
  rw [IsExtraspecial.center_order_p 2 P] at hb
  calc
    Nat.card P = Nat.card (⁅zpowers a, (⊤ : Subgroup P)⁆ : Subgroup P) *
        Nat.card (centralizer ({a} : Set P)) :=
      (ClassTwo.card_commutator_mul_card_centralizer hc a).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hb

theorem exchanged_involution_not_mem_core
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x)) :
    z ∉ conjugateCore U x := by
  let V := conjugateCore U x
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective
  let : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hVcard : Nat.card V = 512 := (Nat.card_congr e.toEquiv).symm.trans hUcard
  have hCD : V ⊓ centralizer ({z} : Set G) ≤
      centralizerLift U z (conjugateElement z x) :=
    hDcore ▸ exchanged_centralizer_le_joint_core U z x hUcore
  intro hzV
  let a : V := ⟨z, hzV⟩
  have hmap : (centralizer ({a} : Set V)).map V.subtype ≤
      V ⊓ centralizer ({z} : Set G) := by
    apply le_inf (map_subtype_le _)
    rintro _ ⟨b, hb, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))
  have hsmall := (card_le_of_le (hmap.trans hCD))
  rw [← Nat.card_congr ((centralizer ({a} : Set V)).equivMapOfInjective
    V.subtype V.subtype_injective).toEquiv, hDcard] at hsmall
  have hlarge := extraspecial_inner_centralizer_card_bound a
  rw [hVcard] at hlarge
  omega

theorem exchanged_centralizer_card_lt
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x)) :
    Nat.card (conjugateCore U x ⊓ centralizer ({z} : Set G) : Subgroup G) < 64 := by
  have hCD : conjugateCore U x ⊓ centralizer ({z} : Set G) ≤
      centralizerLift U z (conjugateElement z x) :=
    hDcore ▸ exchanged_centralizer_le_joint_core U z x hUcore
  have hlt : conjugateCore U x ⊓ centralizer ({z} : Set G) <
      centralizerLift U z (conjugateElement z x) := by
    refine lt_of_le_of_ne hCD ?_
    intro he
    have hzD : z ∈ centralizerLift U z (conjugateElement z x) :=
      mem_sup_right (mem_zpowers z)
    rw [← he] at hzD
    exact exchanged_involution_not_mem_core U z x hUcore hUcard hDcard hDcore hzD.1
  rw [← hDcard]
  by_contra! hge
  exact (ne_of_lt hlt) (eq_of_le_of_card_ge hCD hge)

private theorem commutator_card_le_twice_quotient_image
    (V : Subgroup G) [IsExtraspecial 2 V] (a : G)
    (ha : a ∈ normalizer (V : Set G)) :
    Nat.card (⁅V,zpowers a⁆ : Subgroup G) ≤
      2 * Nat.card (((⁅V,zpowers a⁆).subgroupOf V).map
        (QuotientGroup.mk' (center V))) := by
  let B := (⁅V,zpowers a⁆).subgroupOf V
  have hBV : ⁅V,zpowers a⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr ha)
  have hidx : (center V).relIndex B =
      Nat.card (B.map (QuotientGroup.mk' (center V))) := by
    simpa only [QuotientGroup.ker_mk'] using relIndex_ker B (QuotientGroup.mk' (center V))
  have hc : Nat.card ((center V).subgroupOf B) ≤ 2 := by
    have hh := card_le_of_le (show B ⊓ center V ≤ center V from inf_le_right)
    rw [IsExtraspecial.center_order_p 2 V] at hh
    have he := Nat.card_congr (subgroupOfEquivOfLe
      (show B ⊓ center V ≤ B from inf_le_left)).toEquiv
    rw [inf_subgroupOf_left] at he
    exact he ▸ hh
  have he := ((center V).subgroupOf B).card_mul_index
  change Nat.card ((center V).subgroupOf B) * (center V).relIndex B = Nat.card B at he
  rw [hidx] at he
  calc
    Nat.card (⁅V,zpowers a⁆ : Subgroup G) = Nat.card B :=
      (Nat.card_congr (subgroupOfEquivOfLe hBV).toEquiv).symm
    _ = _ := he.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hc

theorem exchanged_moved_card_gt_four
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x)) :
    4 < Nat.card (((⁅conjugateCore U x,zpowers z⁆).subgroupOf (conjugateCore U x)).map
      (QuotientGroup.mk' (center (conjugateCore U x)))) := by
  let V := conjugateCore U x
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective
  let : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hVcard : Nat.card V = 512 := (Nat.card_congr e.toEquiv).symm.trans hUcard
  have hVi : (centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 = V :=
    conjugateCore_eq_core U z x hUcore
  have hzV : z ∈ normalizer (V : Set G) := by
    have hzC : z ∈ centralizer ({conjugateElement z x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
    rw [← hVi]
    exact ((centralizer ({conjugateElement z x} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hzC
  have hsmall := exchanged_centralizer_card_lt U z x hUcore hUcard hDcard hDcore
  change Nat.card (V ⊓ centralizer ({z} : Set G) : Subgroup G) < 64 at hsmall
  have hcount := card_le_commutator_card_mul_centralizer V z
  have hbound := commutator_card_le_twice_quotient_image V z hzV
  have hCcard : Nat.card ((centralizer ({z} : Set G)).subgroupOf V) =
      Nat.card (V ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    simpa only [inf_subgroupOf_left] using Nat.card_congr (subgroupOfEquivOfLe
      (show V ⊓ centralizer ({z} : Set G) ≤ V from inf_le_left)).toEquiv
  rw [hVcard, hCcard] at hcount
  by_contra! hle
  change Nat.card (((⁅V,zpowers z⁆).subgroupOf V).map
    (QuotientGroup.mk' (center V))) ≤ 4 at hle
  have hB : Nat.card (⁅V,zpowers z⁆ : Subgroup G) ≤ 8 := by omega
  have hh := hcount.trans (Nat.mul_le_mul_right _ hB)
  omega

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
