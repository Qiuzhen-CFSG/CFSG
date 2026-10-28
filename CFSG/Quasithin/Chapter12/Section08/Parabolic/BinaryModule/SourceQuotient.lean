module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryCore
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The elementary binary section in the source parabolic

The source commutator bound makes both U and its original g-conjugate
normalize E: their commutators with E lie in V_1 or V_1^g, both contained
in the actual seed V ≤ E. They generate I_2, so E is normalized by I_2.

The two-core S normalizes W=U∩S and its original conjugate X=W^g.
Consequently [W,X]≤W∩X=E. The source square bound on U and its conjugate
makes both factor images have exponent two. Actual products S=WX then
show every element of the literal S/E has square one, hence this quotient
is elementary abelian. No elementary quotient or module recognition is
assumed in the construction.

Source: Aschbacher--Smith 12.8.4 and 12.8.9(1)--(3), printed pp.851--853,
and the binary instance of G.2.3(6), printed p.334.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original two U-generators normalize the actual intersection E. -/
theorem binary_source_E_normalized
    (F : InvariantFlag T V n) [IsMulCommutative V] (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) :
    F.I₂ L ≤ normalizer (F.E g : Set G) := by
  have hgV : g ∈ normalizer (V : Set G) := F.P_le_seed_normalizer L hL hgP
  have hVE : V ≤ F.E g := F.seed_le_E_of_normalizes g hgV
  have hEU : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  have hEUg : F.E g ≤ conjugate F.U g :=
    inf_le_right.trans (map_mono (show F.W ≤ F.U from inf_le_left))
  have hUE : ⁅F.U, F.E g⁆ ≤ F.E g :=
    ((commutator_mono le_rfl hEU).trans hcomm).trans ((F.le_seed 1).trans hVE)
  have hconj : ⁅conjugate F.U g, conjugate F.U g⁆ ≤ conjugate (F.Vi 1) g := by
    simpa only [conjugate, map_commutator] using
      (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcomm)
  have hUgE : ⁅conjugate F.U g, F.E g⁆ ≤ F.E g :=
    ((commutator_mono le_rfl hEUg).trans hconj).trans
      ((conjugate_le_of_normalizes (F.le_seed 1) g hgV).trans hVE)
  rw [← hgen]
  exact sup_le (le_normalizer_iff_commutator_le_right.mpr hUE)
    (le_normalizer_iff_commutator_le_right.mpr hUgE)

/-- Normality in the literal two-core follows from the proved I_2-normalization. -/
theorem binary_source_E_normal_in_core
    (F : InvariantFlag T V n) [IsMulCommutative V] (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) :
    ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (F.I₂ L)).trans (F.binary_source_E_normalized L hL g hgP hgen hcomm))

/-- The actual source quotient is elementary abelian. The Normal instance is
constructed from the original source inputs, not supplied as a premise. -/
theorem binary_source_quotient_elementary
    (F : InvariantFlag T V n) [IsMulCommutative V] (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hnorm : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.U : Set G))
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1) :
    letI := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
    IsElementaryAbelian 2
      (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := by
  let S := (F.I₂ L).pCoreIn 2
  let N := (F.E g).subgroupOf S
  let : N.Normal := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
  change IsElementaryAbelian 2 (S ⧸ N)
  let q := QuotientGroup.mk' N
  have hgV : g ∈ normalizer (V : Set G) := F.P_le_seed_normalizer L hL hgP
  have hVE : V ≤ F.E g := F.seed_le_E_of_normalizes g hgV
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hW : F.U ⊓ S = F.W := by
    change F.U ⊓ (F.I₂ L).pCoreIn 2 = F.W
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hWS : F.W ≤ S := le_sup_left.trans hsplit.ge
  have hXS : F.X g ≤ S := le_sup_right.trans hsplit.ge
  have hSW : S ≤ normalizer (F.W : Set G) := by
    rw [← hW]
    exact (le_inf hnorm S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hnormal : normalizer (F.I₂ L : Set G) ≤ normalizer (S : Set G) :=
    normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
  have hSg : conjugate S g = S := (conjugate_eq_iff S g).mpr
    (hnormal (le_normalizer_conjugateSpanBy F.U (F.P L) hgP))
  have hSX : S ≤ normalizer (F.X g : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSW).trans
      (F.W.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate S g ≤ normalizer (F.X g : Set G) at hh
    rwa [hSg] at hh
  have hWX : ⁅F.W, F.X g⁆ ≤ F.E g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW))
      (le_normalizer_iff_commutator_le_right.mp (hWS.trans hSX))
  have hsqW : ∀ w ∈ F.W, w ^ 2 ∈ F.E g :=
    fun w hw => hVE (F.le_seed 1 (hsquare w (show w ∈ F.U from hw.1)))
  have hsqX : ∀ x ∈ F.X g, x ^ 2 ∈ F.E g := by
    rintro x ⟨w, hw, rfl⟩
    apply hVE
    apply conjugate_le_of_normalizes (F.le_seed 1) g hgV
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
      (hsquare w (show w ∈ F.U from hw.1))
    simpa only [conjugate, map_pow] using hh
  have hsq : ∀ a : S ⧸ N, a ^ 2 = 1 := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N a
    have hprod : (s : G) ∈ (F.W : Set G) * (F.X g : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hXS.trans hSW), ← hsplit]
      exact s.property
    obtain ⟨w, hw, x, hx, hwx⟩ := hprod
    let wS : S := ⟨w, hWS hw⟩
    let xS : S := ⟨x, hXS hx⟩
    have hs : wS * xS = s := Subtype.ext hwx
    have hqw : (q wS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqW w hw)
    have hqx : (q xS) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqX x hx)
    have hqcomm : Commute (q wS) (q xS) := by
      change q wS * q xS = q xS * q wS
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hWX (commutator_mem_commutator hw hx))
    change (q s) ^ 2 = 1
    rw [← hs, map_mul, hqcomm.mul_pow, hqw, hqx, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
