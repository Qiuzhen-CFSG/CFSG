module
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.RadicalNormalizerModule
public import Theory.GroupAction.HomomorphismFixedKernel
public import Theory.GroupTheory.SmallTwoSectionActions
import all Theory.GroupTheory.SmallTwoSectionActions

/-!
# Pointwise centralizers at elementary index four

Let U be the self-centralizing elementary two-core of M, and let E be
M-invariant of index at most four in U. The pointwise centralizer of E
acts on U/E, with a two-group kernel because it fixes both layers.
The quotient action has order dividing 4!, so a three-free pointwise
centralizer is itself a two-group. Relative normality then places it in U.

This supplies the cubic exception at index four in the original Hermitian
nine-space application of Aschbacher--Smith 4.2.13 and 4.4.3,
printed pp.611--612,623. The proof-only import reuses the internal section
action of SmallTwoSectionActions; it does not expose that implementation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A three-free pointwise module centralizer with elementary core index
at most four is contained in that core. All normality is relative to M. -/
theorem centralizer_le_core_of_fixed_index_le_four_three_free
    (M U E : Subgroup G) [IsElementaryAbelian 2 U]
    (hcore : M.pCoreIn 2 = U) (hCU : centralizer (U : Set G) ≤ U)
    (_hEU : E ≤ U) (hi : E.relIndex U ≤ 4)
    (hME : M ≤ normalizer (E : Set G))
    (h3 : ¬ 3 ∣ Nat.card (centralizer (E : Set G))) :
    M ⊓ centralizer (E : Set G) ≤ U := by
  have hp : IsPGroup 2 U := hcore ▸ isPGroup_pCoreIn 2 M
  have hMU : M ≤ normalizer (U : Set G) := by
    rw [←hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  let C := M ⊓ centralizer (E : Set G)
  let E' := E.subgroupOf U
  let : E'.Normal := inferInstance
  let a : C →* MulAut U := U.normalizerMonoidHom.comp
    (inclusion (show C ≤ normalizer (U : Set G) from inf_le_left.trans hMU))
  have ha : IsPGroup 2 a.ker := by
    apply hp.comap_subtype.to_le
    intro c hc
    apply hCU
    intro u hu
    have he := congrArg (fun x : MulAut U => (x ⟨u,hu⟩ : G)) hc
    change (c : G) * u * (c : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let b := sectionAction C U E (inf_le_left.trans hMU) (inf_le_left.trans hME)
  let q := QuotientGroup.mk' E'
  have hk : IsPGroup 2 b.ker := by
    apply MonoidHom.isPGroup_of_fixes_kernel_and_quotient q
      (by rw [QuotientGroup.ker_mk']; exact hp.to_subgroup E')
      (a.comp b.ker.subtype) (ha.comap_subtype)
    · intro c u
      exact congrArg (fun f : MulAut (U ⧸ E') => f (q u)) c.property
    · intro c u
      apply Subtype.ext
      have hu : (u : U) ∈ E' := (QuotientGroup.eq_one_iff _).mp u.property
      change (c : G) * (u : G) * (c : G)⁻¹ = (u : G)
      rw [←c.val.property.2 (u : G) hu,mul_inv_cancel_right]
  have hb3 : ¬ 3 ∣ Nat.card b.range := by
    intro hd
    exact h3 (hd.trans ((card_dvd_of_surjective b.rangeRestrict b.rangeRestrict_surjective).trans
      (card_dvd_of_le (show C ≤ centralizer (E : Set G) from inf_le_right))))
  have hd : Nat.card b.range ∣ 24 := by
    have he : Nat.card (U ⧸ E') ≤ 4 := hi
    have hdaut := card_dvd_of_injective (MulAut.toPerm (U ⧸ E')) MulEquiv.toEquiv_injective
    rw [Nat.card_perm] at hdaut
    exact b.range.card_subgroup_dvd_card.trans
      (hdaut.trans (Nat.factorial_dvd_factorial he))
  have hb : IsPGroup 2 b.range := IsPGroup.of_card_dvd_pow (n := 3)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3 |>.symm |>.dvd_of_dvd_mul_right hd)
  have hCp : IsPGroup 2 C := by
    have hh := hb.comap_of_ker_isPGroup b hk
    have he : b.range.comap b = ⊤ := by
      apply top_unique
      intro c _
      exact ⟨c,rfl⟩
    rw [he] at hh
    exact hh.of_equiv (topEquiv : (⊤ : Subgroup C) ≃* C)
  rw [←hcore]
  apply le_pCoreIn_of_normalizes hCp inf_le_left
  exact (le_inf M.le_normalizer (hME.trans (normalizer_le_normalizer_centralizer E))).trans
    inf_normalizer_le_normalizer_inf
end Subgroup
