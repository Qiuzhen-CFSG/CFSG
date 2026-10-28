module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.LinearSuzuki.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.Suzuki.BorelFieldQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Quadratic Cartan rigidity for Suzuki groups

For positive parameters, Sylow conjugacy and inner–field coverage put the
same given automorphism over the standard root group. Its inner factor is in
the root normalizer, hence disappears on the explicit Borel quotient. The
quadratic coefficient action is trivial, so disjointness of the original
complement and root group proves pointwise fixation.

At parameter zero the group has order twenty and its Sylow normalizer is
proper, hence has order four. Its odd-order subgroups are trivial, which
handles Sz(2) without invoking nondegenerate coverage.
Source: Aschbacher–Smith F.1.3(5), printed p.260, final paragraph.
-/

public section
open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
namespace CFSG.Quasithin.ChapterF.Source

private theorem suzuki_zero_rigidity : CartanQuadraticRigidity (SuzukiMatrixGroup 0) := by
  intro T D hDN ho _ _ a _ _ _ _ x hx
  let N := normalizer (T : Set (SuzukiMatrixGroup 0))
  have h4 : 4 ∣ Nat.card N := by
    have ht : 2 ^ 2 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card
      (by rw [suzukiZero_card]; decide)
    exact ht.trans (Subgroup.card_dvd_of_le (show (T : Subgroup _) ≤ N from le_normalizer))
  have hi : N.index ∣ 5 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4)
    have he := Nat.mul_dvd_mul_right h4 N.index
    simpa only [N.card_mul_index, suzukiZero_card] using he
  have hi5 : N.index = 5 := ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hi).resolve_left
    (fun he => (suzuki_rankOneSylowFacts 0 T).proper.ne (Subgroup.index_eq_one.mp he))
  have hc : Nat.card N = 4 := by
    have he := N.card_mul_index
    rw [hi5, suzukiZero_card] at he
    omega
  have hd : Nat.card D ∣ 2 ^ 2 := by
    have he : Nat.card D ∣ Nat.card N := Subgroup.card_dvd_of_le hDN
    simpa [hc] using he
  have he : Nat.card D = 1 := Nat.eq_one_of_dvd_coprimes (ho.pow_left 2) hd (dvd_refl _)
  have : Subsingleton D := (Nat.card_eq_one_iff_unique.mp he).1
  have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : D) 1)
  simp [hx1]

private theorem suzuki_positive_rigidity (m : ℕ) (hm : 0 < m) :
    CartanQuadraticRigidity (SuzukiMatrixGroup m) := by
  apply CartanQuadraticRigidity.of_standard (SuzukiRootSubgroup m) (SuzukiBorelSubgroup m)
    (suzuki_root_normalizer_eq_borel m)
  · intro T
    obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) T P
    exact ⟨MulAut.conj g, (congrArg Sylow.toSubgroup hg).trans hP⟩
  · intro D hDB _ hd hs a _ haU haD hquad
    obtain ⟨g, σ, hg⟩ := suzukiAut_eq_inner_mul_field m hm a
    have hgB : g ∈ SuzukiBorelSubgroup m := by
      rw [← suzuki_root_normalizer_eq_borel]
      apply mem_normalizer_iff_map_conj_eq.mpr
      have he : (MulAut.conj g * suzukiFieldAut m σ).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (suzukiFieldAut m σ).toMonoidHom := rfl
      rwa [hg, he, ← Subgroup.map_map, field_map_root] at haU
    let b := borelActor m ⟨g, hgB⟩ σ
    have hUB : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
      rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left
    exact MonoidHom.fixes_complement_of_quadratic_field_quotient
      (SuzukiRootSubgroup m) (SuzukiBorelSubgroup m) D hUB hDB hd hs
      (projection m hm) (projection_surjective m hm) (projection_ker m hm)
      a.toMonoidHom b.toMonoidHom
      (fun x => (borelActor_apply m ⟨g, hgB⟩ σ x).trans (MulEquiv.congr_fun hg.symm x))
      σ.toRingEquiv (projection_borelActor m hm ⟨g, hgB⟩ σ)
      (fun x hx => haD ▸ mem_map_of_mem a.toMonoidHom hx) hquad

/-- Intrinsic Cartan rigidity for every concrete Suzuki parameter, including zero. -/
theorem cartanQuadraticRigidity_suzuki_model (m : ℕ) :
    CartanQuadraticRigidity (SuzukiMatrixGroup m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact suzuki_zero_rigidity
  · exact suzuki_positive_rigidity m hm

/-- The Suzuki source alternative, with its actual matrix-model isomorphism. -/
theorem cartanQuadraticRigidity_suzuki {H : Type*} [Group H] [Finite H]
    (m : ℕ) (e : H ≃* SuzukiMatrixGroup m) : CartanQuadraticRigidity H :=
  CartanQuadraticRigidity.of_equiv e (cartanQuadraticRigidity_suzuki_model m)

end CFSG.Quasithin.ChapterF.Source
