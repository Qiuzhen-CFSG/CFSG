module

public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.CanonicalComplement
public import Theory.GroupTheory.CentralCoprimePrimeLift

/-!
# Reducing odd central splitting across the two-core

Suppose odd central extensions of Sₙ split. Then an odd central extension
of a finite group F with F/O₂(F) ≃ Sₙ has a characteristic complement to
its kernel.

Lift O₂(F) to a two-subgroup Q of the cover. Exact normalizer transport
makes Q normal, and the cover map is injective on Q. The induced extension
after quotienting by Q has kernel equal to the image of the original odd
central kernel. Pulling back a complement in this quotient gives an actual
complement in the cover. The canonical-complement theorem then supplies
characteristicity.

This is the two-core reduction used for the local quotients S₅ and S₃ in
Aschbacher–Smith, E.4.3(2), printed pp. 241–242, combined manuscript of
1 March 2004. Symmetric-group splitting remains an explicit hypothesis;
this module does not assert that splitting or the full source theorem.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound.OddCoverLifting
open Subgroup
universe u

/-- Splitting odd central extensions of Sₙ suffices to split odd central
extensions of groups with symmetric two-core quotient, with a characteristic
complement in the cover. -/
theorem oddCentralSplitting_of_symmetricOddCentralSplitting
    {n : ℕ} (hsplit : SymmetricOddCentralSplitting.{u} n) :
    OddCentralSplitting.{u} n := by
  intro E F _ _ _ _ f hf hc hodd e
  obtain ⟨Q, _, hQmap, hQnorm, _, hQinj⟩ :=
    exists_prime_lift_of_central_coprime f hf hc hodd.coprime_two_left
      (pCore 2 F) pCore_isPGroup
  let : Q.Normal := normalizer_eq_top_iff.mp (by
    rw [← hQnorm, normalizer_eq_top, comap_top])
  let q := QuotientGroup.mk' Q
  let g₀ := (QuotientGroup.mk' (pCore 2 F)).comp f
  have hg₀ : Function.Surjective g₀ :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hk₀ : g₀.ker = Q ⊔ f.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', ← hQmap, comap_map_eq]
  have hQker : Q ≤ g₀.ker := hk₀ ▸ le_sup_left
  let g := QuotientGroup.lift Q g₀ hQker
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective Q g₀ hg₀ hQker
  have hk : g.ker = f.ker.map q := by
    rw [QuotientGroup.ker_lift, hk₀, Subgroup.map_sup]
    rw [(Q.map_eq_bot_iff (f := q)).mpr (by simp [q]), bot_sup_eq]
  have hgc : g.ker ≤ center (E ⧸ Q) := by
    rw [hk]
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Q y
    change q w * q z = q z * q w
    simpa only [map_mul] using congrArg q (mem_center_iff.mp (hc hz) w)
  have hgo : Odd (Nat.card g.ker) := by
    rw [hk]
    exact hodd.of_dvd_nat (f.ker.card_map_dvd q)
  have hks : (e.toMonoidHom.comp g).ker = g.ker :=
    MonoidHom.ker_comp_of_injective g e.toMonoidHom e.injective
  obtain ⟨B, hB⟩ := hsplit (E ⧸ Q) (e.toMonoidHom.comp g)
    (e.surjective.comp hg) (hks ▸ hgc) (hks ▸ hgo)
  have hB' : g.ker.IsComplement' B := hks ▸ hB
  let D := B.comap q
  have hQD : Q ≤ D := by
    intro x hx
    change q x ∈ B
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact B.one_mem
  have hdis : Disjoint f.ker D := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxk, hxD⟩
    have hqx : q x = 1 := hB'.disjoint.le_bot
      ⟨hk ▸ mem_map_of_mem q hxk, hxD⟩
    have hxQ : x ∈ Q := (QuotientGroup.eq_one_iff x).mp hqx
    have hx : (⟨x, hxQ⟩ : Q) = 1 := hQinj (by
      change f x = f 1
      rw [show f x = 1 from hxk, map_one])
    exact congrArg Subtype.val hx
  have hsup : f.ker ⊔ D = ⊤ := by
    apply map_injective_of_ker_le q
      (by simpa only [q, QuotientGroup.ker_mk'] using hQD.trans le_sup_right) le_top
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective Q)]
    change f.ker.map q ⊔ (B.comap q).map q = ⊤
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q), ← hk]
    exact hB'.sup_eq_top
  have hcomp : f.ker.IsComplement' D := by
    apply isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← normal_mul, hsup, coe_top]
  exact ⟨D, characteristic_complement_of_symmetric_twoCore f hf hc hodd e D hcomp,
    hcomp⟩

end Sporadic.Mathieu.M22ValueBound.OddCoverLifting
