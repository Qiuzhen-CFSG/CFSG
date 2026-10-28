module
public import Theory.GroupTheory.SylowAutomorphismPGroup
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Placing a cubic residual in a normalized component

Let A be two-perfect with A/O₂(A) of order three, normalized by an ambient
Sylow two-subgroup T. Suppose A and T normalize K, and automorphisms of
K/O₂(K) stabilizing a Sylow two-subgroup form a two-group. Then either
A≤K or K normalizes A.

If A is not contained in K, its normal intersection with K is a two-group.
Since T normalizes the intersection, it lies in T. Thus A normalizes T∩K
and acts trivially on K/O₂(K). The commutator lies in O₂(K), which normalizes
A, and recovering A as O²(A O₂(K)) gives the asserted normalization.

This uses relative normalization throughout. The source application is the
L₀ placement in Aschbacher--Smith 13.4.10(2), printed p.908.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_intersection_two
    (A K : Subgroup G) (hAK : A ≤ normalizer (K : Set G))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) : IsPGroup 2 (A ⊓ K : Subgroup G) := by
  let N := K.subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer hAK
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hcard : Nat.card A = 3 * 2^n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hc,hn]
  have hthree : ¬ 3 ∣ Nat.card N := by
    intro hd
    have hq : IsPGroup 2 (A ⧸ N) := by
      apply IsPGroup.of_card_dvd_pow (n := n)
      apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp
      rw [←hcard,card_eq_card_quotient_mul_card_subgroup N,mul_comm (Nat.card (A ⧸ N))]
      exact Nat.mul_dvd_mul hd (dvd_refl _)
    have he := hp N inferInstance hq
    apply hout
    intro a ha
    exact show (⟨a,ha⟩ : A) ∈ N from he.symm ▸ mem_top _
  have hN : IsPGroup 2 N := by
    apply IsPGroup.of_card_dvd_pow (n := n)
    have hd := N.card_subgroup_dvd_card
    rw [hcard] at hd
    exact (Nat.Coprime.dvd_mul_left (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm).mp hd
  have hm := hN.map A.subtype
  rwa [subgroupOf_map_subtype,inf_comm] at hm

/-- A cubic residual either lies in the normalized component or is normalized
by it, when the component quotient has two-group Sylow automorphism stabilizers. -/
theorem cubic_residual_le_or_normalized
    (T : Sylow 2 G) (A K : Subgroup G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hAK : A ≤ normalizer (K : Set G))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hstab : ∀ S : Sylow 2 (K ⧸ pCore 2 K),
      IsPGroup 2 (MulAction.stabilizer (MulAut (K ⧸ pCore 2 K))
        (S : Subgroup (K ⧸ pCore 2 K)))) :
    A ≤ K ∨ K ≤ normalizer (A : Set G) := by
  by_cases hle : A ≤ K
  · exact Or.inl hle
  right
  have hcap := cubic_intersection_two A K hAK hp hc hle
  have hcapT : A ⊓ K ≤ (T : Subgroup G) :=
    hcap.le_sylow_of_normalized T ((le_inf hTA hTK).trans inf_normalizer_le_normalizer_inf)
  have hcomm : ⁅A, (T : Subgroup G) ⊓ K⁆ ≤ A ⊓ K := le_inf
    (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hTA))
    ((commutator_mono le_rfl inf_le_right).trans
      (le_normalizer_iff_commutator_le_right.mp hAK))
  have hnS : A ≤ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (le_inf (hcomm.trans hcapT) (hcomm.trans inf_le_right))
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := QuotientGroup.mk' (pCore 2 K)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  let a : A →* MulAut (K ⧸ pCore 2 K) :=
    (normalizerQuotientAction K (pCore 2 K)).comp (inclusion hAK)
  have ha (x : A) (k : K) : a x (q k) =
      q (K.normalizerMonoidHom (inclusion hAK x) k) := by
    exact quotientAut_apply_mk _ _ _
  have hfix (x : A) : (R : Subgroup (K ⧸ pCore 2 K)).map (a x).toMonoidHom = R := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro y ⟨v,hv,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hv
    change a x (q k) ∈ (R : Subgroup (K ⧸ pCore 2 K))
    rw [ha]
    apply mem_map_of_mem
    rw [hS] at hk ⊢
    exact (le_normalizer_iff.mp hnS x.val x.property k.val ⟨hk,k.property⟩).1
  let f : A →* MulAction.stabilizer (MulAut (K ⧸ pCore 2 K))
      (R : Subgroup (K ⧸ pCore 2 K)) := a.codRestrict _ hfix
  have hf := hp.hom_eq_one_of_isPGroup (hstab R) f
  have htriv (x : A) : a x = 1 := congrArg Subtype.val (DFunLike.congr_fun hf x)
  have hcommQ : ⁅A,K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro x hx k hk
    let k' := K.normalizerMonoidHom (inclusion hAK ⟨x,hx⟩) ⟨k,hk⟩ * (⟨k,hk⟩ : K)⁻¹
    have he : q k' = 1 := by
      change q (K.normalizerMonoidHom (inclusion hAK ⟨x,hx⟩) ⟨k,hk⟩ * (⟨k,hk⟩ : K)⁻¹) = 1
      rw [map_mul,map_inv,←ha,htriv]
      simp
    exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff k').mp he)
  have hQnorm := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      (hTK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hres : (pResidual 2 A).map A.subtype = A := by
    rw [(pResidual_eq_top_iff 2 A).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  have hn := normalizes_residual_of_commutator_le_two K (T : Subgroup G) A
    (K.pCoreIn 2) hTA hQT (isPGroup_pCoreIn 2 K) hQnorm (by
      rw [hres,commutator_comm]
      exact hcommQ)
  rwa [hres] at hn
end Subgroup
