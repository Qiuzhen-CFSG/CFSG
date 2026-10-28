module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SplitDihedralCentralSupplement
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The natural action of a split Sylow extension of a triple A₆ cover

The odd central quotient identifies each component Sylow with D₈. A Sylow
C₂ × D₈ has a central involution outside this subgroup. The two-group
quotient and the ambient Sylow order make that involution generate the
extension. Its action on A₆ fixes a subgroup of order eight, whereas an
involution outside the natural S₆ has fixed subgroup D₁₀. Thus conjugation
on the original central quotient lies in the natural S₆.

Source: GLS3 5.2.7(a); Aschbacher–Smith F.6.18(8), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GLS3.Chapter5
namespace Theory.HexEvenExtension
variable {G : Type*} [Group G] [Finite G]

/-- Every Sylow of an odd central A₆ cover is dihedral of order eight. -/
theorem sylow_dihedral (K : Subgroup G)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hc : Odd (Nat.card (center K))) (S : Sylow 2 K) :
    Nat.card S = 8 ∧ Nonempty (S ≃* DihedralGroup 4) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact hc.coprime_two_left
  let U := S.mapSurjective hq
  let a := S.equivOfSurjectiveCoprime q hq hk U
  obtain ⟨b⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral U
  exact ⟨(Nat.card_congr a.toEquiv).trans
    (AlternatingSix.ShadowLocal.alternatingSylow_card U), ⟨a.trans b⟩⟩

/-- The actual split Sylow supplies an outer involution centralizing its
whole Sylow and generating the original normal extension. -/
theorem central_involution
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hc : Odd (Nat.card (center K))) :
    K.index = 2 ∧ ∃ t : G, t ∈ T ∧ orderOf t = 2 ∧ t ∉ K ∧
      K ⊔ zpowers t = ⊤ ∧ ∀ x ∈ (T : Subgroup G), t * x = x * t := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  obtain ⟨hS8, ⟨eS⟩⟩ := sylow_dihedral K e hc S
  let N : Subgroup T := K.subgroupOf (T : Subgroup G)
  let a : N ≃* S := {
    toFun := fun x => ⟨⟨x.val.val, x.property⟩, by rw [hS]; exact x.val.property⟩
    invFun := fun s => ⟨⟨s.val.val, by
      have hs : (s : K) ∈ (S : Subgroup K) := s.property
      change (s : K) ∈ (T : Subgroup G).subgroupOf K
      exact hS ▸ hs⟩, s.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hN : Nat.card (center N) = 2 := by
    rw [Nat.card_congr (centerCongr (a.trans eS)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  obtain ⟨z, hz, hzout, hzo⟩ :=
    exists_central_involution_outside_of_split_sixteen eT N hN
  let t : G := z
  have htout : t ∉ K := hzout
  have hT16 : Nat.card T = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num
  have hindex : K.index = 2 := by
    obtain ⟨n, hn⟩ := hquot.exists_card_eq
    change K.index = 2 ^ n at hn
    by_cases hn0 : n = 0
    · have htop : K = ⊤ := index_eq_one.mp (by simpa [hn0] using hn)
      exact (htout (htop ▸ mem_top t)).elim
    · by_cases hn1 : n = 1
      · simpa [hn1] using hn
      · have hn2 : 2 ≤ n := by omega
        have h8 : 8 ∣ Nat.card K := hS8 ▸ S.card_subgroup_dvd_card
        have h4 : 4 ∣ K.index := by rw [hn]; exact Nat.pow_dvd_pow 2 hn2
        have h32 : 32 ∣ Nat.card G := by
          simpa only [K.card_mul_index] using Nat.mul_dvd_mul h8 h4
        have hh := Nat.le_of_dvd (Nat.card_pos (α := T))
          (T.pow_dvd_card_of_pow_dvd_card (n := 5) h32)
        omega
  refine ⟨hindex, t, z.property, (orderOf_coe z).trans hzo, htout, ?_, ?_⟩
  · apply top_unique
    intro x _
    by_cases hx : x ∈ K
    · exact (show K ≤ K ⊔ zpowers t from le_sup_left) hx
    · have hxt : x * t⁻¹ ∈ K := by
        rw [K.mul_mem_iff_of_index_two hindex, K.inv_mem_iff]
        exact iff_of_false hx htout
      have hh := (K ⊔ zpowers t).mul_mem ((show K ≤ K ⊔ zpowers t from le_sup_left) hxt)
        ((show zpowers t ≤ K ⊔ zpowers t from le_sup_right) (mem_zpowers t))
      simpa using hh
  · intro x hx
    exact congrArg (fun w : T => (w : G)) (mem_center_iff.mp hz ⟨x, hx⟩).symm

/-- Conjugation on the literal central quotient. -/
@[expose] def quotientAction (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6)) :
    G →* MulAut (alternatingGroup (Fin 6)) :=
  (MulAut.centralQuotientAction e).comp MulAut.conjNormal

/-- Fixing the component Sylow excludes the exceptional A₆ automorphisms. -/
theorem involution_action_natural
    (T : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (t : G) (ht : t ^ 2 = 1)
    (hfix : ∀ x ∈ (T : Subgroup G), t * x = x * t) :
    quotientAction K e t ∈ naturalAlternatingAutomorphismSubgroup := by
  let β := quotientAction K e t
  by_cases he : β = 1
  · change β ∈ naturalAlternatingAutomorphismSubgroup
    rw [he]
    exact naturalAlternatingAutomorphismSubgroup.one_mem
  have hβ : orderOf β = 2 := orderOf_eq_prime
    (by change quotientAction K e t ^ 2 = 1; rw [← map_pow, ht, map_one]) he
  by_contra hout
  obtain ⟨b⟩ := a6_outsideNatural_involution_fixed_equiv_dihedral β hβ hout
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U := S.mapSurjective hq
  have hU : (U : Subgroup (alternatingGroup (Fin 6))) ≤ automorphismFixedSubgroup β := by
    rintro a ⟨k, hk, rfl⟩
    change MulAut.centralQuotientAction e (MulAut.conjNormal t : MulAut K)
      (e (QuotientGroup.mk' (center K) k)) = e (QuotientGroup.mk' (center K) k)
    rw [MulAut.centralQuotientAction_apply]
    congr 2
    apply Subtype.ext
    change t * (k : G) * t⁻¹ = k
    have hkT : (k : G) ∈ T := by
      change k ∈ (T : Subgroup G).subgroupOf K
      exact hS ▸ hk
    rw [hfix k hkT, mul_inv_cancel_right]
  have hd := card_dvd_of_le hU
  rw [AlternatingSix.ShadowLocal.alternatingSylow_card U,
    Nat.card_congr b.toEquiv, DihedralGroup.nat_card] at hd
  norm_num at hd

/-- Every ambient element acts through the natural symmetric subgroup. -/
theorem quotientAction_natural
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6))
    (hc : Odd (Nat.card (center K))) (g : G) :
    quotientAction K e g ∈ naturalAlternatingAutomorphismSubgroup := by
  obtain ⟨_, t, _, ht, _, hgen, hfix⟩ := central_involution T eT K hquot e hc
  have hle : K ⊔ zpowers t ≤ naturalAlternatingAutomorphismSubgroup.comap (quotientAction K e) := by
    apply sup_le
    · intro k hk
      refine ⟨(e (QuotientGroup.mk' (center K) ⟨k, hk⟩) : Equiv.Perm (Fin 6)), ?_⟩
      change MulAut.conjNormal _ = MulAut.centralQuotientAction e (MulAut.conjNormal k)
      rw [show (MulAut.conjNormal k : MulAut K) = MulAut.conj ⟨k, hk⟩ from MulAut.conjNormal_val (h := ⟨k, hk⟩),
        MulAut.centralQuotientAction_conj, MulAut.conjNormal_val]
    · apply zpowers_le.mpr
      exact involution_action_natural T K e t
        (ht ▸ pow_orderOf_eq_one t) hfix
  exact hle (hgen ▸ mem_top g)

end Theory.HexEvenExtension
