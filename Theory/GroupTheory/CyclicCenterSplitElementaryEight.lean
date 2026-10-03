module
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A cyclic-center two-group split over an elementary group of order eight

A finite two-group with cyclic center has order at most64 when a normal
elementary subgroup A of order eight has a complement C. The supplied
subgroups and split hypotheses are retained; no action faithfulness or
complement order is assumed.

The kernel of conjugation by C on A is normal in the full group and
disjoint from A. Every nontrivial normal subgroup of a finite two-group
meets its center. Cyclicity of the center would therefore put its unique
involution in both the kernel and A, a contradiction. Thus C embeds in
Aut(A), whose order is168. Its two-power order is at most8, and the split
product formula gives the asserted bound.

This elementary group argument supplies the upper Sylow-order bound in
Stellmacher (8.6)(c), printed pp.41 and45 of the 1997 N-group paper. It
has no campaign dependencies.
-/

open scoped IsMulCommutative

public theorem card_le_sixtyfour_of_cyclic_center_split_elementary_eight
    {T : Type*} [Group T] [Finite T]
    (hT : IsPGroup 2 T) [IsCyclic (Subgroup.center T)]
    (A C : Subgroup T) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hgen : A ⊔ C = ⊤) (hdisjoint : A ⊓ C = ⊥) :
    Nat.card T ≤ 64 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 T) := ⟨hT⟩
  let N := C ⊓ Subgroup.centralizer (A : Set T)
  have hNnormal : N.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
        (Subgroup.centralizer_le_normalizer (N : Set T))
    · exact (le_inf C.le_normalizer Subgroup.le_normalizer_of_normal).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  let _ := hNnormal
  have hNbot : N = ⊥ := by
    by_contra hNne
    let _ : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
    let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a,hane,haZ⟩ := exists_nontrivial_center_mem_normal A (p := 2)
    obtain ⟨n,hnne,hnZ⟩ := exists_nontrivial_center_mem_normal N (p := 2)
    have haneT : (a:T) ≠ 1 := fun h => hane (Subtype.ext h)
    have hnneT : (n:T) ≠ 1 := fun h => hnne (Subtype.ext h)
    have haorder : orderOf (a:T) = 2 :=
      orderOf_eq_prime_iff.mpr ⟨by
        exact elemPow_eq_one_of_isElementaryAbelian (a:T) a.property,haneT⟩
    let z := (n:T) ^ (orderOf (n:T) / 2)
    have hzorder : orderOf z = 2 :=
      orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos (n:T))) (hT.dvd_orderOf hnneT)
    have hzZ : z ∈ Subgroup.center T := (Subgroup.center T).pow_mem hnZ _
    have heq : (⟨a,haZ⟩ : Subgroup.center T) = ⟨z,hzZ⟩ :=
      IsCyclic.eq_of_orderOf_eq_two (by simpa using haorder) (by simpa using hzorder)
    have haC : (a:T) ∈ C := (congrArg Subtype.val heq).symm ▸
      C.pow_mem n.property.1 _
    exact haneT (Subgroup.mem_bot.mp (hdisjoint ▸ ⟨a.property,haC⟩))
  have hCN : C ≤ Subgroup.normalizer (A : Set T) := Subgroup.le_normalizer_of_normal
  let action : C →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hCN)
  have hinj : Function.Injective action := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro c hc
    have hcent : (c:T) ∈ Subgroup.centralizer (A : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hh := congrArg (fun f : MulAut A => (f ⟨a,ha⟩ : T)) (MonoidHom.mem_ker.mp hc)
      change (c:T)*a*(c:T)⁻¹=a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply Subtype.ext
    exact (show (c:T) ∈ (⊥ : Subgroup T) from hNbot ▸ ⟨c.property,hcent⟩)
  have hdiv : Nat.card C ∣ 168 := by
    rw [← card_mulAut_of_elementary_eight A hA]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact action.range.card_subgroup_dvd_card
  obtain ⟨k,hk⟩ := (hT.to_subgroup C).exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra h
    have h16 : 16 ∣ 168 := (pow_dvd_pow 2 (show 4 ≤ k by omega)).trans (hk ▸ hdiv)
    norm_num at h16
  have hC : Nat.card C ≤ 8 := hk ▸ Nat.pow_le_pow_right (by decide) hk3
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A C hCN
  rw [hA,hdisjoint,Subgroup.card_bot,hgen,Subgroup.card_top,one_mul] at hprod
  omega
