module
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition
public import Theory.ElementaryAbelian.Basic

/-!
# Dihedral order eight from a noncentral elementary four-subgroup

A group of order eight containing an elementary four-subgroup that is not
central is dihedral of order eight. The subgroup is supplied explicitly.

Choose a noncentral involution in the four-subgroup. Its centralizer
contains that four-subgroup and is proper, so has order four. The proved
involution-centralizer-four recognition theorem gives a dihedral or
semidihedral model. The semidihedral alternative has order at least sixteen;
the dihedral order formula then fixes its rotation parameter at four.

This elementary recognition supplies the final model in Stellmacher
(10.1)(a3), assertion (8), printed p.61 of
`refs/files/stellmacher-n-group.pdf`. The native edge quotient is separate.
-/

public theorem dihedral_eight_of_noncentral_elementary_four
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G=8)
    (K : Subgroup G) [IsElementaryAbelian 2 K] (hKcard : Nat.card K=4)
    (hK : ¬ K ≤ Subgroup.center G) : Nonempty (G ≃* DihedralGroup 4) := by
  classical
  obtain ⟨x,hxK,hxZ⟩ := SetLike.not_le_iff_exists.mp hK
  have hxne : x≠1 := by intro hx; exact hxZ (hx ▸ (Subgroup.center G).one_mem)
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=K) x hxK
  have hxorder : orderOf x=2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2) with hone | htwo
    · exact (hxne (orderOf_eq_one_iff.mp hone)).elim
    · exact htwo
  let C := Subgroup.centralizer ({x} : Set G)
  have hKC : K ≤ C := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm (s:=K) hk hxK
  have hlower : 4≤Nat.card C := hKcard ▸ Subgroup.card_le_of_le hKC
  have hupper : Nat.card C<8 := by
    by_contra hnot
    have hle : Nat.card C≤8 := hcard ▸ Nat.card_le_card_of_injective C.subtype C.subtype_injective
    have htop : C=⊤ := C.eq_top_of_card_eq (by omega)
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g∈C := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hCcard : Nat.card C=4 := by
    have hdiv : Nat.card C∣8 := hcard ▸ Subgroup.card_subgroup_dvd_card C
    interval_cases h : Nat.card C <;> norm_num at hdiv
    all_goals rfl
  have htwo : IsPGroup 2 G := IsPGroup.of_card (n:=3) hcard
  rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
    htwo x hxorder hxZ hCcard with ⟨m,⟨e⟩⟩ | ⟨n,hn,horder,_⟩
  · have hm : m=4 := by
      have hh := (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
      omega
    subst m
    exact ⟨e⟩
  · have hlower : 16≤2^n := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
