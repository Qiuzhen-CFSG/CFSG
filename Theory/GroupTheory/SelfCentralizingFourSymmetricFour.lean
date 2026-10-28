module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A self-centralizing normal four-group in order twenty-four

A finite group of order twenty-four with a normal elementary abelian subgroup
`U` of order four and `C_G(U) ≤ U` is the symmetric group on four letters.
This is the order-twenty-four identification needed in the terminal step of
Stellmacher (8.2), Journal of Algebra 190 (1997), p. 38; see
`refs/latex/stellmacher-n-group.tex`.

The proof lets the group permute its Sylow `3`-subgroups. Faithfulness of the
conjugation action on `U`, together with the order-two stabilizer bound in
`MulAut U`, shows that a Sylow `3`-subgroup has no nontrivial fixed point in
`U` and cannot be normal. Sylow counting therefore gives exactly four such
subgroups. The kernel of their permutation action has trivial intersection
with `U`; normality then makes it centralize `U`, so self-centrality kills the
kernel. The resulting faithful action has order twenty-four and is thus an
isomorphism onto `Perm (Fin 4)`.
-/

open scoped IsMulCommutative

public theorem mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour
    {G : Type*} [Group G] [Finite G] (U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (hcent : Subgroup.centralizer (U : Set G) ≤ U) (hG : Nat.card G = 24) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  let P : Sylow 3 G := default
  have hfac : Nat.factorization 24 3 = 1 := by
    have hzero : padicValNat 3 8 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 24 Nat.prime_three,
      show (24 : ℕ) = 3 ^ 1 * 8 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  have hPcard : Nat.card P = 3 := by rw [P.card_eq_multiplicity, hG, hfac]; norm_num
  have hPU : Disjoint (P : Subgroup G) U :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hPcard, hU]; decide)
  let φ : P →* MulAut U := MulAut.conjNormal.comp (P : Subgroup G).subtype
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro p hp
    apply Subtype.ext
    apply hPU.le_bot
    refine ⟨p.property, hcent ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have heq := congrArg (fun f : MulAut U => (f ⟨u, hu⟩ : G))
      (MonoidHom.mem_ker.mp hp)
    change (p : G) * u * (p : G)⁻¹ = u at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hφcard : Nat.card φ.range = 3 :=
    (Nat.card_congr (Equiv.ofInjective φ hφinj).symm).trans hPcard
  have hUPcent : U ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) = ⊥ := by
    apply le_antisymm _ bot_le
    rintro u ⟨hu, huc⟩
    by_contra hu1
    let z : U := ⟨u, hu⟩
    have hz : z ≠ 1 := fun hz => hu1 (congrArg Subtype.val hz)
    have hfix : ∀ f ∈ φ.range, f z = z := by
      rintro f ⟨p, rfl⟩
      apply Subtype.ext
      change (p : G) * u * (p : G)⁻¹ = u
      rw [Subgroup.mem_centralizer_iff.mp huc p p.property, mul_inv_cancel_right]
    have hsmall := card_mulAut_subgroup_le_two_of_fixed_point hU z hz φ.range hfix
    rw [hφcard] at hsmall
    omega
  have hPnotnormal : ¬ (P : Subgroup G).Normal := by
    intro hnormal
    let _ : (P : Subgroup G).Normal := hnormal
    have hcomm := Subgroup.commutator_eq_bot_of_disjoint hPU
    have hle : (P : Subgroup G) ≤ U :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcent
    have hPbot : (P : Subgroup G) = ⊥ := le_antisymm
      (fun p hp => hPU.le_bot ⟨hp, hle hp⟩) bot_le
    have hc : Nat.card (P : Subgroup G) = 1 := by rw [hPbot]; simp
    omega
  have hPindex : (P : Subgroup G).index = 8 := by
    have hc := Subgroup.index_mul_card (H := (P : Subgroup G))
    rw [hPcard, hG] at hc
    omega
  have hcount : Nat.card (Sylow 3 G) = 4 := by
    have hd := P.card_dvd_index
    rw [hPindex] at hd
    have hm := card_sylow_modEq_one 3 G
    have hn1 : Nat.card (Sylow 3 G) ≠ 1 := by
      intro hn
      let _ : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn).1
      exact hPnotnormal (Sylow.normal_of_subsingleton P)
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (Sylow 3 G) ∣ 2 ^ 3 by exact hd)
    interval_cases k
    · norm_num at heq
      exact (hn1 heq).elim
    · norm_num at heq
      rw [heq] at hm
      exact (by decide : ¬ Nat.ModEq 3 2 1) hm |>.elim
    · norm_num at heq
      exact heq
    · norm_num at heq
      rw [heq] at hm
      exact (by decide : ¬ Nat.ModEq 3 8 1) hm |>.elim
  let ρ : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
  let K : Subgroup G := ρ.ker
  have hKnorm : K ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    intro k hk
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    have heq := Equiv.congr_fun (MonoidHom.mem_ker.mp hk) P
    exact heq
  have hKUP : ⁅K ⊓ U, (P : Subgroup G)⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    apply le_trans _ hPU.eq_bot.le
    apply le_inf
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hKnorm)
    · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans
        (Subgroup.commutator_le_left U (P : Subgroup G))
  have hKU : K ⊓ U = ⊥ := by
    apply le_antisymm _ bot_le
    exact (le_inf inf_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKUP)).trans hUPcent.le
  have hKbot : K = ⊥ := by
    let _ : K.Normal := inferInstance
    have hcomm : ⁅K, U⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_of_disjoint (disjoint_iff.mpr hKU)
    have hle : K ≤ U :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hcent
    apply le_antisymm _ bot_le
    exact (le_inf le_rfl hle).trans hKU.le
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hKbot
  have hcard : Nat.card G = Nat.card (Equiv.Perm (Sylow 3 G)) := by
    let _ : Fintype (Sylow 3 G) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Sylow 3 G)), Fintype.card_perm,
      ← Nat.card_eq_fintype_card, hcount, hG]
    decide
  have hρbij : Function.Bijective ρ := (Nat.bijective_iff_injective_and_card ρ).mpr ⟨hρinj, hcard⟩
  exact ⟨(MulEquiv.ofBijective ρ hρbij).trans
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hcount))⟩

