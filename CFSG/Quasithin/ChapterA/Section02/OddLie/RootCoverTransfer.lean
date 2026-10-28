module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.RootCoverTransfer.Lifting
public import Theory.GroupTheory.PResidual.CentralKernelTransfer
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.GroupTheory.PrimeRankComplementaryCentralizer

/-!
# Fundamental root lifts and complementary ranks in A.2.17

The root subgroup in G/Z(G) is specified by an actual SL₂ embedding.
Split its prescribed preimage projection using the ordinary and exceptional
cover arguments in `Lifting`. Transvection generation identifies the section
image with K = O^{r'}(K₀), including q = 3. A commutator homomorphism into
the central r'-kernel identifies the full centralizer preimage; functoriality
of the residual then gives J* = O^{r'}(C_{G/Z(G)}(K*)).

The central involution of K puts KJ in its original involution centralizer.
An order-s subgroup of K meets J trivially for odd s, because Z(K) has
order two. Thus 1 + m_s(J) ≤ m_s(KJ), which is the lower bound needed here
even when the defining field is not prime. Cyclic Sylow subgroups carry
the resulting rank-one bound to J*. The final consumer gives (*) for s = 3,r.

The input center conditions are exactly the oddness and defining-prime-free
conditions supplied by the earlier ambient analysis. No lift, centralizer
identity, or complementary rank bound is an input to the final theorem.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.17, printed p.39.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.RootCoverTransfer

variable {G H F : Type*} [Group G] [Group H] [Field F]

/-- The literal inverse image of the marked fundamental root subgroup. -/
@[expose] def rootPreimage (π : G →* H) (j : SL(2,F) →* H) : Subgroup G :=
  j.range.comap π

/-- The source root group K = O^{r'}(K₀), embedded in the original G. -/
@[expose] def rootResidual (r : ℕ) (π : G →* H) (j : SL(2,F) →* H) : Subgroup G :=
  (primeToResidual r (rootPreimage π j)).map (rootPreimage π j).subtype

/-- The source complementary group J = O^{r'}(C_G(K)), with its actual embedding. -/
@[expose] def complementaryResidual (r : ℕ) (K : Subgroup G) : Subgroup G :=
  (primeToResidual r (centralizer (K : Set G))).map (centralizer (K : Set G)).subtype

/-- Lift the prescribed root embedding and identify its image with the
prime-to-r residual of its actual preimage. -/
theorem exists_root_lift [Finite G] [Finite F]
    {r : ℕ} [Fact r.Prime] [CharP F r]
    (hF : Odd (Nat.card F)) (π : G →* H) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center G) (ho : Odd (Nat.card π.ker))
    (hr : Nat.Coprime r (Nat.card π.ker))
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    ∃ k : SL(2,F) →* G, Function.Injective k ∧ π.comp k = j ∧
      k.range = rootResidual r π j := by
  let P := rootPreimage π j
  let e := MonoidHom.ofInjective hj
  let q₀ : P →* j.range := π.subgroupComap j.range
  let q : P →* SL(2,F) := e.symm.toMonoidHom.comp q₀
  have hq (x : P) : j (q x) = π x := congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqs : Function.Surjective q :=
    e.symm.surjective.comp (π.subgroupComap_surjective_of_surjective j.range hπ)
  have hqker {x : P} (hx : x ∈ q.ker) : (x : G) ∈ π.ker := by
    change π x = 1
    rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
  have hqc : q.ker ≤ center P := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hc (hqker hx)) y)
  let a : q.ker →* π.ker := (P.subtype.comp q.ker.subtype).codRestrict _
    (fun x => hqker x.property)
  have hai : Function.Injective a := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : G)) h))
  have hdiv : Nat.card q.ker ∣ Nat.card π.ker := card_dvd_of_injective a hai
  obtain ⟨s, hs⟩ := exists_section_sl2 hF q hqs hqc (ho.of_dvd_nat hdiv)
    (hr.coprime_dvd_right hdiv)
  have hqs' (x) : q (s x) = x := DFunLike.congr_fun hs x
  have hsi : Function.Injective s := by
    intro x y h
    simpa only [hqs'] using congrArg q h
  have hres : primeToResidual r P = s.range :=
    primeToResidual_eq_range_of_central_section r q hqc (hr.coprime_dvd_right hdiv)
      s hs (Matrix.SL2.map_mem_primeToResidual r s)
  refine ⟨P.subtype.comp s, P.subtype_injective.comp hsi, ?_, ?_⟩
  · ext x
    change π (s x) = j x
    rw [← hq, hqs']
  · change (P.subtype.comp s).range = (primeToResidual r P).map P.subtype
    rw [hres, MonoidHom.map_range]

/-- The root residual has the genuine SL₂ isomorphism, compatibly with the
prescribed root embedding, and its image is exactly K₀*. -/
theorem rootResidual_equiv_and_image [Finite G] [Finite F]
    {r : ℕ} [Fact r.Prime] [CharP F r]
    (hF : Odd (Nat.card F)) (π : G →* H) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center G) (ho : Odd (Nat.card π.ker))
    (hr : Nat.Coprime r (Nat.card π.ker))
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    (∃ e : SL(2,F) ≃* rootResidual r π j,
      π.comp ((rootResidual r π j).subtype.comp e.toMonoidHom) = j) ∧
    (rootResidual r π j).map π = j.range := by
  obtain ⟨k, hk, hπk, hK⟩ := exists_root_lift hF π hπ hc ho hr j hj
  constructor
  · refine ⟨(MonoidHom.ofInjective hk).trans (MulEquiv.subgroupCongr hK), ?_⟩
    exact hπk
  · rw [← hK, MonoidHom.map_range, hπk]

/-- The full centralizer and then its prime-to-r residual transport through
the same map. This includes SL₂(3), by r-generation rather than perfectness. -/
theorem complementaryResidual_image [Finite G] [Finite F]
    {r : ℕ} [Fact r.Prime] [CharP F r]
    (hF : Odd (Nat.card F)) (π : G →* H) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center G) (ho : Odd (Nat.card π.ker))
    (hr : Nat.Coprime r (Nat.card π.ker))
    (j : SL(2,F) →* H) (hj : Function.Injective j) :
    (centralizer (j.range : Set H)).comap π =
        centralizer (rootResidual r π j : Set G) ∧
    (complementaryResidual r (rootResidual r π j)).map π =
        complementaryResidual r j.range := by
  obtain ⟨⟨e, he⟩, hmap⟩ := rootResidual_equiv_and_image hF π hπ hc ho hr j hj
  have hgen : primeToResidual r (rootResidual r π j) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := e.surjective x
    exact Matrix.SL2.map_mem_primeToResidual r e.toMonoidHom y
  have hC := comap_centralizer_map_eq_of_primeToResidual r π hc hr
    (rootResidual r π j) hgen
  rw [hmap] at hC
  refine ⟨hC, ?_⟩
  have hCm : (centralizer (rootResidual r π j : Set G)).map π =
      centralizer (j.range : Set H) := by
    rw [← hC, map_comap_eq_self_of_surjective hπ]
  unfold complementaryResidual
  rw [map_embedded_primeToResidual_of_hom, hCm]

/-- The order of SL₂ is divisible by three over every finite field. -/
private theorem three_dvd_card_sl2 [Finite F] : 3 ∣ Nat.card SL(2,F) := by
  rw [GorensteinWalter.sl2_card_formula F]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsq : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmod := Nat.mod_lt (Nat.card F) (by decide : 0 < 3)
  have hsqmod : Nat.card F ^ 2 % 3 = (Nat.card F % 3) ^ 2 % 3 := Nat.pow_mod _ _ _
  by_cases hzero : Nat.card F % 3 = 0
  · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hzero) _
  · have hres : Nat.card F ^ 2 % 3 = 1 := by
      have : Nat.card F % 3 = 1 ∨ Nat.card F % 3 = 2 := by omega
      rcases this with h | h <;> norm_num [h] at hsqmod ⊢ <;> exact hsqmod
    have hsub : (Nat.card F ^ 2 - 1) % 3 = 0 := by omega
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hsub) _

/-- The prime-rank obstruction from an embedded root, expressed on the
original involution centralizer and on any actual image of its complement. -/
theorem sl2_complementary_primeRank_le_one [Finite G] [Finite F]
    {r s : ℕ} [Fact r.Prime] [CharP F r] [Fact s.Prime]
    (hr : r ≠ 2) (hs : Odd s) (hF : Odd (Nat.card F))
    (k : SL(2,F) →* G) (hk : Function.Injective k)
    (J : Subgroup G) (hJ : J ≤ centralizer (k.range : Set G))
    (hdiv : s ∣ Nat.card SL(2,F))
    (hlocal : ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank s (centralizer ({z} : Set G)) ≤ 2)
    (f : J →* H) (hf : Function.Surjective f) :
    primeRank s J ≤ 1 ∧ primeRank s H ≤ 1 := by
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  obtain ⟨hz, hz2⟩ := Matrix.SpecialLinearGroup.map_neg_one_isInvolution hr k hk
  have hcenter : Nat.card (center k.range) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr (MonoidHom.ofInjective hk).symm).toEquiv]
    exact (GorensteinWalter.sl2ProjectiveProjection_ker F ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card F hF)
  have hc2 (x : center k.range) : x ^ 2 = 1 := by
    simpa only [hcenter] using (pow_card_eq_one' (x := x))
  have hKz : k.range ≤ centralizer ({k (-1)} : Set G) := by
    rintro x ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    simp
  exact Subgroup.complementary_primeRank_le_one hs k.range J hJ hc2
    ((Nat.card_congr (MonoidHom.ofInjective hk).toEquiv) ▸ hdiv)
    (k (-1)) ⟨-1, rfl⟩ hKz (hlocal _ hz hz2) f hf

/-- A.2.17's root and complementary-centralizer transfer, retaining the literal
central quotient of G. The multiplier and defining-core analysis supply only
the odd and defining-prime-free center assumptions, not any lift or rank result. -/
theorem central_quotient_root_transfer [Finite G] [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r]
    (hr : r ≠ 2) (hcard : Nat.card F = r ^ e)
    (ho : Odd (Nat.card (center G))) (hcop : Nat.Coprime r (Nat.card (center G)))
    (j : SL(2,F) →* (G ⧸ center G)) (hj : Function.Injective j)
    (hlocal : ∀ s : ℕ, s = 3 ∨ s = r → ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank s (centralizer ({z} : Set G)) ≤ 2) :
    let π := QuotientGroup.mk' (center G)
    let K := rootResidual r π j
    let J := complementaryResidual r K
    (∃ a : SL(2,F) ≃* K, π.comp (K.subtype.comp a.toMonoidHom) = j) ∧
      K.map π = j.range ∧
      (centralizer (j.range : Set (G ⧸ center G))).comap π = centralizer (K : Set G) ∧
      J.map π = complementaryResidual r j.range ∧
      e ≤ 2 ∧
      (primeRank 3 J ≤ 1 ∧ primeRank 3 (J.map π) ≤ 1) ∧
      (primeRank r J ≤ 1 ∧ primeRank r (J.map π) ≤ 1) := by
  let π := QuotientGroup.mk' (center G)
  have hπ := QuotientGroup.mk'_surjective (center G)
  have hc : π.ker ≤ center G := by rw [QuotientGroup.ker_mk']
  have ho' : Odd (Nat.card π.ker) := by rwa [QuotientGroup.ker_mk']
  have hcop' : Nat.Coprime r (Nat.card π.ker) := by rwa [QuotientGroup.ker_mk']
  have hF : Odd (Nat.card F) := by
    rw [hcard]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  obtain ⟨heq, hmap⟩ := rootResidual_equiv_and_image hF π hπ hc ho' hcop' j hj
  obtain ⟨hcent, hres⟩ := complementaryResidual_image hF π hπ hc ho' hcop' j hj
  obtain ⟨k, hk, hπk, hK⟩ := exists_root_lift hF π hπ hc ho' hcop' j hj
  let K := rootResidual r π j
  let J := complementaryResidual r K
  have hJK : J ≤ centralizer (k.range : Set G) := by
    rw [hK]
    exact map_subtype_le _
  have hbound (s : ℕ) [Fact s.Prime] (hs : Odd s) (hsr : s = 3 ∨ s = r)
      (hd : s ∣ Nat.card SL(2,F)) :
      primeRank s J ≤ 1 ∧ primeRank s (J.map π) ≤ 1 :=
    sl2_complementary_primeRank_le_one hr hs hF k hk J hJK hd (hlocal s hsr)
      (π.subgroupMap J) (π.subgroupMap_surjective J)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hrd : r ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula F, hcard]
    have he : e ≠ 0 := by
      intro he
      have hcF : 1 < Nat.card F := Finite.one_lt_card
      simp [he] at hcard
      omega
    exact dvd_mul_of_dvd_left (dvd_pow_self r he) _
  have he : e ≤ 2 := by
    let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
    obtain ⟨hz, hz2⟩ := Matrix.SpecialLinearGroup.map_neg_one_isInvolution hr k hk
    exact (Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hcard k hk).trans
      (hlocal r (Or.inr rfl) _ hz hz2)
  exact ⟨heq, hmap, hcent, hres, he,
    hbound 3 (by decide) (Or.inl rfl) three_dvd_card_sl2,
    hbound r ((Fact.out : r.Prime).odd_of_ne_two hr) (Or.inr rfl) hrd⟩

/-- The literal quotient-centralizer residual satisfies source A.2.17 (*).
This is the consumer interface for the classical and exceptional centralizer
models downstairs; all lifting and rank premises are discharged above. -/
theorem quotient_complementary_rank_bounds [Finite G] [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r]
    (hr : r ≠ 2) (hcard : Nat.card F = r ^ e)
    (ho : Odd (Nat.card (center G))) (hcop : Nat.Coprime r (Nat.card (center G)))
    (j : SL(2,F) →* (G ⧸ center G)) (hj : Function.Injective j)
    (hlocal : ∀ s : ℕ, s = 3 ∨ s = r → ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank s (centralizer ({z} : Set G)) ≤ 2) :
    primeRank 3 (complementaryResidual r j.range) ≤ 1 ∧
      primeRank r (complementaryResidual r j.range) ≤ 1 := by
  obtain ⟨_, _, _, hJ, _, ⟨_, h3⟩, ⟨_, hrank⟩⟩ :=
    central_quotient_root_transfer hr hcard ho hcop j hj hlocal
  change (complementaryResidual r (rootResidual r (QuotientGroup.mk' (center G)) j)).map
    (QuotientGroup.mk' (center G)) = complementaryResidual r j.range at hJ
  rw [hJ] at h3 hrank
  exact ⟨h3, hrank⟩

end CFSG.Quasithin.ChapterA.Section02.RootCoverTransfer
