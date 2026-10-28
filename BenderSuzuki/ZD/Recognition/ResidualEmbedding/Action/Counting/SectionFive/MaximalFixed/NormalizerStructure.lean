module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.LocalData
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.Eligibility
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddContainment
public import BenderSuzuki.SE.StrongEmbeddingConjugacy
public import Theory.GroupTheory.InvolutionCentralizerLifting

/-!
# Normalizer structure in the contrary branch of Proposition 5.2

Let an odd subgroup P be normalized by a distinguished involution s but fail
to fix its unique fixed point. Any distinct commuting distinguished pair in
N_G(P) would absorb P into that point stabilizer by coprime four-group action.
Thus s is isolated in the full normalizer and Z-star makes its odd-core image
central. Local strong embedding in the distinguished-generated subgroup gives
conjugacy of all its distinguished involutions. Its image modulo the odd core
is consequently cyclic of order at most two. Injectivity on every four-group
then bounds the two-rank of the distinguished-generated subgroup by one.

The proof transports only the eligibility and conjugacy calculation to the
base point. The odd core, quotient map and rank calculation remain in the
original normalizer. Source: GLS, Volume 4, Chapter 2, Lemma 3.13 and the
paragraph preceding (5A), printed pp.33 and 40.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem fixes_mk_iff (x b : G) :
    x • (QuotientGroup.mk b : G ⧸ M) = QuotientGroup.mk b ↔ b⁻¹ * x * b ∈ M := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h

private theorem odd_le_stabilizer_of_commuting_distinguished
    (h : IsProductDisconnected Z M) (P : Subgroup G) (hodd : Odd (Nat.card P))
    {s t : G} (hs : s ∈ Z) (ht : t ∈ Z) (hne : s ≠ t) (hcomm : Commute s t)
    (hsN : s ∈ Subgroup.normalizer (P : Set G))
    (htN : t ∈ Subgroup.normalizer (P : Set G))
    {beta : G ⧸ M} (hsBeta : s • beta = beta) :
    P ≤ MulAction.stabilizer G beta := by
  induction beta using Quotient.inductionOn with
  | h b =>
    let e := MulAut.conj b⁻¹
    let Q := P.map e.toMonoidHom
    have hsM : e s ∈ M := by
      simpa [e, MulAut.conj_apply] using (fixes_mk_iff s b).mp hsBeta
    have hQN : ∀ x ∈ Subgroup.normalizer (P : Set G),
        e x ∈ Subgroup.normalizer (Q : Set G) := by
      intro x hx
      exact (Subgroup.le_normalizer_map (H := P) e.toMonoidHom)
        (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    have hQM : Q ≤ M := odd_le_of_commuting_distinguished h Q
      (by dsimp only [Q]; rw [Subgroup.card_map_of_injective e.injective]; exact hodd)
      (h.invariant _ _ hs) hsM (h.invariant _ _ ht)
      (fun he => hne (e.injective he)) (hcomm.map e.toMonoidHom)
      ((Subgroup.closure_le _).mpr (by
        intro x hx
        rcases hx with rfl | rfl
        · exact hQN s hsN
        · exact hQN t htN))
    intro x hx
    apply MulAction.mem_stabilizer_iff.mpr
    apply (fixes_mk_iff x b).mpr
    simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      hQM (Subgroup.mem_map_of_mem e.toMonoidHom hx)

private theorem normalizer_distinguished_conjugate
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    {s : G} (hs : s ∈ Z) (hsN : s ∈ Subgroup.normalizer (P : Set G))
    {beta : G ⧸ M} (hsBeta : s • beta = beta)
    (hnot : ¬ P ≤ MulAction.stabilizer G beta) :
    ∀ x ∈ Z, x ∈ Subgroup.normalizer (P : Set G) →
      ∀ y ∈ Z, y ∈ Subgroup.normalizer (P : Set G) →
      ∃ g : Subgroup.normalizer (P : Set G), MulAut.conj (g : G) x = y := by
  let N := Subgroup.normalizer (P : Set G)
  have hN : N ≠ ⊤ := by
    intro htop
    have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases r.simple.eq_bot_or_eq_top_of_normal P hn with hbot | htop
    · exact hnot (hbot ▸ bot_le)
    · have hsP : s ∈ P := htop ▸ Subgroup.mem_top s
      have hsI := BenderSuzuki.IsInvolution.subtype (h.involutions s hs) hsP
      have hord : orderOf (⟨s, hsP⟩ : P) = 2 :=
        orderOf_eq_prime hsI.sq_eq_one hsI.ne_one
      exact hodd.not_two_dvd_nat (hord ▸ orderOf_dvd_natCard (⟨s, hsP⟩ : P))
  induction beta using Quotient.inductionOn with
  | h b =>
    let e := MulAut.conj b⁻¹
    let F := N.map e.toMonoidHom
    have hF : F ≠ ⊤ := by
      intro htop
      have he := congrArg (Subgroup.comap e.toMonoidHom) htop
      rw [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at he
      exact hN he
    have hFM : ¬ F ≤ M := by
      intro hFM
      apply hnot
      intro x hx
      apply MulAction.mem_stabilizer_iff.mpr
      apply (fixes_mk_iff x b).mpr
      simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        hFM (Subgroup.mem_map_of_mem e.toMonoidHom (P.le_normalizer hx))
    have hsF : e s ∈ F := Subgroup.mem_map_of_mem e.toMonoidHom hsN
    have hsM : e s ∈ M := by
      simpa [e, MulAut.conj_apply] using (fixes_mk_iff s b).mp hsBeta
    have hSE := r.local_embedding F hF hFM ⟨e s, h.invariant _ _ hs, hsF, hsM⟩
    let C := Subgroup.closure (F.subtype ⁻¹' Z)
    intro x hx hxN y hy hyN
    have hxF : e x ∈ F := Subgroup.mem_map_of_mem e.toMonoidHom hxN
    have hyF : e y ∈ F := Subgroup.mem_map_of_mem e.toMonoidHom hyN
    let xF : F := ⟨e x, hxF⟩
    let yF : F := ⟨e y, hyF⟩
    have hxC : xF ∈ C := Subgroup.subset_closure (h.invariant _ _ hx)
    have hyC : yF ∈ C := Subgroup.subset_closure (h.invariant _ _ hy)
    let xC : C := ⟨xF, hxC⟩
    let yC : C := ⟨yF, hyC⟩
    have hxi : PFAppendixIII.IsInvolution xC :=
      BenderSuzuki.IsInvolution.subtype (BenderSuzuki.IsInvolution.subtype
        (h.involutions (e x) (h.invariant _ _ hx)) hxF) hxC
    have hyi : PFAppendixIII.IsInvolution yC :=
      BenderSuzuki.IsInvolution.subtype (BenderSuzuki.IsInvolution.subtype
        (h.involutions (e y) (h.invariant _ _ hy)) hyF) hyC
    obtain ⟨g, hg⟩ := hSE.involutions_conjugate hxi hyi
    obtain ⟨k, hk, hkEq⟩ := F.inv_mem (g : F).property
    refine ⟨⟨k, hk⟩, ?_⟩
    apply e.injective
    have he := congrArg (fun a : C => ((a : F) : G)) hg
    change (((g : F) : G))⁻¹ * e x * ((g : F) : G) = e y at he
    simp only [MulAut.conj_apply, map_mul, map_inv]
    have hkEq' : e k = (((g : F) : G))⁻¹ := hkEq
    rw [hkEq', inv_inv]
    exact he

/-- The local structure preceding (5A), at an arbitrary fixed point. -/
public theorem sectionFive_normalizerStructure_of_not_fixed
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    {s : G} (hs : s ∈ Z) (hsN : s ∈ Subgroup.normalizer (P : Set G))
    {beta : G ⧸ M} (hsBeta : s • beta = beta)
    (hnot : ¬ P ≤ MulAction.stabilizer G beta) :
    SectionFiveNormalizerStructure Z P := by
  let N := Subgroup.normalizer (P : Set G)
  let C := Subgroup.closure (N.subtype ⁻¹' Z)
  let sN : N := ⟨s, hsN⟩
  have hsi : PFAppendixIII.IsInvolution sN := BenderSuzuki.IsInvolution.subtype (h.disconnected.involutions s hs) hsN
  have hconj := normalizer_distinguished_conjugate h.disconnected r P hodd hs hsN hsBeta hnot
  have hiso : ∀ g : N, Commute (g * sN * g⁻¹) sN → g * sN * g⁻¹ = sN := by
    intro g hg
    apply Subtype.ext
    by_contra hne
    apply hnot
    apply odd_le_stabilizer_of_commuting_distinguished h.disconnected P hodd hs
      (h.disconnected.invariant (g : G) s hs) (Ne.symm hne)
      (show Commute s ((g : G) * s * (g : G)⁻¹) from
        (show Commute ((g : G) * s * (g : G)⁻¹) s from congrArg Subtype.val hg.eq).symm)
      hsN (show (g : G) * s * (g : G)⁻¹ ∈ N from
        N.mul_mem (N.mul_mem g.property hsN) (N.inv_mem g.property)) hsBeta
  obtain ⟨S, hsS, hc, hw⟩ := Glauberman.ZStar.isolated_involution_local_data sN
    (by simpa [pow_two] using hsi.sq_eq_one) hsi.ne_one hiso
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  have hcentral : q sN ∈ Subgroup.center (N ⧸ pPrimeCore 2 N) :=
    Glauberman.ZStar.glauberman_zstar_local S sN hsi hsS hc hw
  have hsame : ∀ x : N, (x : G) ∈ Z → q x = q sN := by
    intro x hx
    obtain ⟨g, hg⟩ := hconj s hs hsN x hx x.property
    have hgn : g * sN * g⁻¹ = x := Subtype.ext hg
    rw [← hgn, map_mul, map_mul, map_inv,
      Subgroup.mem_center_iff.mp hcentral (q g), mul_assoc, mul_inv_cancel, mul_one]
  have hC : C ≤ (Subgroup.zpowers (q sN)).comap q := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    change q x ∈ Subgroup.zpowers (q sN)
    rw [hsame x hx]
    exact Subgroup.mem_zpowers _
  refine ⟨?_, hconj, ?_⟩
  · rintro ⟨E, hEcard, hEsq⟩
    let EN := E.map C.subtype
    have hENcard : Nat.card EN = 4 := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact hEcard
    have hENp : IsPGroup 2 EN := IsPGroup.of_card (n := 2) (by omega)
    let f : EN → Subgroup.zpowers (q sN) := fun x => ⟨q (x : N), hC (by
      obtain ⟨y, hy, he⟩ := x.property
      rw [← he]
      exact y.property)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply IsPGroup.quotient_pPrimeCore_injective EN hENp
      exact congrArg Subtype.val hxy
    have hbound := Nat.card_le_card_of_injective f hf
    have hcyclic : Nat.card (Subgroup.zpowers (q sN)) ≤ 2 := by
      rw [Nat.card_zpowers]
      apply Nat.le_of_dvd (by decide)
      apply orderOf_dvd_of_pow_eq_one
      simpa only [← map_pow, map_one] using congrArg q hsi.sq_eq_one
    omega
  · intro x hx
    apply oddCore_sup_involution_centralizer
      (BenderSuzuki.IsInvolution.subtype (h.disconnected.involutions x hx) x.property)
    change q x ∈ Subgroup.center (N ⧸ pPrimeCore 2 N)
    rw [hsame x hx]
    exact hcentral

end BenderSuzuki.ZD
