module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs

/-!
# The maximal abelian subgroup argument in the unitary branch

Choose an abelian two-subgroup centralizing a nondistinguished involution,
first maximizing its two-rank and then its order. A large abelian subgroup
of `M` supplies an involution outside the distinguished closure. Fusion
moves the chosen involution into the literal two-point stabilizer `D`.

Conjugation on the actual distinguished closure `Lᵤ` has a kernel of order
at most two on any two-subgroup, under the explicit Lemma 13.3 input.
The model's automorphism bounds then give rank at most `n+2`. The large
subgroup gives rank at least `2*n`, forcing `n=2`; maximal order and the
model's exceptional image bound give the contradiction `64 ≤ |Q| ≤ 32`.

The construction of the large subgroup, the centralizer bound and the
intrinsic unitary automorphism bounds remain explicit proof obligations.
Thus this is the endgame, not the completed source exclusion.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Section 13, (13A)–(13C) and the
paragraph following (13C); Chapter 4, Lemmas 3.4–3.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal conjugation action on `Lᵤ` transfers its automorphism
bounds to every abelian two-subgroup of the ambient `C_G(u)`. -/
public theorem abelian_centralizer_bounds (h : IsProductDisconnected Z M)
    {u : G} {n : ℕ} (hkernel : CentralizerTwoBound Z u)
    (hmodel : AutomorphismBounds (centralizerClosure Z u) n)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQa : IsMulCommutative Q)
    (hQC : Q ≤ centralizer ({u} : Set G)) :
    primeRank 2 Q ≤ n + 2 ∧ (n = 2 → 4 ≤ primeRank 2 Q → Nat.card Q ≤ 32) := by
  let L := centralizerClosure Z u
  have hCN : centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨h.invariant g x hx.1,
      (centralizer ({u} : Set G)).mul_mem
        ((centralizer ({u} : Set G)).mul_mem hg hx.2)
        ((centralizer ({u} : Set G)).inv_mem hg)⟩
  let f : Q →* MulAut L := L.normalizerMonoidHom.comp (inclusion (hQC.trans hCN))
  have hkC : f.ker.map Q.subtype ≤ centralizer (L : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : (inclusion (hQC.trans hCN) y) ∈ L.normalizerMonoidHom.ker := hy
    rw [normalizerMonoidHom_ker] at hy'
    exact hy'
  have hk : Nat.card f.ker ≤ 2 := by
    have hc := hkernel (f.ker.map Q.subtype) hkC ((hQ.to_subgroup f.ker).map Q.subtype)
    rwa [card_map_of_injective Q.subtype_injective] at hc
  let := hQa
  refine ⟨?_, ?_⟩
  · simpa only [Nat.add_assoc] using
      primeRank_le_succ_of_kernel_card_le_two f hk hmodel.rank
  · intro hn hr
    exact card_le_thirty_two_of_abelian_image_bound f hQ hk hr
      (hmodel.exceptional_order hn)

/-- A pair eligible for the source's lexicographic maximum (13A).
Fusion allows the nondistinguished involution to be chosen anywhere in `G`. -/
@[expose] public def Candidate (Z : Set G) (v : G) (Q : Subgroup G) : Prop :=
  PFAppendixIII.IsInvolution v ∧ v ∉ Z ∧ IsPGroup 2 Q ∧ IsMulCommutative Q ∧
    Q ≤ centralizer ({v} : Set G)

/-- The maximum exists since the ambient group and its subgroup lattice
are finite. The second maximization retains the first maximum. -/
public theorem exists_maximal_candidate (h : ∃ v Q, Candidate Z v Q) :
    ∃ v Q, Candidate Z v Q ∧
      (∀ w R, Candidate Z w R → primeRank 2 R ≤ primeRank 2 Q) ∧
      (∀ w R, Candidate Z w R → primeRank 2 R = primeRank 2 Q → Nat.card R ≤ Nat.card Q) := by
  classical
  let s : Set (G × Subgroup G) := {p | Candidate Z p.1 p.2}
  have hs : s.Nonempty := by
    obtain ⟨v, Q, hQ⟩ := h
    exact ⟨(v, Q), hQ⟩
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image s
    (fun p => primeRank 2 p.2) (Set.toFinite s) hs
  let t : Set (G × Subgroup G) := {q ∈ s | primeRank 2 q.2 = primeRank 2 p.2}
  obtain ⟨q, hq, hcard⟩ := Set.exists_max_image t
    (fun q => Nat.card q.2) (Set.toFinite t) ⟨p, hp, rfl⟩
  refine ⟨q.1, q.2, hq.1, ?_, ?_⟩
  · intro w R hR
    exact (hmax (w, R) hR).trans_eq hq.2.symm
  · intro w R hR hr
    exact hcard (w, R) ⟨hR, hr.trans hq.2⟩

/-- The large abelian subgroup has more involutions than the distinguished
closure has elements, so one of its involutions is nondistinguished. -/
public theorem LargeAbelianData.exists_candidate {n : ℕ} (d : LargeAbelianData M n)
    (hn : 0 < n) (hA : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) :
    ∃ v, Candidate Z v d.subgroup := by
  let R := d.subgroup
  let A := closure (Z ∩ (M : Set G))
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := R) (p := 2)
  let E' := E.map R.subtype
  have hcard : Nat.card E' = 2 ^ (2 * n) := by
    rw [card_map_of_injective R.subtype_injective, hEc, d.rank]
  have hnot : ¬ E' ≤ A := by
    intro hle
    have hc := card_le_of_le hle
    rw [hcard, hA] at hc
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    omega
  obtain ⟨v, hvE, hvA⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨x, hx, rfl⟩ := hvE
  have hxR : (x : G) ∈ R := x.property
  have hv : PFAppendixIII.IsInvolution (x : G) := by
    refine ⟨fun he => hvA (by change (x : G) ∈ A; rw [he]; exact A.one_mem), ?_⟩
    let := hE
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x hx)
  have hvZ : (x : G) ∉ Z := fun hxZ =>
    hvA (subset_closure ⟨hxZ, d.le_pointStabilizer hxR⟩)
  refine ⟨x, hv, hvZ, d.two_group, d.abelian, ?_⟩
  let := d.abelian
  intro y hy
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : R) x)

omit [Finite G] in
/-- Conjugation preserves eligibility, using the invariance of `Z`. -/
public theorem Candidate.conjugate (h : IsProductDisconnected Z M)
    {v : G} {Q : Subgroup G} (hQ : Candidate Z v Q) (g : G) :
    Candidate Z (MulAut.conj g v) (Q.map (MulAut.conj g).toMonoidHom) := by
  rcases hQ with ⟨hv, hvZ, hp, ha, hc⟩
  refine ⟨_root_.BenderSuzuki.IsInvolution.map_of_injective hv
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    ?_, hp.map _, ?_, ?_⟩
  · intro hz
    have hz' := h.invariant g⁻¹ _ hz
    apply hvZ
    simpa [MulAut.conj_apply, mul_assoc] using hz'
  · let := ha
    exact Q.map_isMulCommutative _
  · rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hc hx))

/-- The complete maximal-subgroup and numerical endgame, with the
geometric and intrinsic model inputs still explicit. The assembly owner
must construct all three inputs before asserting the Section 13 exclusion. -/
public theorem exclusion_of_local_data (h : IsProductDisconnected Z M)
    {t : G} {n : ℕ} (hn : 2 ≤ n)
    (hA : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ d ∈ residualPairStabilizer M t, IsConj v d)
    (hlarge : LargeAbelianData M n)
    (hkernel : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      CentralizerTwoBound Z u)
    (hmodel : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      AutomorphismBounds (centralizerClosure Z u) n) : False := by
  obtain ⟨v₀, hv₀⟩ := hlarge.exists_candidate (by omega) hA
  obtain ⟨v, Q, hQ, hmax, hmaxcard⟩ := exists_maximal_candidate
    ⟨v₀, hlarge.subgroup, hv₀⟩
  have hlow : 2 * n ≤ primeRank 2 Q := by
    simpa only [hlarge.rank] using hmax v₀ hlarge.subgroup hv₀
  obtain ⟨d, hd, hg⟩ := hfusion v hQ.1 hQ.2.1
  obtain ⟨g, hg⟩ := isConj_iff.mp hg
  have hg' : MulAut.conj g v = d := hg
  let Q' := Q.map (MulAut.conj g).toMonoidHom
  have hQ' : Candidate Z d Q' := hg' ▸ hQ.conjugate h g
  have he := Q.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hr : primeRank 2 Q = primeRank 2 Q' := primeRank_equiv 2 he
  have hc : Nat.card Q = Nat.card Q' := Nat.card_congr he.toEquiv
  have hb := abelian_centralizer_bounds h (hkernel d hd hQ'.1) (hmodel d hd hQ'.1)
    Q' hQ'.2.2.1 hQ'.2.2.2.1 hQ'.2.2.2.2
  have hn2 : n = 2 := by omega
  have hQrank : primeRank 2 Q = 2 * n := by omega
  have hlo : (2 ^ n) ^ 3 ≤ Nat.card Q := by
    simpa only [hlarge.card] using hmaxcard v₀ hlarge.subgroup hv₀
      (hlarge.rank.trans hQrank.symm)
  have hup : Nat.card Q ≤ 32 := hc ▸ hb.2 hn2 (by omega)
  norm_num [hn2] at hlo
  omega

end BenderSuzuki.ZD.UnitaryExclusion
