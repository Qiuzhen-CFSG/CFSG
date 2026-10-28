module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Basic
public import Theory.GroupAction.FourthPowerFixed
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The fixed distinguished subgroup has order greater than two

Put `A = ⟨Z ∩ M⟩`. Lemma 12.2 makes A elementary abelian of order at
least four. For an involution of D, the displacement subgroup on A is
contained in the fixed subgroup. If the fixed subgroup had at most two
elements, the rank-nullity count would force |A| = 4 and exactly two fixed
elements. The action would therefore be a transposition. Its sign gives a
nontrivial two-group image of M, contradicting the focal-transfer conclusion
`O²(M) = M` from fusion control and simplicity.

The public conclusions use the literal ambient intersection `A ∩ C_G(v)`.
In particular its order is `2^k` with `k ≥ 2`, excluding the fixed field of
order two before either automorphism or centralizer recognition is invoked.

Source: GLS4, Chapter 2, the first paragraph of the proof of Lemma 12.4
and Lemma 4.2(b), in `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup

private theorem fixed_card_gt_two_of_twoPerfect
    {H A : Type*} [Group H] [Finite H] [Group A] [Finite A]
    [IsElementaryAbelian 2 A]
    (hres : External.hallPResidual 2 H = ⊤) (hA : 4 ≤ Nat.card A)
    (f : H →* MulAut A) (v : H) (hv : v ^ 2 = 1) :
    2 < Nat.card (FixedPoints.subgroup (zpowers (f v)) A) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let a := f v
  let F := FixedPoints.subgroup (zpowers a) A
  have ha : a ^ 2 = 1 := by simp only [a, ← map_pow, hv, map_one]
  obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data a ha
  have hbound := card_le_of_le hle
  change Nat.card A = Nat.card F * Nat.card (commutatorAction (zpowers a) A) at hcount
  change Nat.card (commutatorAction (zpowers a) A) ≤ Nat.card F at hbound
  by_contra! hsmall
  have hF : Nat.card F = 2 := by nlinarith
  have hfour : Nat.card A = 4 := by nlinarith
  let p := MulAction.toPermHom (MulAut A) A
  let s : H →* ℤˣ := Equiv.Perm.sign.comp (p.comp f)
  have htwo : IsPGroup 2 ℤˣ := fun x => ⟨1, by simp⟩
  have hker := External.hallPResidual_le_ker_of_isPGroup s htwo
  rw [hres] at hker
  have hsign : Equiv.Perm.sign (p a) = 1 := MonoidHom.mem_ker.mp (hker (mem_top v))
  have hfix : Fintype.card {x : A // (p a) x = x} = 2 := by
    rw [← Nat.card_eq_fintype_card]
    calc
      _ = Nat.card F := Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        (MulAut.mem_fixed_zpowers_iff a x).symm)
      _ = 2 := hF
  have hsupp : (p a).support.card = 2 := by
    have hc := Fintype.card_subtype_compl (fun x : A => (p a) x = x)
    rw [hfix, ← Nat.card_eq_fintype_card (α := A), hfour] at hc
    simpa only [Fintype.card_subtype, Equiv.Perm.support] using hc
  have hminus : Equiv.Perm.sign (p a) = -1 :=
    (Equiv.Perm.card_support_eq_two.mp hsupp).sign_eq
  have : (1 : ℤˣ) = -1 := hsign.symm.trans hminus
  exact (by decide : (1 : ℤˣ) ≠ -1) this

/-- The source inequality `qᵥ > 2`, including the transfer exclusion of
`qᵥ = 2`; no local model or fixed-field premise is assumed. -/
public theorem proper_pair_involution_fixed_card_gt_two
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    2 < Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let A := closure (Z ∩ (M : Set G))
  let : IsElementaryAbelian 2 A := hA
  have hMN : M ≤ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer h.disconnected]
  let f : M →* MulAut A := A.normalizerMonoidHom.comp (inclusion hMN)
  let vM : M := ⟨v, hvD.1⟩
  let F := FixedPoints.subgroup (zpowers (f vM)) A
  have hmap : F.map A.subtype = A ⊓ centralizer ({v} : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have he := congrArg A.subtype ((MulAut.mem_fixed_zpowers_iff (f vM) a).mp ha)
      change v * (a : G) * v⁻¹ = (a : G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      apply (MulAut.mem_fixed_zpowers_iff (f vM) _).mpr
      apply Subtype.ext
      change v * x * v⁻¹ = x
      rw [← mem_centralizer_singleton_iff.mp hx.2, mul_assoc, mul_inv_cancel, mul_one]
  have hfour : 4 ≤ Nat.card A := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hF := fixed_card_gt_two_of_twoPerfect (r.linear_twoResidual_eq_top h.disconnected)
    hfour f vM (Subtype.ext hv.sq_eq_one)
  rw [← hmap, card_map_of_injective A.subtype_injective]
  exact hF

/-- The exponent of the actual fixed distinguished subgroup is at least two.
This supplies the parameter restriction in Lemma 12.4(b,c). -/
public theorem proper_pair_involution_fixed_exponent
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    ∃ k : ℕ, 2 ≤ k ∧
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let A := closure (Z ∩ (M : Set G))
  let C := A ⊓ centralizer ({v} : Set G)
  let : IsElementaryAbelian 2 A := hA
  have hp : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (inclusion (show C ≤ A from inf_le_left)) (inclusion_injective _)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hlarge := proper_pair_involution_fixed_card_gt_two h r ha hz hzM ht htM hL heven hvD hv
  change 2 < Nat.card C at hlarge
  refine ⟨k, ?_, hk⟩
  by_contra! hsmall
  have hle := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : k ≤ 1)
  rw [← hk] at hle
  norm_num at hle
  omega

end BenderSuzuki.ZD
