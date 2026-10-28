module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.FixedSize
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.SpecificGroups.PSL2.RankOneRoots

/-!
# Involutory action on the proper residual subgroup

Let `L = ⟨z,t,[O₂′(D),t]⟩` be proper and put `A = ⟨Z ∩ M⟩`.
An involution of `D` either centralizes `L`, or `L` and its actual fixed
subgroup are PSL₂ groups over a field and its square-root subfield. The
smaller field has order exactly `|C_A(v)| = 2^k`, with `k ≥ 2`.

The inner-action distinction follows directly from Lemma 12.2: an inner
representative differs from `v` by an element of `C_G(L) ≤ D`, so lies
in the odd-order group `D ∩ L`. Its induced automorphism has both odd order
and square one, hence is trivial. Suzuki automorphisms squaring to one are
inner, while an outer PSL₂ involution has the genuine subfield fixed group.
The normalizer-action equivalence transports this group to `L ∩ C_G(v)`.

To identify its parameter, choose a nonidentity `a ∈ C_A(v)`. In the larger
PSL₂ model, elementary abelianness and cardinality give `C_L(a) = A`.
Thus `C_{C_L(v)}(a) = C_A(v)`, and the smaller PSL₂ model gives its order.
`FixedSize` supplies the transfer argument excluding order two. No replacement
of `v` by a conjugate or assumption that `v` commutes with `t` is needed.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.2 and 12.4(b), and
`refs/KGroup/GLS4/Chapter4.tex`, Lemma 3.4(b,c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem inner_normalizer_action_eq_one
    (L D : Subgroup G) (hCD : centralizer (L : Set G) ≤ D)
    (hodd : Odd (Nat.card (D ⊓ L : Subgroup G)))
    (v : normalizer (L : Set G)) (hvD : (v : G) ∈ D)
    (hsq : (L.normalizerMonoidHom v) ^ 2 = 1)
    (hi : ∃ b : L, L.normalizerMonoidHom v = MulAut.conj b) :
    L.normalizerMonoidHom v = 1 := by
  obtain ⟨b, hb⟩ := hi
  have hc : (b : G)⁻¹ * (v : G) ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun hb (⟨x, hx⟩ : L))
    change (v : G) * x * (v : G)⁻¹ = (b : G) * x * (b : G)⁻¹ at he
    have he' := congrArg (fun y : G => (b : G)⁻¹ * y * (v : G)) he
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using he'.symm
  have hbD : (b : G) ∈ D := by
    have hh := D.mul_mem hvD (D.inv_mem (hCD hc))
    simpa only [mul_inv_rev, mul_inv_cancel_left, inv_inv] using hh
  have hbo : Odd (orderOf b) := by
    rw [← Subgroup.orderOf_coe b]
    exact hodd.of_dvd_nat ((D ⊓ L).orderOf_dvd_natCard ⟨hbD, b.property⟩)
  have hao : Odd (orderOf (L.normalizerMonoidHom v)) := by
    rw [hb]
    exact hbo.of_dvd_nat (orderOf_map_dvd MulAut.conj b)
  obtain ⟨k, hk⟩ := hao
  have hp := pow_orderOf_eq_one (L.normalizerMonoidHom v)
  rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul] at hp
  exact hp

private theorem binary_involution_centralizer_card {n : ℕ} (hn : 0 < n)
    (a : PSL2BinaryMatrixGroup n) (ha : PFAppendixIII.IsInvolution a) :
    Nat.card (centralizer ({a} : Set (PSL2BinaryMatrixGroup n))) = 2 ^ n := by
  obtain ⟨g, t, ht, hg, _, _⟩ := Theory.PSL2.involution_root_geometry a
    (orderOf_eq_prime ha.sq_eq_one ha.ne_one)
  let f := MulAut.conj g
  have hmem (x : PSL2BinaryMatrixGroup n) :
      x ∈ centralizer ({a} : Set (PSL2BinaryMatrixGroup n)) ↔
        f x ∈ Converse.PUnip (BinaryGaloisField n) := by
    rw [← Theory.PSL2.centralizer_root_eq ht, ← hg]
    simp only [mem_centralizer_singleton_iff, ← map_mul, f,
      (MulAut.conj g).injective.eq_iff]
  rw [Nat.card_congr (Equiv.subtypeEquiv f.toEquiv hmem), Converse.PUnip_card,
    Converse.card_binaryGaloisField n hn.ne']

omit [Finite G] in
private theorem relative_involution_centralizer_card
    (L : Subgroup G) {n : ℕ} (hn : 0 < n)
    (e : L ≃* PSL2BinaryMatrixGroup n) {a : G}
    (haL : a ∈ L) (ha : PFAppendixIII.IsInvolution a) :
    Nat.card (L ⊓ centralizer ({a} : Set G) : Subgroup G) = 2 ^ n := by
  let aL : L := ⟨a, haL⟩
  let f : (L ⊓ centralizer ({a} : Set G) : Subgroup G) ≃
      centralizer ({aL} : Set L) :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp x.property.2))⟩
      invFun := fun x => ⟨x.val, x.val.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmem (x : L) : x ∈ centralizer ({aL} : Set L) ↔
      e x ∈ centralizer ({e aL} : Set (PSL2BinaryMatrixGroup n)) := by
    simp only [mem_centralizer_singleton_iff, ← map_mul, e.injective.eq_iff]
  rw [Nat.card_congr f, Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hmem)]
  exact binary_involution_centralizer_card hn (e aL)
    (IsInvolution.map_of_injective (IsInvolution.subtype ha haL) e.toMonoidHom e.injective)

private theorem fixed_distinguished_card_of_linear_models
    (L A : Subgroup G) {v : G} (hAL : A ≤ L)
    [IsElementaryAbelian 2 A] {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hA : Nat.card A = 2 ^ n)
    (e : L ≃* PSL2BinaryMatrixGroup n)
    (f : (L ⊓ centralizer ({v} : Set G) : Subgroup G) ≃* PSL2BinaryMatrixGroup m)
    (hlarge : 2 < Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G)) :
    Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ m := by
  let F := A ⊓ centralizer ({v} : Set G)
  let C := L ⊓ centralizer ({v} : Set G)
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G)
    omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : F)
  have haA : (a : G) ∈ A := a.property.1
  have hai : PFAppendixIII.IsInvolution (a : G) := by
    refine ⟨fun hh => ha (Subtype.ext hh), ?_⟩
    exact congrArg A.subtype (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a, haA⟩ : A))
  have hAC : A ≤ L ⊓ centralizer ({(a : G)} : Set G) := by
    intro x hx
    refine ⟨hAL hx, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg A.subtype (mul_comm' (⟨x, hx⟩ : A) ⟨a, haA⟩)
  have hAeq : A = L ⊓ centralizer ({(a : G)} : Set G) := by
    apply eq_of_le_of_card_ge hAC
    rw [relative_involution_centralizer_card L hn e (hAL haA) hai, hA]
  have hF : F = C ⊓ centralizer ({(a : G)} : Set G) := by
    exact (congrArg (fun B : Subgroup G => B ⊓ centralizer ({v} : Set G)) hAeq).trans
      (inf_right_comm _ _ _)
  rw [show (A ⊓ centralizer ({v} : Set G) : Subgroup G) = F from rfl, hF]
  exact relative_involution_centralizer_card C hm f ⟨hAL haA, a.property.2⟩ hai

/-- GLS4, Chapter 2, Lemma 12.4(b), with the literal fixed subgroup and
its parameter measured by the fixed distinguished closure. -/
public theorem proper_residualGenerated_involution_action
    {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (residualGenerated M z t : Set G) ∨
        ∃ k : ℕ, 2 ≤ k ∧
          Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k ∧
          Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup (2 * k)) ∧
          Nonempty ((residualGenerated M z t ⊓ centralizer ({v} : Set G) : Subgroup G) ≃*
            PSL2BinaryMatrixGroup k) := by
  intro v hvD hv
  by_cases hc : v ∈ centralizer (residualGenerated M z t : Set G)
  · exact Or.inl hc
  right
  obtain ⟨n, hn, hmodels, hAL, hDN, _, _, _, hA, hcard, _, _, _, hCD,
    _, _, _, hK, _, hKcard, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let A := closure (Z ∩ (M : Set G))
  let vN : normalizer (L : Set G) := ⟨v, hDN hvD⟩
  let a := L.normalizerMonoidHom vN
  have hasq : a ^ 2 = 1 := by
    change (L.normalizerMonoidHom vN) ^ 2 = 1
    rw [← map_pow, show vN ^ 2 = 1 from Subtype.ext hv.sq_eq_one, map_one]
  have hodd : Odd (Nat.card (D ⊓ L : Subgroup G)) := by
    rw [← hK, hKcard]
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    have hp : 0 < 2 ^ n := by positivity
    apply Nat.odd_iff.mpr
    have hh := Nat.even_iff.mp he
    omega
  have houter : ¬ ∃ b : L, a = MulAut.conj b := by
    intro hi
    have he := inner_normalizer_action_eq_one L D hCD hodd vN hvD hasq hi
    have hk : vN ∈ L.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hk
    exact hc hk
  rcases hmodels with hlin | hsz
  · obtain ⟨e⟩ := hlin
    let b := MulAut.congr e a
    have hbsq : b ^ 2 = 1 := by simp only [b, ← map_pow, hasq, map_one]
    obtain ⟨m, hm, hnm, ⟨f⟩⟩ := Linear.outer_fixed_model hn b hbsq
      (fun hi => houter ((MulAut.congr_inner_iff e a).mp hi))
    let g : (L ⊓ centralizer ({v} : Set G) : Subgroup G) ≃* PSL2BinaryMatrixGroup m :=
      (L.normalizerFixedEquivCentralizer vN).symm.trans
        ((MulAut.fixedSubgroupCongr e a).trans f)
    have : IsElementaryAbelian 2 A := hA
    have hfixed := fixed_distinguished_card_of_linear_models L A hAL (by omega) hm
      hcard e g (proper_pair_involution_fixed_card_gt_two h r ha hz hzM ht htM hL heven hvD hv)
    obtain ⟨k, hk, hkcard⟩ :=
      proper_pair_involution_fixed_exponent h r ha hz hzM ht htM hL heven hvD hv
    have hkm : k = m := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hkcard.symm.trans hfixed)
    subst m
    refine ⟨k, hk, hkcard, ?_, ⟨g⟩⟩
    rw [← hnm]
    exact ⟨e⟩
  · obtain ⟨s, hs, _, ⟨e⟩⟩ := hsz
    have he : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, hasq, map_one]
    obtain ⟨b, hb, _⟩ := suzuki_involutoryAut_inner_and_twoRank s hs (MulAut.congr e a) he
    exact False.elim (houter ((MulAut.congr_inner_iff e a).mp ⟨b, hb⟩))

end BenderSuzuki.ZD
