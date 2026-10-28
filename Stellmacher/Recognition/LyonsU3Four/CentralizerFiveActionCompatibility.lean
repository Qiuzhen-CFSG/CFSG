module

public import Stellmacher.Recognition.LyonsU3Four.ActionIndexFromLocalData
public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenAction

/-!
# The centralizer action as a cube of the normalizer action

Let N = N_G(S) and C = C_G(z), where z is a nonidentity element of Z(S).
The local normalizer N ∩ C centralizes all of Z(S), so it is normal in N.
Its maps into the two actual odd-core quotients have the same kernel,
namely its own odd core. Thus C/O₂′(C) identifies, preserving S, with the
centralizer of z in N/O₂′(N).

Choose the order-fifteen complement in the latter quotient. The embedding
C₅ → C₁₅ sending a generator to its cube gives an injective semidirect-product
map whose image centralizes z. The known order-five local quotient gives
equal cardinalities, making this map an isomorphism. Consequently the local
action is exactly the cube of this order-fifteen automorphism.

Source: Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), Lemma 1(c–d), pp. 372–373, and the local group used in Lemma 4.
-/

namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup

private theorem local_normalizer_normal
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    ((centralizer ({z} : Set G)).subgroupOf (normalizer (S : Set G))).Normal := by
  let N := normalizer (S : Set G)
  let C := centralizer ({z} : Set G)
  let f := (MulAut.characteristic (center S)).comp (S : Subgroup G).normalizerMonoidHom
  have he : C.subgroupOf N = f.ker := by
    ext n
    constructor
    · intro hn
      have hn' : (⟨(n : G), hn⟩ : C) ∈
          normalizer (centralizerSylow S hz : Set C) := by
        change (⟨(n : G), hn⟩ : C) ∈ normalizer ((S : Subgroup G).subgroupOf C : Set C)
        rw [← subgroupOf_normalizer_eq (sylow_le_involutionCentralizer S hz)]
        exact n.property
      have hnZ := local_normalizer_le_center_centralizer S h d hz hz1 hn'
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      apply Subtype.ext
      change (n : G) * (w.val : G) * (n : G)⁻¹ = (w.val : G)
      have hc := mem_centralizer_iff.mp hnZ (w.val : G) ⟨w.val, w.property, rfl⟩
      change (w.val : G) * (n : G) = (n : G) * (w.val : G) at hc
      rw [← hc, mul_inv_cancel_right]
    · intro hn
      obtain ⟨w, hw, hwz⟩ := hz
      have he := congrArg (fun a : center S => (a.val : G))
        (DFunLike.congr_fun hn (⟨w, hw⟩ : center S))
      change (n : G) * (w : G) * (n : G)⁻¹ = (w : G) at he
      change (w : G) = z at hwz
      rw [hwz] at he
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  rw [he]
  infer_instance

private theorem quotient_restriction_ker
    {H : Type*} [Group H] [Finite H] (K : Subgroup H) [K.Normal] :
    ((QuotientGroup.mk' (pPrimeCore 2 H)).comp K.subtype).ker = pPrimeCore 2 K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := (QuotientGroup.mk' (pPrimeCore 2 H)).comp K.subtype
  have he : f.ker = (pPrimeCore 2 H).comap K.subtype := by
    ext x
    exact QuotientGroup.eq_one_iff _
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [he]
    exact Nat.Coprime.of_dvd_right
      (card_comap_dvd_of_injective _ K.subtype K.subtype_injective)
      (pPrimeCore_coprime_card (p := 2))
  · rw [he]
    exact map_le_iff_le_comap.mp (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 K)

/-- The centralizer quotient embeds in the actual normalizer quotient as the
centralizer of the same central involution, preserving every supplied Sylow element. -/
public theorem exists_involutionCentralizer_normalizer_quotient_equiv
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (w : S) (hw : (w : G) = z) :
    ∃ e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
        centralizer ({sylowNormalizerQuotientMap S w} : Set
          (normalizer (S : Set G) ⧸ pPrimeCore 2 (normalizer (S : Set G)))),
      ∀ s : S, (e (involutionCentralizerQuotientMap S hz s)).val =
        sylowNormalizerQuotientMap S s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normalizer (S : Set G)
  let C := centralizer ({z} : Set G)
  let K := C.subgroupOf N
  let : K.Normal := local_normalizer_normal S h d hz hz1
  let qN := QuotientGroup.mk' (pPrimeCore 2 N)
  let qC := QuotientGroup.mk' (pPrimeCore 2 C)
  let i : K →* C :=
    { toFun := fun k => ⟨k.val.val, k.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : C => (x : G)) he))
  let fC := qC.comp i
  have hfC : Function.Surjective fC := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 C) x
    obtain ⟨o, ho, n, hn, rfl⟩ := d.involution_factorization z hz hz1 c
    have hnN : (n : G) ∈ N := by
      change n ∈ normalizer ((S : Subgroup G).subgroupOf C : Set C) at hn
      rw [← subgroupOf_normalizer_eq (sylow_le_involutionCentralizer S hz)] at hn
      exact hn
    refine ⟨⟨⟨n, hnN⟩, n.property⟩, ?_⟩
    change qC n = qC (o * n)
    have hoq : qC o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, hoq, one_mul]
  have hfCker : fC.ker = pPrimeCore 2 K := by
    have hc : Nat.Coprime 2 (Nat.card fC.ker) := by
      have he : fC.ker = (pPrimeCore 2 C).comap i := by
        ext k
        exact QuotientGroup.eq_one_iff _
      rw [he]
      exact Nat.Coprime.of_dvd_right (card_comap_dvd_of_injective _ i hi)
        (pPrimeCore_coprime_card (p := 2))
    have he := pPrimeCore_comap_eq_of_surjective_coprime 2 fC hfC hc
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at he
    exact he
  let fN := qN.comp K.subtype
  let D := centralizer ({sylowNormalizerQuotientMap S w} : Set (N ⧸ pPrimeCore 2 N))
  let g : K →* D := fN.codRestrict D (by
    intro k
    apply mem_centralizer_singleton_iff.mpr
    change qN k.val * qN (inclusion (S : Subgroup G).le_normalizer w) =
      qN (inclusion (S : Subgroup G).le_normalizer w) * qN k.val
    simp only [← map_mul]
    apply congrArg qN
    apply Subtype.ext
    change (k.val : G) * (w : G) = (w : G) * (k.val : G)
    rw [hw]
    exact mem_centralizer_singleton_iff.mp k.property)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 N) x.val
    let a := (S : Subgroup G).normalizerMonoidHom n
    have hfix : a w = w := by
      apply sylowNormalizerQuotientMap_injective S h
      change qN (n * inclusion (S : Subgroup G).le_normalizer w * n⁻¹) =
        sylowNormalizerQuotientMap S w
      rw [map_mul, map_mul, map_inv, hn]
      change x.val * sylowNormalizerQuotientMap S w * x.val⁻¹ = _
      rw [mem_centralizer_singleton_iff.mp x.property, mul_assoc, mul_inv_cancel, mul_one]
    have hnC : (n : G) ∈ C := by
      have he := congrArg Subtype.val hfix
      change (n : G) * (w : G) * (n : G)⁻¹ = (w : G) at he
      rw [hw] at he
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
    exact ⟨⟨n, hnC⟩, Subtype.ext hn⟩
  have hgker : g.ker = pPrimeCore 2 K := by
    have he : g.ker = fN.ker := by
      ext k
      exact Subtype.ext_iff
    rw [he]
    exact quotient_restriction_ker K
  let eC := QuotientGroup.liftEquiv (pPrimeCore 2 K) hfC hfCker.symm
  let eN := QuotientGroup.liftEquiv (pPrimeCore 2 K) hg hgker.symm
  refine ⟨eC.symm.trans eN, ?_⟩
  intro s
  let k : K := ⟨inclusion (S : Subgroup G).le_normalizer s,
    sylow_le_involutionCentralizer S hz s.property⟩
  have heC : eC (QuotientGroup.mk' (pPrimeCore 2 K) k) =
      involutionCentralizerQuotientMap S hz s := rfl
  change (eN (eC.symm (involutionCentralizerQuotientMap S hz s))).val = _
  rw [← heC, eC.symm_apply_apply]
  rfl

private def cubeEmbedding : Multiplicative (ZMod 5) →* Multiplicative (ZMod 15) :=
  AddMonoidHom.toMultiplicative
    (ZMod.lift 5 ⟨zmultiplesHom (ZMod 15) 3, by decide⟩)

private theorem cubeEmbedding_generator :
    cubeEmbedding (Multiplicative.ofAdd 1) = (Multiplicative.ofAdd (1 : ZMod 15)) ^ 3 := by
  change Multiplicative.ofAdd (ZMod.lift 5 _ (1 : ZMod 5)) = _
  rw [show (1 : ZMod 5) = ((1 : ℤ) : ZMod 5) from rfl, ZMod.lift_coe]
  rfl

private theorem cubeEmbedding_injective : Function.Injective cubeEmbedding := by
  decide

private theorem cubeEmbedding_cube (a : Multiplicative (ZMod 5)) :
    ∃ n : ℤ, cubeEmbedding a = (Multiplicative.ofAdd (1 : ZMod 15)) ^ (3 * n) := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective a.toAdd
  subst hn
  refine ⟨n, ?_⟩
  change Multiplicative.ofAdd (ZMod.lift 5 _ (n : ZMod 5)) = _
  rw [ZMod.lift_coe]
  change Multiplicative.ofAdd (n • (3 : ZMod 15)) = _
  apply Multiplicative.toAdd.injective
  change n • (3 : ZMod 15) = (3 * n) • (1 : ZMod 15)
  simp [zsmul_eq_mul, mul_comm]


/-- The actual involution-centralizer quotient uses the cube of an actual
order-fifteen Sylow automorphism, with the canonical Sylow embedding fixed. -/
public theorem exists_orderFifteen_centralizerFive_equiv
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 5) →* MulAut S),
      orderOf β = 15 ∧ α (Multiplicative.ofAdd (1 : ZMod 5)) = β ^ (3 : ℕ) ∧
      ∃ e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
        S ⋊[α] Multiplicative (ZMod 5),
        ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s := by
  classical
  obtain ⟨β, φ, hβ, hφ, eN, heN⟩ :=
    exists_orderFifteen_normalizer_equiv S h d.automizer_fifteen
  let α := φ.comp cubeEmbedding
  have hα : α (Multiplicative.ofAdd (1 : ZMod 5)) = β ^ (3 : ℕ) := by
    change φ (cubeEmbedding _) = _
    rw [cubeEmbedding_generator, map_pow, hφ]
  let w : S := ⟨z, centerImage_le S hz⟩
  have hw : w ∈ center S := by
    obtain ⟨s, hs, he⟩ := hz
    exact (show s = w from Subtype.ext he) ▸ hs
  have hfix (a : Multiplicative (ZMod 5)) : α a w = w := by
    have hc : MulAut.characteristic (center S) (β ^ (3 : ℕ)) = 1 := by
      rw [map_pow, ← order_fifteen_center_order S h β hβ]
      exact pow_orderOf_eq_one _
    have hwfix : (β ^ (3 : ℕ)) w = w :=
      congrArg Subtype.val (DFunLike.congr_fun hc (⟨w, hw⟩ : center S))
    obtain ⟨n, hn⟩ := cubeEmbedding_cube a
    have he : α a = (β ^ (3 : ℕ)) ^ n := by
      change φ (cubeEmbedding a) = _
      rw [hn, map_zpow, hφ, zpow_mul]
      rfl
    rw [he]
    exact smul_eq_self_of_mem_zpowers (show (β ^ (3 : ℕ)) ^ n ∈ zpowers (β ^ (3 : ℕ)) from
      mem_zpowers_iff.mpr ⟨n, rfl⟩) (a := w) hwfix
  obtain ⟨eC, heC⟩ := exists_involutionCentralizer_normalizer_quotient_equiv
    S h d hz hz1 w rfl
  let j : S ⋊[α] Multiplicative (ZMod 5) →* S ⋊[φ] Multiplicative (ZMod 15) :=
    SemidirectProduct.map (MonoidHom.id S) cubeEmbedding (fun _ => rfl)
  have hj : Function.Injective j := by
    intro a b he
    apply SemidirectProduct.ext
    · exact congrArg (fun x : S ⋊[φ] Multiplicative (ZMod 15) => x.left) he
    · exact cubeEmbedding_injective (congrArg SemidirectProduct.right he)
  let D := centralizer ({sylowNormalizerQuotientMap S w} : Set
    (normalizer (S : Set G) ⧸ pPrimeCore 2 (normalizer (S : Set G))))
  let k : S ⋊[α] Multiplicative (ZMod 5) →* D :=
    (eN.symm.toMonoidHom.comp j).codRestrict D (by
      intro a
      apply mem_centralizer_singleton_iff.mpr
      apply eN.injective
      simp only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        eN.apply_symm_apply, heN]
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
          SemidirectProduct.right_inl, map_one, MulAut.one_apply]
        change a.left * α a.right w = w * a.left
        rw [hfix]
        exact mem_center_iff.mp hw a.left
      · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
          mul_one, one_mul])
  let g := eC.symm.toMonoidHom.comp k
  have hg : Function.Injective g := by
    intro a b he
    apply hj
    apply eN.symm.injective
    exact congrArg Subtype.val (eC.symm.injective he)
  have hcard : Nat.card (S ⋊[α] Multiplicative (ZMod 5)) =
      Nat.card (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) := by
    obtain ⟨_, ψ, _, _, e, _⟩ := d.involution_quotient z hz hz1
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, SemidirectProduct.card]
  let e := MulEquiv.ofBijective g ((Nat.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩)
  refine ⟨β, α, hβ, hα, e.symm, ?_⟩
  intro s
  apply e.injective
  rw [e.apply_symm_apply]
  change involutionCentralizerQuotientMap S hz s = eC.symm (k (SemidirectProduct.inl s))
  apply eC.injective
  rw [eC.apply_symm_apply]
  apply Subtype.ext
  rw [heC]
  apply eN.injective
  change eN (sylowNormalizerQuotientMap S s) = eN (eN.symm (j (SemidirectProduct.inl s)))
  rw [eN.apply_symm_apply, heN]
  rfl

end Stellmacher.Recognition.LyonsU3Four
