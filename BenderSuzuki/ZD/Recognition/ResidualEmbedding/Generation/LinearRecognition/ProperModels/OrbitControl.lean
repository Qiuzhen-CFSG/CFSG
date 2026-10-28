module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.OrbitControl.Cosets
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.OrbitControl.OddCore

/-!
# The distinguished orbit and normalization of the residual subgroup

Write `D = M ∩ Mᵗ`, `O = O₂'(D)`, `K = [O, ⟨t⟩]`, and
`L = ⟨z, t, K⟩`. Local Z-star puts `[D, ⟨t⟩]` in the ambient image
of the relative odd core `O`. The odd-order inverted representatives of
`Z ∩ M` therefore lie in `I = {i ∈ O | iᵗ = i⁻¹}` and in `K`.
This proves `Z ∩ M = zᴵ` and `D = I C_D(z)`.

The commutators with `D` and with `O` coincide, so `D` normalizes `⟨t,K⟩`.
The factorization at `z` then shows that `D` normalizes `L`. The orbit
identity also puts `⟨Z ∩ M⟩` in `L`. These results need only product
disconnection; the final wrappers keep the proper-model hypotheses and
apply the containment to centralize the odd core of proper `L`.

Source: GLS, Volume 4, Chapter 2, Propositions 3.5, 3.6(c,d), 3.8(d),
and Lemma 3.10, printed pp.29–32; `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem square_mem_of_inverted {t k : G} (ht : PFAppendixIII.IsInvolution t)
    (hi : rightConjugateElem k t = k⁻¹) : ⁅k, t⁆ = k ^ 2 := by
  have he : t * k⁻¹ * t⁻¹ = k := by
    simpa [rightConjugateElem, ht.inv_eq_self, mul_assoc] using congrArg Inv.inv hi
  simp only [commutatorElement_def, mul_assoc, he, pow_two]

omit [Finite G] in
private theorem mem_of_square_mem_of_odd {k : G} (hk : Odd (orderOf k))
    {H : Subgroup G} (hs : k ^ 2 ∈ H) : k ∈ H := by
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := k) hk.coprime_two_left
  rw [← hn]
  exact H.pow_mem hs n

/-- The ambient image of the relative odd core has odd cardinality. -/
public theorem residualPairStabilizer_oddCore_card (M : Subgroup G) (t : G) :
    Odd (Nat.card ((pPrimeCore 2 (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype)) := by
  rw [card_map_of_injective Subtype.val_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))

/-- The actual inverted set of the odd core is contained in `K`. -/
public theorem residual_inverted_oddCore_mem_commutator {t k : G}
    (ht : PFAppendixIII.IsInvolution t)
    (hk : k ∈ peterfalviKSet
      ((pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype) t) :
    k ∈ residualCommutator M t :=
  IsStronglyEmbedded.mem_commutator_zpowers_of_mem_peterfalviKSet _
    (residualPairStabilizer_oddCore_card M t) ht hk

/-- Proposition 3.6(c), with an actual inverted odd-core conjugator. -/
public theorem distinguished_exists_inverted_oddCore_conjugator
    (h : IsProductDisconnected Z M) {z t y : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hy : y ∈ Z) (hyM : y ∈ M) :
    ∃ k : G, k ∈ peterfalviKSet
      ((pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype) t ∧ rightConjugateElem z k = y := by
  have hcore := residualPairStabilizer_commutator_le_oddCore h ht htM
  obtain ⟨k, hkD, hi, ho, he⟩ :=
    distinguished_exists_odd_inverted_conjugator h hz hzM ht htM hy hyM
  refine ⟨k, ⟨?_, hi⟩, he⟩
  apply mem_of_square_mem_of_odd ho
  rw [← square_mem_of_inverted (h.involutions t ht) hi]
  exact hcore (commutator_mem_commutator hkD (mem_zpowers t))

/-- The distinguished orbit is exactly the image of the actual odd-core
inverted set, with right conjugation as in the source. -/
public theorem distinguished_eq_inverted_oddCore_orbit
    (h : IsProductDisconnected Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    Z ∩ (M : Set G) = (fun k => rightConjugateElem z k) ''
      peterfalviKSet ((pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype) t := by
  ext y
  constructor
  · intro hy
    exact distinguished_exists_inverted_oddCore_conjugator
      h hz hzM ht htM hy.1 hy.2
  · rintro ⟨k, hk, rfl⟩
    have hkM : k ∈ M := by
      obtain ⟨a, _, rfl⟩ := hk.1
      exact a.property.1
    refine ⟨?_, M.mul_mem (M.mul_mem (M.inv_mem hkM) hzM) hkM⟩
    simpa [rightConjugateElem, MulAut.conj_apply] using h.invariant k⁻¹ z hz

/-- Closure containment in Lemma 3.10. -/
public theorem residualGenerated_contains_distinguishedClosure
    (h : IsProductDisconnected Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t := by
  apply (closure_le _).mpr
  intro y hy
  obtain ⟨k, hk, rfl⟩ := distinguished_exists_inverted_oddCore_conjugator
    h hz hzM ht htM hy.1 hy.2
  have hkL : k ∈ residualGenerated M z t :=
    mem_sup_right (residual_inverted_oddCore_mem_commutator (h.involutions t ht) hk)
  have hzL : z ∈ residualGenerated M z t :=
    mem_sup_left (mem_sup_left (mem_zpowers z))
  exact (residualGenerated M z t).mul_mem
    ((residualGenerated M z t).mul_mem ((residualGenerated M z t).inv_mem hkL) hzL) hkL

/-- Proposition 3.8(d): the factorization uses the inverted set, not its closure. -/
public theorem residualPairStabilizer_factor_at_distinguished
    (h : IsProductDisconnected Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    {d : G} (hd : d ∈ residualPairStabilizer M t) :
    ∃ i c : G, i ∈ peterfalviKSet
      ((pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype) t ∧
      c ∈ residualPairStabilizer M t ⊓ centralizer ({z} : Set G) ∧ d = i * c := by
  have hyZ : d * z * d⁻¹ ∈ Z := h.invariant d z hz
  have hyM : d * z * d⁻¹ ∈ M := M.mul_mem (M.mul_mem hd.1 hzM) (M.inv_mem hd.1)
  obtain ⟨k, hk, he⟩ := distinguished_exists_inverted_oddCore_conjugator
    h hz hzM ht htM hyZ hyM
  have hkD : k ∈ residualPairStabilizer M t := by
    obtain ⟨a, _, rfl⟩ := hk.1
    exact a.property
  refine ⟨k⁻¹, k * d, ⟨?_, ?_⟩, ⟨(residualPairStabilizer M t).mul_mem hkD hd, ?_⟩, by simp⟩
  · exact ((pPrimeCore 2 (residualPairStabilizer M t)).map _).inv_mem hk.1
  · simpa [rightConjugateElem, mul_assoc] using congrArg Inv.inv hk.2
  · apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : G => k * a * d) he
    simpa [rightConjugateElem, mul_assoc] using hh.symm

/-- The local Z-star input makes the commutator with all of `D` equal to `K`. -/
public theorem residualCommutator_eq_pair_commutator (h : IsProductDisconnected Z M) {t : G}
    (ht : t ∈ Z) (htM : t ∉ M) :
    residualCommutator M t = ⁅residualPairStabilizer M t, zpowers t⁆ := by
  have hi := h.involutions t ht
  have hcore := residualPairStabilizer_commutator_le_oddCore h ht htM
  apply le_antisymm
  · apply commutator_mono _ le_rfl
    rintro _ ⟨a, _, rfl⟩
    exact a.property
  · apply commutator_le.mpr
    intro d hd x hx
    have hxcase : x = 1 ∨ x = t := by
      classical
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx)
      have hn : n < 2 := by
        simpa only [Finset.mem_range, orderOf_eq_prime hi.2 hi.1] using hn
      interval_cases n <;> simp
    rcases hxcase with he | he
    · subst x
      simp
    · subst x
      apply residual_inverted_oddCore_mem_commutator hi
      refine ⟨hcore (commutator_mem_commutator hd (mem_zpowers t)), ?_⟩
      simp only [rightConjugateElem, commutatorElement_def, mul_inv_rev, inv_inv,
        hi.inv_eq_self]
      have htt : t * t = 1 := by simpa [pow_two] using hi.sq_eq_one
      simp [mul_assoc, htt]

/-- Proposition 3.6: `D = O₂'(D) C_D(t)`, with the odd core taken
inside `D` and then mapped into the ambient group. -/
public theorem residualPairStabilizer_factor_at_swapping (h : IsProductDisconnected Z M) {t : G}
    (ht : t ∈ Z) (htM : t ∉ M)
    {d : G} (hd : d ∈ residualPairStabilizer M t) :
    ∃ k c : G, k ∈ (pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype ∧
      c ∈ residualPairStabilizer M t ⊓ centralizer ({t} : Set G) ∧ d = k * c := by
  have hi := h.involutions t ht
  have hcore := residualPairStabilizer_commutator_le_oddCore h ht htM
  let O := (pPrimeCore 2 (residualPairStabilizer M t)).map
    (residualPairStabilizer M t).subtype
  let x := ⁅d, t⁆
  have hxO : x ∈ O := hcore (commutator_mem_commutator hd (mem_zpowers t))
  have hxo : Odd (orderOf x) := by
    have hh := (residualPairStabilizer_oddCore_card M t).of_dvd_nat
      (orderOf_dvd_natCard (⟨x, hxO⟩ : O))
    simpa using hh
  have hxi : rightConjugateElem x t = x⁻¹ := by
    have htt : t * t = 1 := by simpa [pow_two] using hi.sq_eq_one
    simp [x, rightConjugateElem, commutatorElement_def, hi.inv_eq_self, mul_assoc, htt]
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := x) hxo.coprime_two_left
  let k := x ^ n
  have hkO : k ∈ O := O.pow_mem hxO n
  have hki : rightConjugateElem k t = k⁻¹ := by
    have hi : MulAut.conj t⁻¹ x = x⁻¹ := by
      simpa [rightConjugateElem, MulAut.conj_apply] using hxi
    have hh : MulAut.conj t⁻¹ (x ^ n) = (x ^ n)⁻¹ := by
      rw [map_pow, hi, inv_pow]
    simpa [k, MulAut.conj_apply, rightConjugateElem] using hh
  have hk2 : k ^ 2 = x := by
    simpa only [k, ← pow_mul, Nat.mul_comm n 2] using hn
  have hcomm : ⁅k, t⁆ = ⁅d, t⁆ := (square_mem_of_inverted hi hki).trans hk2
  have hkD : k ∈ residualPairStabilizer M t := by
    exact Subgroup.map_subtype_le _ hkO
  refine ⟨k, k⁻¹ * d, hkO,
    ⟨(residualPairStabilizer M t).mul_mem
      ((residualPairStabilizer M t).inv_mem hkD) hd, ?_⟩, by simp⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun a : G => k⁻¹ * a * t * d) hcomm
  simpa [commutatorElement_def, mul_assoc] using hh.symm

/-- The subgroup generated by `t` and `K` is normalized by `D`. -/
public theorem residualPairStabilizer_normalizes_t_sup_commutator (h : IsProductDisconnected Z M) {t : G}
    (ht : t ∈ Z) (htM : t ∉ M) :
    residualPairStabilizer M t ≤ normalizer
      ((zpowers t ⊔ residualCommutator M t : Subgroup G) : Set G) := by
  rw [residualCommutator_eq_pair_commutator h ht htM]
  let D := residualPairStabilizer M t
  let B := zpowers t ⊔ ⁅D, zpowers t⁆
  apply le_normalizer_iff.mpr
  intro d hd x hx
  have hmap : B.map (MulAut.conj d).toMonoidHom ≤ B := by
    rw [Subgroup.map_sup]
    apply sup_le
    · apply map_le_iff_le_comap.mpr
      apply zpowers_le.mpr
      change MulAut.conj d t ∈ B
      rw [conj_eq_commutatorElement_mul]
      exact B.mul_mem (mem_sup_right (commutator_mem_commutator hd (mem_zpowers t)))
        (mem_sup_left (mem_zpowers t))
    · apply map_le_iff_le_comap.mpr
      intro a ha
      exact mem_sup_right ((mem_normalizer_iff.mp
        (normalizer_commutator_ge_left D (zpowers t) hd) a).mp ha)
  exact hmap (mem_map_of_mem _ hx)

/-- Normalization in Lemma 3.10 under product disconnection. -/
public theorem residualPairStabilizer_le_normalizer_residualGenerated_of_productDisconnected
    (h : IsProductDisconnected Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G) := by
  have hBn := residualPairStabilizer_normalizes_t_sup_commutator
    h ht htM
  intro d hd
  obtain ⟨i, c, hi, hc, rfl⟩ :=
    residualPairStabilizer_factor_at_distinguished h hz hzM ht htM hd
  apply (normalizer (residualGenerated M z t : Set G)).mul_mem
  · apply (residualGenerated M z t).le_normalizer
    exact mem_sup_right (residual_inverted_oddCore_mem_commutator (h.involutions t ht) hi)
  · have hcz : c ∈ normalizer (zpowers z : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [zpowers_eq_closure, centralizer_closure]
      exact hc.2
    change c ∈ normalizer ((zpowers z ⊔ zpowers t ⊔ residualCommutator M t : Subgroup G) : Set G)
    rw [sup_assoc]
    exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hcz, hBn hc.1⟩

/-- Lemma 3.10 in the proper-model branch, under the original source inputs.
The stronger theorem above shows that properness and evenness are not needed
for the orbit containment itself. -/
public theorem proper_residualGenerated_contains_distinguishedClosure
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (_hL : residualGenerated M z t ≠ ⊤)
    (_heven : Even (Nat.card (residualPairStabilizer M t))) :
    closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t :=
  residualGenerated_contains_distinguishedClosure h.disconnected hz hzM ht htM

/-- Lemma 3.10 supplies normalization in the proper-model branch, without
any additional orbit or factorization premise. -/
public theorem residualPairStabilizer_le_normalizer_residualGenerated
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (_hL : residualGenerated M z t ≠ ⊤)
    (_heven : Even (Nat.card (residualPairStabilizer M t))) :
    residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G) :=
  residualPairStabilizer_le_normalizer_residualGenerated_of_productDisconnected
    h.disconnected hz hzM ht htM

/-- The orbit containment discharges the extra premise of the existing
odd-core centralization step in Lemma 12.2. -/
public theorem proper_residualGenerated_oddCore_le_center
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    twoPrimeCore (residualGenerated M z t) ≤ center (residualGenerated M z t) :=
  residualGenerated_oddCore_le_center_of_distinguishedClosure_le
    h r ha hz hzM ht htM hL
    (proper_residualGenerated_contains_distinguishedClosure h r ha hz hzM ht htM hL heven)

end BenderSuzuki.ZD
