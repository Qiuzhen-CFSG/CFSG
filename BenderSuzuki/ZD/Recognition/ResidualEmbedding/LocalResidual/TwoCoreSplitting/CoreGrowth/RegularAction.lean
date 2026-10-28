module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Setup
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Counting
public import Theory.PPrimeCore

/-!
# Regular conjugation by the inverted odd-core set

This proves the sharp transitivity and generation used in GLS, Volume 4,
Chapter 2, Proposition 17.6, referring there to Proposition 3.6(c).
Here `D = M ∩ Mᵗ` and the inverted set is literally the subset of the
ambient image of `O_{2'}(D)` specified in `CoreGrowth.Setup`.

The local normal-complement conclusion of Corollary 16.6(e) gives an
alternative to the earlier Z-star argument: every odd-order element of
`D` belongs to `O_{2'}(D)`. Thus `i ↦ ti` identifies the inverted set with
`Z ∩ Mt`. The coset count gives its cardinality, and the odd-product
argument proves that conjugation is injective for every `z ∈ Z ∩ M`.
The elementary injectivity argument is adapted from the private proof in
`MinimalReduction.Preliminaries.Counting`, without changing that shared
module's public boundary.

Finally, every basic commutator `[x,t]` with `x ∈ O_{2'}(D)` is inverted
by `t`. Conversely an inverted odd-order element is a power of its square,
which is its commutator with `t`. This proves generation with the actual
ambient subgroup maps. No regularity or generation premise is assumed.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem odd_inverter {c x : G} (hc : Odd (orderOf c))
    (hi : MulAut.conj c x = x⁻¹) : x = x⁻¹ := by
  have hs : Commute (c ^ 2) x := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      c ^ 2 * x * (c ^ 2)⁻¹ = MulAut.conj c (MulAut.conj c x) := by
        simp only [MulAut.conj_apply, pow_two]; group
      _ = x := by rw [hi, map_inv, hi, inv_inv]
  obtain ⟨k, hk⟩ := hc
  have he : c ^ (2 * k) * c = 1 := by
    rw [← pow_succ, ← hk, pow_orderOf_eq_one]
  have hcomm : Commute (c ^ (2 * k)) x := by
    simpa only [pow_mul] using hs.pow_left k
  have hcx : Commute c x := by
    have hcinv : c = (c ^ (2 * k))⁻¹ := by
      have hh := congrArg Inv.inv (eq_inv_iff_mul_eq_one.mpr he)
      simpa using hh.symm
    rw [hcinv]
    exact hcomm.inv_left
  exact (mul_inv_eq_iff_eq_mul.mpr hcx.eq).symm.trans hi

omit [Finite G] in
private theorem odd_square_one {x : G} (ho : Odd (orderOf x)) (hx : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := ho
  have hp := pow_orderOf_eq_one x
  rw [hk, pow_succ, pow_mul, hx, one_pow, one_mul] at hp
  exact hp

private theorem outside_injective (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {s t : G} (hs : s ∈ Z) (_hsM : s ∉ M) (ht : t ∈ Z) (htM : t ∉ M)
    (he : MulAut.conj (s : G) z = MulAut.conj t z) : s = t := by
  have si := (h.involutions s hs).inv_eq_self
  have ti := (h.involutions t ht).inv_eq_self
  have ss : s * s = 1 := by simpa [pow_two] using (h.involutions s hs).sq_eq_one
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hc : Commute (s * t) z := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (s * t) * z * (s * t)⁻¹ = MulAut.conj s (MulAut.conj t z) := by
        simp only [MulAut.conj_apply]; group
      _ = MulAut.conj s (MulAut.conj (s : G) z) := by rw [he]
      _ = z := by
        simp only [MulAut.conj_apply, si]
        calc
          s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by simp [ss]
  have hxM : s * t ∈ M := h.centralizer_le hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr hc.eq)
  have hxodd := productDisconnected_odd_orderOf_mul h hs ht htM (Or.inr hxM)
  have hct : MulAut.conj t (s * t) = (s * t)⁻¹ := by
    simp [MulAut.conj_apply, mul_inv_rev, si, ti, mul_assoc, tt]
  have hcz : MulAut.conj z (s * t) = s * t :=
    mul_inv_eq_iff_eq_mul.mpr hc.symm.eq
  have hcx : MulAut.conj (z * t) (s * t) = (s * t)⁻¹ := by
    calc
      _ = MulAut.conj z (MulAut.conj t (s * t)) := by
        simp only [MulAut.conj_apply]; group
      _ = (s * t)⁻¹ := by rw [hct, map_inv, hcz]
  have hinv := odd_inverter
    (productDisconnected_odd_orderOf_mul h hz ht htM (Or.inl hzM)) hcx
  have hone : s * t = 1 := odd_square_one hxodd (by
    rw [pow_two]
    nth_rw 1 [hinv]
    exact inv_mul_cancel _)
  exact (eq_inv_iff_mul_eq_one.mpr hone).trans ti



private theorem oddCoreImage_mem_iff
    {t x : G} (hc : HasNormalPComplement 2 (residualPairStabilizer M t)) :
    x ∈ (pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype ↔
      x ∈ residualPairStabilizer M t ∧ Odd (orderOf x) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    have hcop := (pPrimeCore_coprime_card (p := 2)
      (G := residualPairStabilizer M t)).of_dvd_right
        (orderOf_dvd_natCard (⟨y, hy⟩ : pPrimeCore 2 (residualPairStabilizer M t)))
    change Odd (orderOf (y : G))
    rw [Subgroup.orderOf_coe]
    simpa only [Subgroup.orderOf_mk, Nat.coprime_two_left] using hcop
  · rintro ⟨hx, ho⟩
    obtain ⟨N, hN, hNc, hNq⟩ := hc
    let := hN
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩,
      mem_pPrimeCore_of_normal_complement N hNc hNq _ (by
        simpa only [Subgroup.orderOf_mk, Nat.coprime_two_left] using ho), rfl⟩

omit [Finite G] in
private theorem conj_mem_pair {t x : G} (ht : IsInvolution t)
    (hx : x ∈ residualPairStabilizer M t) :
    t * x * t⁻¹ ∈ residualPairStabilizer M t := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy, he⟩ := hx.2
    change t⁻¹ * y * (t⁻¹)⁻¹ = x at he
    simp only [inv_inv] at he
    rw [← he]
    simpa [mul_assoc] using hy
  · exact Subgroup.mem_map.mpr ⟨x, hx.1, by
      change t⁻¹ * x * (t⁻¹)⁻¹ = t * x * t⁻¹
      simp only [ht.inv_eq_self]⟩

private theorem conj_mem_oddCoreImage {t x : G} (ht : IsInvolution t)
    (hc : HasNormalPComplement 2 (residualPairStabilizer M t))
    (hx : x ∈ (pPrimeCore 2 (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype) :
    t * x * t⁻¹ ∈ (pPrimeCore 2 (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype := by
  obtain ⟨hxD, ho⟩ := (oddCoreImage_mem_iff hc).mp hx
  apply (oddCoreImage_mem_iff hc).mpr
  refine ⟨conj_mem_pair ht hxD, ?_⟩
  change Odd (orderOf (MulAut.conj t x))
  rwa [MulEquiv.orderOf_eq]

private theorem inverted_mul_mem_Z (h : IsProductDisconnected Z M)
    {t : G} (ht : t ∈ Z)
    (hc : HasNormalPComplement 2 (residualPairStabilizer M t))
    {i : M} (hi : i ∈ coreGrowthInvertedSet M t) : t * (i : G) ∈ Z := by
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hs : (t * (i : G)) ^ 2 = 1 := by
    have hinv := hi.2
    rw [ti] at hinv
    calc
      _ = (t * (i : G) * t) * (i : G) := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hinv]; simp
  have ho := ((oddCoreImage_mem_iff hc).mp hi.1).2
  have hp : t * (t * (i : G)) = (i : G) := by rw [← mul_assoc, tt, one_mul]
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_involutions_odd_product
    t (t * (i : G)) (h.involutions t ht).sq_eq_one hs (hp.symm ▸ ho))
  exact hg ▸ h.invariant g t ht

private theorem coset_product_mem_inverted (h : IsProductDisconnected Z M)
    {t s : G} (ht : t ∈ Z) (htM : t ∉ M) (hs : s ∈ Z) (hst : s * t ∈ M)
    (hc : HasNormalPComplement 2 (residualPairStabilizer M t)) :
    ∃ i : M, i ∈ coreGrowthInvertedSet M t ∧ (i : G) = t * s := by
  have ti := (h.involutions t ht).inv_eq_self
  have si := (h.involutions s hs).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hts : t * s ∈ M := by simpa [mul_inv_rev, ti, si] using M.inv_mem hst
  refine ⟨⟨t * s, hts⟩, ⟨(oddCoreImage_mem_iff hc).mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
  · refine ⟨hts, Subgroup.mem_map.mpr ⟨s * t, hst, ?_⟩⟩
    change t⁻¹ * (s * t) * (t⁻¹)⁻¹ = t * s
    simp [ti, mul_assoc, tt]
  · have ho := productDisconnected_odd_orderOf_mul h hs ht htM (Or.inr hst)
    have hi : Odd (orderOf (s * t)⁻¹) := by simpa only [orderOf_inv] using ho
    simpa [mul_inv_rev, ti, si] using hi
  · change t * (t * s) * t⁻¹ = (t * s)⁻¹
    simp [ti, si, ← mul_assoc t t, tt]

/-- Sharp transitivity for every distinguished involution, using the actual
normal 2-complement of the pair stabilizer. -/
public theorem coreGrowthConjugate_bijective_of_normal_complement
    (h : IsProductDisconnected Z M) {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hc : HasNormalPComplement 2 (residualPairStabilizer M t))
    (z : M) (hz : (z : G) ∈ Z) :
    Function.Bijective (coreGrowthConjugate h t z hz) := by
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  let f : coreGrowthInvertedSet M t → {s : G // s ∈ Z ∧ s * t ∈ M} := fun i =>
    ⟨t * (i : G), inverted_mul_mem_Z h ht hc i.property, by
      have he : t * (i : G) * t = (i : G)⁻¹ := by simpa [ti] using i.property.2
      rw [he]
      exact M.inv_mem (i : M).property⟩
  have hfi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val he)
  have hfs : Function.Surjective f := by
    intro s
    obtain ⟨i, hi, he⟩ := coset_product_mem_inverted h ht htM s.property.1 s.property.2 hc
    refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
    change t * (i : G) = s
    rw [he, ← mul_assoc, tt, one_mul]
  have hcard : Nat.card (coreGrowthInvertedSet M t) =
      Nat.card {w : M // (w : G) ∈ Z} := by
    calc
      _ = Nat.card {s : G // s ∈ Z ∧ s * t ∈ M} :=
        Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)
      _ = Nat.card {w : G // w ∈ Z ∧ w ∈ M} :=
        productDisconnected_card_right_coset h ht htM
      _ = _ := Nat.card_congr {
        toFun := fun (w : {w : G // w ∈ Z ∧ w ∈ M}) => ⟨⟨w, w.property.2⟩, w.property.1⟩
        invFun := fun (w : {w : M // (w : G) ∈ Z}) => ⟨w, w.property, w.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hinj : Function.Injective (coreGrowthConjugate h t z hz) := by
    intro i j he
    apply hfi
    apply Subtype.ext
    apply outside_injective h hz z.property (f i).property.1 ?_ (f j).property.1 ?_ ?_
    · intro hm
      apply htM
      have hh := M.mul_mem hm (M.inv_mem (i : M).property)
      simpa [f, mul_assoc] using hh
    · intro hm
      apply htM
      have hh := M.mul_mem hm (M.inv_mem (j : M).property)
      simpa [f, mul_assoc] using hh
    · have heG := congrArg (fun w : {w : M // (w : G) ∈ Z} => ((w : M) : G)) he
      change (i : G) * (z : G) * (i : G)⁻¹ = (j : G) * (z : G) * (j : G)⁻¹ at heG
      change MulAut.conj (t * (i : G)) (z : G) = MulAut.conj (t * (j : G)) (z : G)
      simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using
        congrArg (fun x : G => t * x * t⁻¹) heG
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

private theorem involution_zpowers_cases {t b : G} (ht : IsInvolution t)
    (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  classical
  have ho : orderOf t = 2 := orderOf_eq_prime_iff.mpr ⟨ht.sq_eq_one, ht.ne_one⟩
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hb)
  have hnlt : n < 2 := ho ▸ Finset.mem_range.mp hn
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with hh | hh
  · left; simpa [hh] using he.symm
  · right; simpa [hh] using he.symm

/-- The set of odd-core elements inverted by `t` generates exactly the
ambient commutator subgroup, with all subgroup maps retained. -/
public theorem coreGrowthInvertedSet_generates_of_normal_complement
    {t : G} (ht : IsInvolution t)
    (hc : HasNormalPComplement 2 (residualPairStabilizer M t)) :
    (Subgroup.closure (coreGrowthInvertedSet M t)).map M.subtype =
      residualCommutator M t := by
  let K := (pPrimeCore 2 (residualPairStabilizer M t)).map
    (residualPairStabilizer M t).subtype
  let L := (Subgroup.closure (coreGrowthInvertedSet M t)).map M.subtype
  have ti := ht.inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro i hi
    change (i : G) ∈ ⁅K, Subgroup.zpowers t⁆
    have hsq : (i : G) ^ 2 ∈ ⁅K, Subgroup.zpowers t⁆ := by
      have hm := Subgroup.commutator_mem_commutator hi.1 (Subgroup.mem_zpowers t)
      have he : ⁅(i : G), t⁆ = (i : G) ^ 2 := by
        change (i : G) * t * (i : G)⁻¹ * t⁻¹ = (i : G) ^ 2
        have hinv : t * (i : G)⁻¹ * t⁻¹ = (i : G) := by
          have hh := congrArg Inv.inv hi.2
          simpa [mul_inv_rev, mul_assoc] using hh
        calc
          _ = (i : G) * (t * (i : G)⁻¹ * t⁻¹) := by group
          _ = (i : G) ^ 2 := by rw [hinv, pow_two]
      exact he ▸ hm
    obtain ⟨k, hk⟩ := ((oddCoreImage_mem_iff hc).mp hi.1).2
    have he : ((i : G) ^ 2) ^ (k + 1) = (i : G) := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        ← hk, pow_succ, pow_orderOf_eq_one, one_mul]
    exact he ▸ (⁅K, Subgroup.zpowers t⁆).pow_mem hsq (k + 1)
  · change ⁅K, Subgroup.zpowers t⁆ ≤ L
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    rcases involution_zpowers_cases ht hb with hb1 | hbt
    · rw [hb1]; simp
    · rw [hbt]
      have hconj := conj_mem_oddCoreImage ht hc (K.inv_mem ha)
      have hcomm : ⁅a, t⁆ ∈ K := by
        have hh := K.mul_mem ha hconj
        simpa only [commutatorElement_def, mul_assoc] using hh
      have hinv : t * ⁅a, t⁆ * t⁻¹ = ⁅a, t⁆⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv, ti]
        simp only [mul_assoc, tt, mul_one]
      have hm : ⁅a, t⁆ ∈ M := ((oddCoreImage_mem_iff hc).mp hcomm).1.1
      apply Subgroup.mem_map.mpr
      exact ⟨⟨⁅a, t⁆, hm⟩, Subgroup.subset_closure ⟨hcomm, hinv⟩, rfl⟩

/-- The generation and sharp-transitivity inputs to core growth, with the
normal complement discharged by the source local hypothesis. The other
residual and counting hypotheses of Proposition 17.6 are unnecessary for
this step. In particular regularity holds for every distinguished `z`. -/
public theorem TwoCoreCountingData.inverted_set_generation_and_regularity
    (d : TwoCoreCountingData Z M) (h : MinimalCounterexample Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    (Subgroup.closure (coreGrowthInvertedSet M d.t)).map M.subtype =
        residualCommutator M d.t ∧
      ∀ z : M, ∀ hz : (z : G) ∈ Z,
        Function.Bijective (coreGrowthConjugate h.disconnected d.t z hz) := by
  have hc := (hlocal (residualPairStabilizer M d.t)
    (residualPairStabilizer_localClosure_eq_bot h.disconnected d.t_not_mem)).1
  exact ⟨coreGrowthInvertedSet_generates_of_normal_complement
      (h.disconnected.involutions d.t d.t_mem) hc,
    coreGrowthConjugate_bijective_of_normal_complement
      h.disconnected d.t_mem d.t_not_mem hc⟩

end BenderSuzuki.ZD
