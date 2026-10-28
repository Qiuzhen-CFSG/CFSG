module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Swapping

/-!
# Distinguished normalizing swaps: Lemma 7.3

Every z-invariant Sylow p-subgroup of the triple stabilizer admits a
normalizing involution in the distinguished set Z interchanging the base
point and beta. The easy branch extends a point-swapping involution to an
invariant Sylow subgroup of the pair stabilizer. In the other branch,
fixed-prime, fixed-involution maximality gives double transitivity, and a
normalizer reflection is transported along a conjugacy of triples. Sylow
conjugacy in the triple stabilizer finishes both branches.

All conjugations retain membership in Z. Product disconnection restricts
to N_G(P), so its odd-product reflection supplies the normalizer step
without a local strong-embedding invocation. In particular no oddness of
the pair stabilizer or ambient strong embedding is used.

Source: GLS, Volume 4, Chapter 2, Lemmas 6.1 and 7.3.
Sylow and stabilizer calculations adapt `SE.Section7Lemma73`; the
pair-conjugacy calculation adapts `Counting.SectionThree.Indices`.
-/

noncomputable section
namespace BenderSuzuki.ZD.NormalizingSwap
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

/-- A Sylow subgroup of `D` that lies in an intermediate subgroup `E` is
still Sylow in `E`, in the ambient encoding used by Section 7. -/
private theorem theorem4bIsSylowSubgroupOf_of_le
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E D : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P D)
    (hPE : P ≤ E) (hED : E ≤ D) :
    theorem4bIsSylowSubgroupOf p P E := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PD, hP⟩
  let ED : Subgroup D := E.subgroupOf D
  have hPDle : (PD : Subgroup D) ≤ ED := by
    intro x hx
    change (x : X) ∈ E
    apply hPE
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hx
  let PED : Sylow p ED := PD.subtype hPDle
  let e : ED ≃* E := Subgroup.subgroupOfEquivOfLe hED
  let PE : Sylow p E := PED.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨PE, ?_⟩
  apply le_antisymm
  · intro x hxP
    rw [hP] at hxP
    rcases Subgroup.mem_map.mp hxP with ⟨xD, hxPD, rfl⟩
    apply Subgroup.mem_map.mpr
    let xED : ED := ⟨xD, hPDle hxPD⟩
    refine ⟨e xED, ?_, rfl⟩
    have hxPED : xED ∈ PED := by
      exact hxPD
    simpa [PE] using
      (Subgroup.mem_map_of_mem e.toMonoidHom hxPED)
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xE, hxPE, rfl⟩
    have hxPE' : xE ∈ (PED : Subgroup ED).map e.toMonoidHom := by
      simpa [PE] using hxPE
    rcases Subgroup.mem_map.mp hxPE' with ⟨xED, hxPED, hx⟩
    change (xED : D) ∈ (PD : Subgroup D) at hxPED
    rw [hP]
    apply Subgroup.mem_map.mpr
    refine ⟨(xED : D), hxPED, ?_⟩
    change (xED : X) = (xE : X)
    calc
      (xED : X) = (e xED : X) := by rfl
      _ = (xE : X) := congrArg (fun y : E => (y : X)) hx

/-- Equal-order ambient groups have the same Sylow size, so a Sylow subgroup
of one that lies in the other is Sylow in the other. -/
private theorem theorem4bIsSylowSubgroupOf_of_card_eq
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P D F : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P F)
    (hPD : P ≤ D) (hcard : Nat.card D = Nat.card F) :
    theorem4bIsSylowSubgroupOf p P D := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PF, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card F).factorization p := by
    rw [hP, Subgroup.card_map_of_injective F.subtype_injective]
    exact Sylow.card_eq_multiplicity PF
  have hPDcard : Nat.card (P.subgroupOf D) =
      p ^ (Nat.card D).factorization p := by
    rw [natCard_subgroupOf_eq P D hPD, hPcard, hcard]
  let PD : Sylow p D := Sylow.ofCard (P.subgroupOf D) hPDcard
  refine ⟨PD, ?_⟩
  have hmap : (P.subgroupOf D).map D.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  simpa [PD] using hmap.symm

/-- Inside a fixed ambient subgroup, Sylow status is determined by subgroup
cardinality. -/
private theorem theorem4bIsSylowSubgroupOf_of_subgroup_card_eq
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQE : Q ≤ E) (hcard : Nat.card Q = Nat.card P) :
    theorem4bIsSylowSubgroupOf p Q E := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PE, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card E).factorization p := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective]
    exact Sylow.card_eq_multiplicity PE
  have hQEcard : Nat.card (Q.subgroupOf E) =
      p ^ (Nat.card E).factorization p := by
    rw [natCard_subgroupOf_eq Q E hQE, hcard, hPcard]
  let QE : Sylow p E := Sylow.ofCard (Q.subgroupOf E) hQEcard
  refine ⟨QE, ?_⟩
  change Q = (Q.subgroupOf E).map E.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]

private theorem theorem4bIsSylowSubgroupOf_le
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (h : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases h with ⟨Q, hQ⟩
  rw [hQ]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
  exact q.property

private theorem lemma73_D_conjBy_eq_F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z a : X} {beta : conjugateCosetSpace M}
    (ha0 : a • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta)
    (hab : a • beta = z • beta) :
    (M ⊓ MulAction.stabilizer X beta).conjBy a =
      MulAction.stabilizer X beta ⊓
        MulAction.stabilizer X (z • beta) := by
  rw [Subgroup.conjBy, Subgroup.map_inf _ _ _ (MulAut.conj a).injective]
  conv_lhs =>
    lhs
    rw [← baseCoset_stabilizer M]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [ha0, hab]

/-- Conjugating a source triple stabilizer along a triple transport gives the
original Section 7 triple stabilizer. -/
private theorem lemma73_tripleStabilizer_conjBy_eq_E
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z s g : X} {gamma delta beta : conjugateCosetSpace M}
    (hgamma : g • gamma =
      (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hdelta : g • delta = beta)
    (hsz : rightConjugateElem s g⁻¹ = z) :
    (((MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X delta) ⊓
        MulAction.stabilizer X (s • delta)).conjBy g) =
      theorem4bSection7E M z beta := by
  have hgsdelta : g • (s • delta) = z • beta := by
    have hconj : g * s * g⁻¹ = z := by
      simpa [rightConjugateElem] using hsz
    calc
      g • (s • delta) = (g * s) • delta := by rw [mul_smul]
      _ = ((g * s * g⁻¹) * g) • delta := by simp
      _ = z • (g • delta) := by rw [hconj, mul_smul]
      _ = z • beta := by rw [hdelta]
  rw [theorem4bSection7E, theorem4bSection7D, Subgroup.conjBy]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hgamma, hdelta, hgsdelta, baseCoset_stabilizer]

/-- Transport a swapping involution between two Sylow subgroups of a pointwise
pair stabilizer. -/
private theorem lemma73_transport_swap_between_sylows
    {X Omega : Type u} [Group X] [Finite X] [MulAction X Omega]
    {Z : Set X} {M : Subgroup X} (h : IsProductDisconnected Z M)
    {p : ℕ} {E P Q : Subgroup X} {alpha beta : Omega} {t : X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E)
    (hEalpha : E ≤ MulAction.stabilizer X alpha)
    (hEbeta : E ≤ MulAction.stabilizer X beta)
    (ht : t ∈ Z)
    (htNormQ : t ∈ Subgroup.normalizer (Q : Set X))
    (htAlpha : t • alpha = beta) (htBeta : t • beta = alpha) :
    ∃ u : X,
      u ∈ Z ∧
      u ∈ Subgroup.normalizer (P : Set X) ∧
      u • alpha = beta ∧ u • beta = alpha := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨P₀, hP⟩
  rcases hQsyl with ⟨Q₀, hQ⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq E P₀ Q₀
  have hQconj : Q = P.conjBy (x : X) := by
    rw [hQ, hP, ← hx]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rw [Subgroup.conjBy]
    change Subgroup.map E.subtype
        (Subgroup.map (MulDistribMulAction.toMonoidHom E (MulAut.conj x))
          (P₀ : Subgroup E)) =
      Subgroup.map ((MulAut.conj (x : X)).toMonoidHom)
        (Subgroup.map E.subtype (P₀ : Subgroup E))
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconjNorm :=
    section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (Subgroup.zpowers_le.mpr htNormQ) (x : X)⁻¹
  have hconjNormP : (Subgroup.zpowers t).conjBy (x : X)⁻¹ ≤
      Subgroup.normalizer (P : Set X) := by
    simpa [hQconj, Subgroup.conjBy_inv] using hconjNorm
  let u : X := rightConjugateElem t (x : X)
  have huNorm : u ∈ Subgroup.normalizer (P : Set X) := by
    apply hconjNormP
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨t, Subgroup.mem_zpowers t, ?_⟩
    simp [u, rightConjugateElem]
  have hxAlpha : (x : X) • alpha = alpha :=
    MulAction.mem_stabilizer_iff.mp (hEalpha x.property)
  have hxBeta : (x : X) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp (hEbeta x.property)
  have hxInvAlpha : (x : X)⁻¹ • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X alpha).inv_mem (hEalpha x.property)
  have hxInvBeta : (x : X)⁻¹ • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X beta).inv_mem (hEbeta x.property)
  refine ⟨u, (show u ∈ Z by simpa [u, rightConjugateElem, MulAut.conj_apply] using h.invariant (x : X)⁻¹ t ht), huNorm, ?_, ?_⟩
  · calc
      u • alpha = (x : X)⁻¹ • (t • ((x : X) • alpha)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • alpha) := by rw [hxAlpha]
      _ = (x : X)⁻¹ • beta := by rw [htAlpha]
      _ = beta := hxInvBeta
  · calc
      u • beta = (x : X)⁻¹ • (t • ((x : X) • beta)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • beta) := by rw [hxBeta]
      _ = (x : X)⁻¹ • alpha := by rw [htBeta]
      _ = alpha := hxInvAlpha

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

private theorem base_transitive (h : IsProductDisconnected Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    {a : G} (ha : a ∈ Z) (haM : a ∈ M) :
    ∃ d : (M ⊓ rightConjugate M t : Subgroup G), MulAut.conj (d : G) z = a := by
  let O := {s : G // s ∈ Z ∧ s ∉ M}
  let f : O → O := fun s => ⟨MulAut.conj (s : G) z, h.invariant s z hz,
    fun hm => s.property.2 ((h.conjugate_mem_iff z hz hzM s).mp hm)⟩
  have hf : Function.Injective f := by
    intro s u he
    exact Subtype.ext (outside_injective h hz hzM s.property.1 s.property.2
      u.property.1 u.property.2 (congrArg Subtype.val he))
  have hsur := Finite.surjective_of_injective hf
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  let b : O := ⟨MulAut.conj t a, h.invariant _ _ ha,
    fun hm => htM ((h.conjugate_mem_iff a ha haM t).mp hm)⟩
  obtain ⟨s, hs⟩ := hsur b
  have he : MulAut.conj (s : G) z = MulAut.conj t a := congrArg Subtype.val hs
  have he' : MulAut.conj (t * s) z = a := by
    calc
      _ = MulAut.conj t (MulAut.conj (s : G) z) := by simp [MulAut.conj_apply, mul_assoc]
      _ = a := by rw [he]; simp only [MulAut.conj_apply, ti]; calc
        t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by simp [tt]
  have hm : t * (s : G) ∈ M :=
    (h.conjugate_mem_iff z hz hzM _).mp (by rw [he']; exact haM)
  have hsm : (s : G) * t ∈ M := by
    simpa only [mul_inv_rev, ti, (h.involutions s s.property.1).inv_eq_self] using M.inv_mem hm
  refine ⟨⟨t * s, hm, ?_⟩, he'⟩
  have hh := rightConjugateElem_mem_rightConjugate (g := t) hsm
  simpa [rightConjugateElem, ti, mul_assoc, tt] using hh

/-- Lemma 6.1 in the exact transport form needed by Lemma 7.3: double
transitivity first matches the ordered pair, and Proposition 3.6(c) adjusts
the fixed-point involution inside the resulting two-point stabilizer. -/
private theorem lemma61_triple_transport
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {Z : Set X} (h : IsProductDisconnected Z M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    {z s : X} (hzM : z ∈ M) (hz : z ∈ Z)
    (hs : s ∈ Z)
    {gamma delta beta : conjugateCosetSpace M}
    (hsGamma : s • gamma = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hbetaNe : beta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    ∃ g : X,
      g • gamma = (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
      g • delta = beta ∧
      rightConjugateElem s g⁻¹ = z := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  obtain ⟨x, hxGamma, hxDelta⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo)
      hgammaDelta hbetaNe.symm
  let s' : X := rightConjugateElem s x⁻¹
  have hs' : s' ∈ Z := by
    simpa [s', rightConjugateElem, MulAut.conj_apply] using h.invariant x s hs
  have hxInvAlpha : x⁻¹ • alpha = gamma := by
    calc
      x⁻¹ • alpha = x⁻¹ • (x • gamma) := by rw [hxGamma]
      _ = gamma := inv_smul_smul x gamma
  have hs'Alpha : s' • alpha = alpha := by
    calc
      s' • alpha = x • (s • (x⁻¹ • alpha)) := by
        simp [s', rightConjugateElem, mul_smul]
      _ = x • (s • gamma) := by rw [hxInvAlpha]
      _ = x • gamma := by rw [hsGamma]
      _ = alpha := hxGamma
  have hs'M : s' ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hs'Alpha
  obtain ⟨t, htZ, htAlpha⟩ := sectionThree_swap h alpha beta hbetaNe.symm
  have ht := h.involutions t htZ
  have htM : t ∉ M := by
    intro hm
    have hf : t • alpha = alpha := MulAction.mem_stabilizer_iff.mp (by
      simpa [alpha, baseCoset_stabilizer] using hm)
    exact hbetaNe (htAlpha.symm.trans hf)
  obtain ⟨c, hc⟩ := base_transitive h hs' hs'M htZ htM hz hzM
  let d : X := (c : X)⁻¹
  have hdD : d ∈ M ⊓ rightConjugate M t := (M ⊓ rightConjugate M t).inv_mem c.property
  have hs'd : rightConjugateElem s' d = z := by
    simpa [d, rightConjugateElem, MulAut.conj_apply] using hc
  have hdAlpha : d • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact hdD.1
  have hstabBeta : MulAction.stabilizer X beta = rightConjugate M t := by
    rw [← htAlpha]
    simpa [alpha, MulAction.Quotient.smul_mk, smul_eq_mul, ht.inv_eq_self] using
      conjugateCoset_stabilizer M t
  have hdBeta : d • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hstabBeta]
    exact hdD.2
  have hdInvAlpha : d⁻¹ • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X alpha).inv_mem
      (MulAction.mem_stabilizer_iff.mpr hdAlpha)
  have hdInvBeta : d⁻¹ • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X beta).inv_mem
      (MulAction.mem_stabilizer_iff.mpr hdBeta)
  let g : X := d⁻¹ * x
  refine ⟨g, ?_, ?_, ?_⟩
  · calc
      g • gamma = d⁻¹ • (x • gamma) := by simp [g, mul_smul]
      _ = d⁻¹ • alpha := by rw [hxGamma]
      _ = alpha := hdInvAlpha
  · calc
      g • delta = d⁻¹ • (x • delta) := by simp [g, mul_smul]
      _ = d⁻¹ • beta := by rw [hxDelta]
      _ = beta := hdInvBeta
  · calc
      rightConjugateElem s g⁻¹ =
          rightConjugateElem s (x⁻¹ * d) := by
            congr 1
            simp [g]
      _ = rightConjugateElem (rightConjugateElem s x⁻¹) d := by
        rw [rightConjugateElem_comp]
      _ = z := hs'd

/-- The normalizer-growth consequence needed in the hard branch of Lemma 7.3.
It is independent of the involution and fixed-point data. -/
private theorem lemma73_normalizer_not_le_of_not_sylow_F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z : X} {beta : conjugateCosetSpace M} {p : ℕ} {P : Subgroup X}
    (hp : Nat.Prime p)
    (hPsylE : theorem4bIsSylowSubgroupOf p P
      (theorem4bSection7E M z beta))
    (hPnotF : ¬ theorem4bIsSylowSubgroupOf p P
      (theorem4bSection7F z beta)) :
    ¬ Subgroup.normalizer (P : Set X) ≤ M := by
  classical
  let E : Subgroup X := theorem4bSection7E M z beta
  let F : Subgroup X := theorem4bSection7F z beta
  have hFM : F ⊓ M = E := by
    simp only [F, E, theorem4bSection7F, theorem4bSection7E,
      theorem4bSection7D]
    ac_rfl
  intro hnorm
  let : Fact p.Prime := ⟨hp⟩
  have hPsylFM : theorem4bIsSylowSubgroupOf p P (F ⊓ M) := by
    rw [hFM]
    exact hPsylE
  rcases hPsylFM with ⟨R, hPR⟩
  have hnormR :
      Subgroup.normalizer
          (section8SubgroupInAmbient
            (R : Subgroup (F ⊓ M : Subgroup X)) : Set X) ≤ M := by
    simpa [section8SubgroupInAmbient, hPR] using hnorm
  obtain ⟨R_F, hR_F⟩ :=
    section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
      (G := X) (p := p) (M := M) (N := F) R hnormR
  apply hPnotF
  refine ⟨R_F, ?_⟩
  calc
    P = section8SubgroupInAmbient
        (R : Subgroup (F ⊓ M : Subgroup X)) := by
          simpa [section8SubgroupInAmbient] using hPR
    _ = section8SubgroupInAmbient (R_F : Subgroup F) := hR_F.symm
    _ = (R_F : Subgroup F).map F.subtype := rfl

/-- Product disconnection restricts to the normalizer. Its distinguished
reflection conjugator remains in that normalizer. -/
private theorem normalizer_outside_distinguished
    (h : IsProductDisconnected Z M) {P : Subgroup G} {z : G}
    (hz : z ∈ Z) (hzM : z ∈ M)
    (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (hNnot : ¬ Subgroup.normalizer (P : Set G) ≤ M) :
    ∃ s u : G, s ∈ Z ∧ s ∉ M ∧
      s ∈ Subgroup.normalizer (P : Set G) ∧ u ∈ Z ∧
      u ∈ Subgroup.normalizer (P : Set G) ∧ rightConjugateElem z u = s := by
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨n, hnN, hnM⟩ := SetLike.not_le_iff_exists.mp hNnot
  let s : G := MulAut.conj n z
  have hs : s ∈ Z := h.invariant n z hz
  have hsN : s ∈ N := N.mul_mem (N.mul_mem hnN hzP) (N.inv_mem hnN)
  have hsM : s ∉ M := fun hm => hnM ((h.conjugate_mem_iff z hz hzM n).mp hm)
  have hN := productDisconnected_subgroup h N hNnot ⟨z, hz, hzP, hzM⟩
  obtain ⟨u, hu, hconj⟩ := sectionThree_distinguished_conjugator hN
    (z := ⟨z, hzP⟩) (u := ⟨s, hsN⟩) hz hzM hs hsM
  refine ⟨s, u, hs, hsM, hsN, hu, u.property, ?_⟩
  have he := congrArg N.subtype hconj
  change (u : G) * z * (u : G)⁻¹ = s at he
  simpa only [rightConjugateElem, MulAut.conj_apply,
    (h.involutions (u : G) hu).inv_eq_self] using he

private theorem twoPoint_sylow_swap
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    {beta : G ⧸ M} (hne : beta ≠ QuotientGroup.mk 1) {Q : Subgroup G}
    (hQ : theorem4bIsSylowSubgroupOf p Q (theorem4bSection7D M beta)) :
    ∃ t ∈ Z, t ∈ Subgroup.normalizer (Q : Set G) ∧
      t • (QuotientGroup.mk 1 : G ⧸ M) = beta ∧
      t • beta = (QuotientGroup.mk 1 : G ⧸ M) := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let D := theorem4bSection7D M beta
  obtain ⟨t, htZ, hta⟩ := h3.swap alpha beta hne.symm
  have ht := h.involutions t htZ
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    have hn := theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup G)) (z := t) (beta := alpha) ht (Subgroup.mem_top t)
    simpa [D, theorem4bSection7D, alpha, baseCoset_stabilizer, hta] using hn
  obtain ⟨R, hR, _, htR, _⟩ := h3.swapping_sylow t htZ alpha
    (by simpa only [hta] using hne) p hp hpOdd D ⊥
    (by simp [D, theorem4bSection7D, hta, alpha])
    htD IsPGroup.of_bot bot_le (by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp)
  have htb : t • beta = alpha := by
    rw [← hta, ← mul_smul]
    have htt : t * t = 1 := by simpa only [pow_two] using ht.sq_eq_one
    rw [htt, one_smul]
  apply lemma73_transport_swap_between_sylows h hp hQ hR
    (by simp [theorem4bSection7D, alpha])
    (by exact inf_le_right) htZ htR hta htb

/-- Both Sylow branches of distinguished Lemma 7.3. -/
private theorem exists_swap_normalizing
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {Z : Set X} (h : IsProductDisconnected Z M)
    (hc : ActionCounting Z M) (h3 : ActionSectionThree Z M)
    (d : ActionMaximalCounterexample Z M)
    {beta : conjugateCosetSpace M}
    (hbetaK : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    {P : Subgroup X}
    (hPsyl : theorem4bIsSylowSubgroupOf d.data.p P
      (theorem4bSection7E M d.data.z beta))
    (hzP : d.data.z ∈ Subgroup.normalizer (P : Set X)) :
    ∃ t : X,
      t ∈ Z ∧
      t ∈ Subgroup.normalizer (P : Set X) ∧
      t • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta ∧
      t • beta = (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let D : Subgroup X := theorem4bSection7D M beta
  let E : Subgroup X := theorem4bSection7E M d.data.z beta
  by_cases hEasy : ∃ Q : Subgroup X,
      theorem4bIsSylowSubgroupOf d.data.p Q D ∧
      d.data.z ∈ Subgroup.normalizer (Q : Set X)
  · rcases hEasy with ⟨Q, hQsylD, hzQ⟩
    have hQD : Q ≤ D := theorem4bIsSylowSubgroupOf_le hQsylD
    have hQD' : Q ≤ M ⊓ MulAction.stabilizer X beta := by
      simpa [D, theorem4bSection7D] using hQD
    have hQE : Q ≤ E := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        (theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer hzQ hQD')
    have hED : E ≤ D := by
      change theorem4bSection7E M d.data.z beta ≤
        theorem4bSection7D M beta
      exact inf_le_left
    have hQsylE : theorem4bIsSylowSubgroupOf d.data.p Q E := by
      simpa [E] using
        (theorem4bIsSylowSubgroupOf_of_le d.data.hp hQsylD hQE hED)
    obtain ⟨t, ht, htNorm, htAlpha, htBeta⟩ :=
      twoPoint_sylow_swap h h3 d.data.hp d.data.hpOdd hbetaNe hQsylD
    have hEalpha : E ≤ MulAction.stabilizer X alpha := by
      have hDM : D ≤ M := by
        change theorem4bSection7D M beta ≤ M
        exact inf_le_left
      simpa [alpha, baseCoset_stabilizer] using hED.trans hDM
    have hEbeta : E ≤ MulAction.stabilizer X beta := by
      have hDbeta : D ≤ MulAction.stabilizer X beta := by
        change theorem4bSection7D M beta ≤ MulAction.stabilizer X beta
        exact inf_le_right
      exact hED.trans hDbeta
    exact lemma73_transport_swap_between_sylows h
      d.data.hp hPsyl hQsylE hEalpha hEbeta ht htNorm htAlpha htBeta
  · have htwo : MulAction.IsMultiplyPretransitive X
        (conjugateCosetSpace M) 2 := by
      by_contra hnot2
      apply hEasy
      exact (d.invariant_sylow_iff h hc hbetaK hbetaNe).mpr
        (d.card_eq_primeShare hc hnot2)
    have hzbNe : d.data.z • beta ≠ beta := by
      intro hfix
      exact hbetaNe (action_fixedPoint_eq_base h d.data.hzZ d.data.hzM hfix)
    obtain ⟨a, ha0, hab⟩ :=
      (MulAction.is_two_pretransitive_iff.mp htwo)
        hbetaNe.symm hzbNe.symm
    have hDconj : D.conjBy a = theorem4bSection7F d.data.z beta := by
      simpa [D, theorem4bSection7D, theorem4bSection7F] using
        lemma73_D_conjBy_eq_F ha0 hab
    have hcardDF : Nat.card D =
        Nat.card (theorem4bSection7F d.data.z beta) := by
      calc
        Nat.card D = Nat.card (D.conjBy a) :=
          (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
        _ = Nat.card (theorem4bSection7F d.data.z beta) := by rw [hDconj]
    have hPnotF : ¬ theorem4bIsSylowSubgroupOf d.data.p P
        (theorem4bSection7F d.data.z beta) := by
      intro hPF
      have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le hPsyl
      have hED : E ≤ D := by
        change theorem4bSection7E M d.data.z beta ≤
          theorem4bSection7D M beta
        exact inf_le_left
      have hPD := theorem4bIsSylowSubgroupOf_of_card_eq
        (D := D) (F := theorem4bSection7F d.data.z beta)
        d.data.hp hPF (hPE.trans hED) hcardDF
      apply hEasy
      exact ⟨P, by simpa [D] using hPD, hzP⟩
    have hNnot : ¬ Subgroup.normalizer (P : Set X) ≤ M :=
      lemma73_normalizer_not_le_of_not_sylow_F d.data.hp hPsyl hPnotF
    obtain ⟨s, u, hsZ, hsNotM, hsNorm, huZ, huNorm, hzu⟩ :=
      normalizer_outside_distinguished h d.data.hzZ d.data.hzM hzP hNnot
    have hu := h.involutions u huZ
    have hzAlpha : d.data.z • alpha = alpha := by
      dsimp [alpha]
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [baseCoset_stabilizer M]
        exact d.data.hzM)
    let gamma : conjugateCosetSpace M := u • alpha
    have hsGamma : s • gamma = gamma := by
      calc
        s • gamma = rightConjugateElem d.data.z u • (u • alpha) := by
          rw [hzu]
        _ = ((u⁻¹ * d.data.z * u) * u) • alpha := by
          simp [rightConjugateElem, mul_smul]
        _ = (u⁻¹ * d.data.z) • alpha := by
          congr 1
          have huu : u * u = 1 := by
            simpa [pow_two] using hu.sq_eq_one
          calc
            (u⁻¹ * d.data.z * u) * u =
                u⁻¹ * d.data.z * (u * u) := by group
            _ = u⁻¹ * d.data.z := by rw [huu]; simp
        _ = u⁻¹ • (d.data.z • alpha) := by rw [mul_smul]
        _ = u⁻¹ • alpha := by rw [hzAlpha]
        _ = u • alpha := by rw [hu.inv_eq_self]
        _ = gamma := rfl
    have hgammaNe : gamma ≠ alpha := by
      intro hgamma
      have huFix : u •
          (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1 := by
        simpa [gamma, alpha] using hgamma
      have huM : u ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact MulAction.mem_stabilizer_iff.mpr huFix
      apply hsNotM
      rw [← hzu]
      exact M.mul_mem (M.mul_mem (M.inv_mem huM) d.data.hzM) huM
    have huu : u * u = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    have huGamma : u • gamma = alpha := by
      change u • (u • alpha) = alpha
      rw [← mul_smul, huu, one_smul]
    have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le hPsyl
    have hED : E ≤ D := by
      change theorem4bSection7E M d.data.z beta ≤
        theorem4bSection7D M beta
      exact inf_le_left
    have hDM : D ≤ M := by
      change theorem4bSection7D M beta ≤ M
      exact inf_le_left
    have hPalpha : P ≤ MulAction.stabilizer X alpha := by
      change P ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M)
      rw [baseCoset_stabilizer M]
      exact (hPE.trans hED).trans hDM
    have hPgamma : P ≤ MulAction.stabilizer X gamma := by
      simpa [gamma] using
        theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
          huNorm hPalpha
    have hPsAlpha : P ≤ MulAction.stabilizer X (s • alpha) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        hsNorm hPalpha
    let T : Subgroup X :=
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X alpha) ⊓
        MulAction.stabilizer X (s • alpha)
    have hPT : P ≤ T := le_inf (le_inf hPgamma hPalpha) hPsAlpha
    obtain ⟨g, hgGamma, hgAlpha, hsg⟩ :=
      lemma61_triple_transport h htwo d.data.hzM d.data.hzZ hsZ
        hsGamma hgammaNe hbetaNe
    have hTE : T.conjBy g = E := by
      simpa [T, E] using
        lemma73_tripleStabilizer_conjBy_eq_E hgGamma hgAlpha hsg
    let Q : Subgroup X := P.conjBy g
    have hQE : Q ≤ E := by
      rw [← hTE]
      exact Subgroup.map_mono hPT
    have hQcard : Nat.card Q = Nat.card P := by
      simpa [Q, Subgroup.conjBy] using
        (Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    have hQsylE : theorem4bIsSylowSubgroupOf d.data.p Q E :=
      theorem4bIsSylowSubgroupOf_of_subgroup_card_eq
        d.data.hp (by simpa [E] using hPsyl) hQE hQcard
    let t : X := rightConjugateElem u g⁻¹
    have ht : t ∈ Z := by
      simpa [t, rightConjugateElem, MulAut.conj_apply] using h.invariant g u huZ
    have hconjNorm : (Subgroup.zpowers u).conjBy g ≤
        Subgroup.normalizer (Q : Set X) := by
      simpa [Q] using
        section11_conjBy_le_normalizer_conjBy_of_le_normalizer
          (Subgroup.zpowers_le.mpr huNorm) g
    have htMemConj : t ∈ (Subgroup.zpowers u).conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨u, Subgroup.mem_zpowers u, ?_⟩
      simp [t, rightConjugateElem]
    have htNorm : t ∈ Subgroup.normalizer (Q : Set X) :=
      hconjNorm htMemConj
    have hgInvAlpha : g⁻¹ • alpha = gamma := by
      calc
        g⁻¹ • alpha = g⁻¹ • (g • gamma) := by rw [hgGamma]
        _ = gamma := inv_smul_smul g gamma
    have hgInvBeta : g⁻¹ • beta = alpha := by
      calc
        g⁻¹ • beta = g⁻¹ • (g • alpha) := by rw [hgAlpha]
        _ = alpha := inv_smul_smul g alpha
    have htAlpha : t • alpha = beta := by
      calc
        t • alpha = g • (u • (g⁻¹ • alpha)) := by
          simp [t, rightConjugateElem, mul_smul]
        _ = g • (u • gamma) := by rw [hgInvAlpha]
        _ = g • alpha := by rw [huGamma]
        _ = beta := hgAlpha
    have htBeta : t • beta = alpha := by
      calc
        t • beta = g • (u • (g⁻¹ • beta)) := by
          simp [t, rightConjugateElem, mul_smul]
        _ = g • (u • alpha) := by rw [hgInvBeta]
        _ = g • gamma := rfl
        _ = alpha := hgGamma
    have hEalpha : E ≤ MulAction.stabilizer X alpha := by
      change E ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M)
      rw [baseCoset_stabilizer M]
      exact hED.trans hDM
    have hEbeta : E ≤ MulAction.stabilizer X beta := by
      have hDbeta : D ≤ MulAction.stabilizer X beta := by
        change theorem4bSection7D M beta ≤ MulAction.stabilizer X beta
        exact inf_le_right
      exact hED.trans hDbeta
    exact lemma73_transport_swap_between_sylows h
      d.data.hp hPsyl hQsylE hEalpha hEbeta ht htNorm htAlpha htBeta

end BenderSuzuki.ZD.NormalizingSwap

namespace BenderSuzuki.ZD
open PFAppendixIII PFchapter1section1

/-- Distinguished Lemma 7.3: every invariant Sylow subgroup of the triple
stabilizer admits a distinguished normalizing swap. -/
public theorem actionGamma_normalizing_swap
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (h3 : ActionSectionThree Z M)
    (d : ActionMaximalCounterexample Z M)
    {beta : G ⧸ M} (hbeta : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf d.data.p P (theorem4bSection7E M d.data.z beta))
    (hzP : d.data.z ∈ Subgroup.normalizer (P : Set G)) :
    ∃ t ∈ Z, t ∈ Subgroup.normalizer (P : Set G) ∧
      t • (QuotientGroup.mk 1 : G ⧸ M) = beta := by
  obtain ⟨t, htZ, htP, hta, _⟩ := NormalizingSwap.exists_swap_normalizing
    h.disconnected hc h3 d hbeta hne hP hzP
  exact ⟨t, htZ, htP, hta⟩

end BenderSuzuki.ZD
