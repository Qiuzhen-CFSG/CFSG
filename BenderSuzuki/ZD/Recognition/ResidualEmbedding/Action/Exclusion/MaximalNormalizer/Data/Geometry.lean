module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Swapping

/-!
# Distinguished triples and their p-subgroups

Double transitivity matches an ordered pair. Conjugacy of the distinguished
involutions in its stabilizer then matches the third point as well. Transport
of stabilizers bounds every p-subgroup fixing a distinguished triple by a
Sylow p-subgroup of the reference triple stabilizer.

Source: GLS, Volume 4, Chapter 2, Lemma 6.1 and Proposition 7.8.
The transport calculation is retained from the checked, private argument in
`ThetaChain.Gamma.NormalizingSwap`; the cardinal comparison adapts
`SE.Section7Final`. No oddness of a point stabilizer is used.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
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
public theorem action_distinguished_triple_transport
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

/-- Cardinality comparison with a Sylow subgroup represented in an ambient
group by `theorem4bIsSylowSubgroupOf`. -/
private theorem theorem4b_lemma710_card_le_sylow_of_isPGroup
    {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : Nat.Prime p) {P Q E : Subgroup X}
    (hPp : IsPGroup p P) (hPE : P ≤ E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E) :
    Nat.card P ≤ Nat.card Q := by
  let : Fact p.Prime := ⟨hp⟩
  let PE : Subgroup E := P.subgroupOf E
  have hPEp : IsPGroup p PE :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
  obtain ⟨S, hPES⟩ := hPEp.exists_le_sylow
  rcases hQsyl with ⟨QE, hQeq⟩
  calc
    Nat.card P = Nat.card PE := (natCard_subgroupOf_eq P E hPE).symm
    _ ≤ Nat.card (S : Subgroup E) := Subgroup.card_le_of_le hPES
    _ = Nat.card (QE : Subgroup E) := by
      rw [S.card_eq_multiplicity, QE.card_eq_multiplicity]
    _ = Nat.card Q := by
      rw [hQeq, Subgroup.card_map_of_injective E.subtype_injective]

/-- A `p`-subgroup fixing a source triple has cardinality at most the selected
Sylow subgroup `P₁` of the reference triple stabilizer. -/
public theorem action_triple_pSubgroup_card_le
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    {Z : Set X} (h : IsProductDisconnected Z M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : ActionCounterexample Z M) {beta : conjugateCosetSpace M}
    (hne : beta ≠ QuotientGroup.mk 1)
    {P₁ : Subgroup X}
    (hP₁ : theorem4bIsSylowSubgroupOf d.p P₁ (theorem4bSection7E M d.z beta))
    {w : X} (hw : w ∈ Z)
    {gamma delta : conjugateCosetSpace M}
    (hwGamma : w • gamma = gamma) (hgammaDelta : gamma ≠ delta)
    {P : Subgroup X} (hPp : IsPGroup d.p P)
    (hPtriple : P ≤
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X delta) ⊓
        MulAction.stabilizer X (w • delta)) :
    Nat.card P ≤ Nat.card P₁ := by
  obtain ⟨g, hgGamma, hgDelta, hgw⟩ :=
    action_distinguished_triple_transport h htwo d.hzM d.hzZ hw
      hwGamma hgammaDelta hne
  have hconj := lemma73_tripleStabilizer_conjBy_eq_E
    hgGamma hgDelta hgw
  let Pg : Subgroup X := P.conjBy g
  have hPgp : IsPGroup d.p Pg := by
    exact hPp.map (MulAut.conj g).toMonoidHom
  have hPgE : Pg ≤ theorem4bSection7E M d.z beta := by
    change P.map (MulAut.conj g).toMonoidHom ≤ _
    rw [← hconj]
    exact Subgroup.map_mono hPtriple
  have hcardPg : Nat.card Pg = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hcardPg]
  exact theorem4b_lemma710_card_le_sylow_of_isPGroup
    d.hp hPgp hPgE hP₁

end BenderSuzuki.ZD
