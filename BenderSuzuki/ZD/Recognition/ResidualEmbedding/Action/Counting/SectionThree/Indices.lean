module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Swapping
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Counting
/-!
# The two centralizer indices in distinguished Section 3 counting

For an outside distinguished involution `t`, put `D = M ∩ M^t`. The
odd-product lemma shows that every `s ∈ Z ∩ Mt` is conjugate to `t` by a
power of `s * t` in `D`. Thus its `D`-conjugacy orbit is exactly `Z ∩ Mt`.
The distinguished coset count identifies its cardinality with `|Z ∩ M|`.

For `z ∈ Z ∩ M`, conjugation of `z` by the distinguished involutions outside
`M` is a permutation. Restricting this permutation supplies a conjugator in
`D` from `z` to each member of `Z ∩ M`. Orbit–stabilizer gives the second
index. Point swapping and simultaneous conjugation transport the two formulas
to the required cosets. All indices are relative to the two-point stabilizer.

Source: GLS, Volume 4, Chapter 2, Lemmas 3.2–3.4 and Proposition 3.6(a–d),
printed pp.28–30. This direct conjugacy-orbit proof uses the distinguished
coset argument to obtain the two indices without the intervening odd-core
factorization. In particular it assumes neither oddness of `D` nor strong
embedding. The private injectivity argument is adapted from
`MinimalReduction.Preliminaries.Counting`; the power conjugator calculation
also appears in `Theory.GroupTheory.ZStar.OddProductConjugator`.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
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

omit [Finite G] in
private theorem index_eq_card (H : Subgroup G) (z : G) (S : Set G)
    (hS : ∀ x, x ∈ S ↔ ∃ a : H, MulAut.conj (a : G) z = x) :
    ((H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf H).index = Nat.card S := by
  let : MulAction H G := {
    smul a x := MulAut.conj (a : G) x
    one_smul x := by change (1 : G) * x * 1⁻¹ = x; simp
    mul_smul a b x := by
      change ((a : G) * (b : G)) * x * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
      group }
  have hstab : MulAction.stabilizer H z =
      (H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf H := by
    ext a
    change MulAut.conj (a : G) z = z ↔ _
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, a.property, true_and]
    exact mul_inv_eq_iff_eq_mul
  rw [← hstab, MulAction.index_stabilizer]
  have horbit : MulAction.orbit H z = S := by
    ext x
    exact (hS x).symm
  rw [horbit]
  rfl

private theorem m_eq_card (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) :
    theorem4bM M z = Nat.card {x : G // x ∈ Z ∧ x ∈ M} := by
  apply index_eq_card M z {x | x ∈ Z ∧ x ∈ M}
  intro x
  constructor
  · rintro ⟨hx, hxM⟩
    exact productDisconnected_conjugator_mem h hz hzM hx hxM
  · rintro ⟨a, rfl⟩
    exact ⟨h.invariant _ _ hz, (h.conjugate_mem_iff z hz hzM a).mpr a.property⟩

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

private theorem base_index (h : IsProductDisconnected Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    let D := M ⊓ rightConjugate M t
    ((D ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf D).index = theorem4bM M z := by
  rw [m_eq_card h hz hzM]
  apply index_eq_card _ z {x | x ∈ Z ∧ x ∈ M}
  intro x
  constructor
  · rintro ⟨hx, hxM⟩
    exact base_transitive h hz hzM ht htM hx hxM
  · rintro ⟨d, rfl⟩
    exact ⟨h.invariant _ _ hz, (h.conjugate_mem_iff z hz hzM d).mpr d.property.1⟩

omit [Finite G] in
private theorem product_mem_twoPoint (h : IsProductDisconnected Z M)
    {s t : G} (hs : s ∈ Z) (ht : t ∈ Z) (hm : s * t ∈ M) :
    s * t ∈ M ⊓ rightConjugate M t := by
  refine ⟨hm, ?_⟩
  have hi : t * s ∈ M := by
    simpa [mul_inv_rev, (h.involutions s hs).inv_eq_self,
      (h.involutions t ht).inv_eq_self] using M.inv_mem hm
  have hh := rightConjugateElem_mem_rightConjugate (g := t) hi
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  simpa [rightConjugateElem, (h.involutions t ht).inv_eq_self, ← mul_assoc, tt] using hh

private theorem swapping_base_index (h : IsProductDisconnected Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    let D := M ⊓ rightConjugate M t
    ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z := by
  rw [m_eq_card h hz hzM, ← productDisconnected_card_right_coset h ht htM]
  apply index_eq_card _ t {s | s ∈ Z ∧ s * t ∈ M}
  intro s
  constructor
  · rintro ⟨hs, hm⟩
    obtain ⟨a, ha⟩ := productDisconnected_odd_orderOf_mul h hs ht htM (Or.inr hm)
    have ti := (h.involutions t ht).inv_eq_self
    have si := (h.involutions s hs).inv_eq_self
    have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
    have hsem : SemiconjBy t (s * t)⁻¹ (s * t) := by
      change t * (s * t)⁻¹ = (s * t) * t
      rw [mul_inv_rev, ti, si, ← mul_assoc, tt, one_mul, mul_assoc, tt, mul_one]
    refine ⟨⟨(s * t) ^ (a + 1),
      (M ⊓ rightConjugate M t).pow_mem (product_mem_twoPoint h hs ht hm) _⟩, ?_⟩
    change (s * t) ^ (a + 1) * t * ((s * t) ^ (a + 1))⁻¹ = s
    have hexp : (a + 1) + (a + 1) = orderOf (s * t) + 1 := by omega
    calc
      _ = (s * t) ^ (a + 1) * ((s * t) ^ (a + 1) * t) := by
        rw [← inv_pow, mul_assoc, (hsem.pow_right (a + 1)).eq]
      _ = (s * t) ^ (orderOf (s * t) + 1) * t := by
        rw [← mul_assoc, ← pow_add, hexp]
      _ = s := by rw [pow_succ, pow_orderOf_eq_one, one_mul, mul_assoc, tt, mul_one]
  · rintro ⟨d, rfl⟩
    refine ⟨h.invariant _ _ ht, ?_⟩
    have hd := rightConjugateElem_mem_of_mem_rightConjugate
      (M := M) (g := t⁻¹) (x := (d : G)⁻¹)
      (by simpa only [inv_inv] using (rightConjugate M t).inv_mem d.property.2)
    have ti := (h.involutions t ht).inv_eq_self
    have hh := M.mul_mem d.property.1 hd
    simpa [rightConjugateElem, MulAut.conj_apply, ti, mul_assoc] using hh

private theorem base_arbitrary (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) (beta : G ⧸ M)
    (hb : beta ≠ QuotientGroup.mk 1) :
    let D := M ⊓ MulAction.stabilizer G beta
    ((D ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf D).index = theorem4bM M z := by
  obtain ⟨t, ht, he⟩ := sectionThree_swap h (QuotientGroup.mk 1) beta hb.symm
  have htM : t ∉ M := by
    intro hm
    apply hb
    rw [← he]
    exact MulAction.mem_stabilizer_iff.mp (by rw [baseCoset_stabilizer]; exact hm)
  have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
    rw [← he]
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, (h.involutions t ht).inv_eq_self]
      using conjugateCoset_stabilizer M t
  dsimp only
  rw [hstab]
  exact base_index h hz hzM ht htM

omit [Finite G] in
private theorem index_map_equiv (H : Subgroup G) (z : G) (e : G ≃* G) :
    (((H.map e.toMonoidHom) ⊓ Subgroup.centralizer ({e z} : Set G)).subgroupOf
      (H.map e.toMonoidHom)).index =
      ((H ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf H).index := by
  have hc : (Subgroup.centralizer ({z} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set G) := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      simpa using congrArg e hx
    · intro hx
      simpa using congrArg e.symm hx
  change ((H.map e.toMonoidHom) ⊓ Subgroup.centralizer ({e z} : Set G)).relIndex
    (H.map e.toMonoidHom) = _
  rw [← hc, ← Subgroup.map_inf _ _ _ e.injective]
  exact Subgroup.relIndex_map_map_of_injective _ _ e.injective

private theorem swapping_arbitrary (h : IsProductDisconnected Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z)
    (beta : G ⧸ M) (hb : t • beta ≠ beta) :
    let D := MulAction.stabilizer G beta ⊓ MulAction.stabilizer G (t • beta)
    ((D ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf D).index = theorem4bM M z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective beta
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let t' := MulAut.conj g⁻¹ t
  have ht' : t' ∈ Z := h.invariant _ _ ht
  have hg : (QuotientGroup.mk g : G ⧸ M) = g • alpha := by
    simp [alpha, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hmove : t • (QuotientGroup.mk g : G ⧸ M) = g • (t' • alpha) := by
    rw [hg]
    simp [t', MulAut.conj_apply, mul_smul]
  have ht'M : t' ∉ M := by
    intro hm
    have hfix : t' • alpha = alpha :=
      MulAction.mem_stabilizer_iff.mp (by rw [baseCoset_stabilizer]; exact hm)
    exact hb (by rw [hmove, hfix, ← hg])
  let D' := M ⊓ rightConjugate M t'
  have hD' : D' = MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G (t' • alpha) := by
    rw [baseCoset_stabilizer]
    have hs : MulAction.stabilizer G (t' • alpha) = rightConjugate M t' := by
      simpa [alpha, MulAction.Quotient.smul_mk, smul_eq_mul,
        (h.involutions t' ht').inv_eq_self] using conjugateCoset_stabilizer M t'
    rw [hs]
  have hD : D'.map (MulAut.conj g).toMonoidHom =
      MulAction.stabilizer G (QuotientGroup.mk g : G ⧸ M) ⊓
      MulAction.stabilizer G (t • (QuotientGroup.mk g : G ⧸ M)) := by
    rw [hD', Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hg, ← hmove]
  have he : MulAut.conj g t' = t := by simp [t', MulAut.conj_apply, mul_assoc]
  have hi := index_map_equiv D' t' (MulAut.conj g)
  rw [he, hD] at hi
  exact hi.trans (swapping_base_index h hz hzM ht' ht'M)

/-- GLS Proposition 3.6(d), with both indices taken inside the corresponding
 two-point stabilizer. Product disconnection suffices for these identities. -/
public theorem sectionThreeIndices_of_productDisconnected (h : IsProductDisconnected Z M) :
    SectionThreeIndices Z M := by
  exact ⟨fun z hz hzM t ht beta hb => swapping_arbitrary h hz hzM ht beta hb,
    fun z hz hzM beta hb => base_arbitrary h hz hzM beta hb⟩

/-- The Section 3 index input at the minimal-counterexample assembly boundary. -/
public theorem sectionThreeIndices_of_local (h : MinimalCounterexample Z M)
    (_hs : SimpleReduction Z M) (_hl : SectionThreeLocal Z M) : SectionThreeIndices Z M :=
  sectionThreeIndices_of_productDisconnected h.disconnected

end BenderSuzuki.ZD
