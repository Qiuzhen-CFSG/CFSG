module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary
public import Theory.GroupTheory.PPrimeCoreSupplement

/-!
# Distinguished odd-core factorization and placement of the Section 6 witness

For a distinguished involution z in M and any nonbase coset beta, every
m in M is a product o*c with o in the actual odd core of the two-point
stabilizer D and c in C_M(z). More precisely, for a distinguished involution
t interchanging the base point and beta, o can be chosen inverted by t.
Restricting the factorization to D proves Proposition 3.8(d).

The finite outside-conjugation permutation from `Preliminaries.Counting`
supplies an inverted factor. The odd-product lemma makes its order odd,
and Section 3 puts its square, hence the factor itself, in the odd core.
The private permutation lemmas below adapt that module's private proof.

For the Section 6 witness, W lies in the z-invariant triple stabilizer E.
The swapping-core assertion gives [W,z] <= O_{2'}(E). The factorization
shows that E supplements O_{2'}(D), so the general core-supplement theorem
places O_{2'}(E) inside O_{2'}(D). Neither D nor E is assumed odd or
normalized by every element of M; in particular z need not normalize D.

All results use the explicit `ActionSectionThree` input. Its construction
from minimality belongs to the Section 3 owner; no `ResidualAction` is used.
The stronger product-disconnection statements specialize to the minimal
counterexample and maximal witness in the parent Corollary 6.4 assembly.

Source: GLS, Volume 4, Chapter 2, Proposition 3.6(a,b), Proposition 3.8(d),
and Corollary 6.4, printed pp.29--31 and 45. The complete text of Proposition
3.6 is in the recovered `Scratch/ZDPreliminaries/Source.txt` in retained
workspace a1cd3849cd24463dbd4927bcdcfc4b4e; Chapter2.tex omits its statement.
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

-- The same finite outside-conjugation permutation as Preliminaries.Counting.
private theorem outside_conjugation_surjective (h : IsProductDisconnected Z M)
    {z u : G} (hz : z ∈ Z) (hzM : z ∈ M) (hu : u ∈ Z) (huM : u ∉ M) :
    ∃ s ∈ Z, s ∉ M ∧ MulAut.conj s z = u := by
  let O := {s : G // s ∈ Z ∧ s ∉ M}
  let f : O → O := fun s => ⟨MulAut.conj (s : G) z, h.invariant s z hz,
    fun hm => s.property.2 ((h.conjugate_mem_iff z hz hzM s).mp hm)⟩
  have hf : Function.Injective f := by
    intro s t he
    exact Subtype.ext (outside_injective h hz hzM s.property.1 s.property.2
      t.property.1 t.property.2 (congrArg Subtype.val he))
  obtain ⟨s, hs⟩ := (Finite.surjective_of_injective hf) ⟨u, hu, huM⟩
  exact ⟨s, s.property.1, s.property.2, congrArg Subtype.val hs⟩

omit [Finite G] in
private theorem inverted_odd_mem_of_commutator_le {D O : Subgroup G} {t x : G}
    (hx : x ∈ D) (hodd : Odd (orderOf x))
    (hinv : t * x * t⁻¹ = x⁻¹) (hc : ⁅D, Subgroup.zpowers t⁆ ≤ O) : x ∈ O := by
  have hx2 : x ^ 2 ∈ O := by
    have hh := hc (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t))
    have he : ⁅x,t⁆ = x ^ 2 := by
      calc
        ⁅x,t⁆ = x * (t * x * t⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
        _ = x ^ 2 := by rw [hinv]; simp [pow_two]
    rwa [he] at hh
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hodd.coprime_two_left
  rw [← hn]
  exact O.pow_mem hx2 n

/-- Elementwise Proposition 3.6(b), retaining the inverted odd-core factor. -/
public theorem action_oddCore_factorization_inverted
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {beta : G ⧸ M} (hb : beta ≠ QuotientGroup.mk 1)
    {t : G} (ht : t ∈ Z) (htBase : t • (QuotientGroup.mk 1 : G ⧸ M) = beta)
    {m : G} (hm : m ∈ M) :
    ∃ o ∈ corollary64OddCore (theorem4bSection7D M beta),
      t * o * t⁻¹ = o⁻¹ ∧
      ∃ c ∈ elementCentralizerIn M z, m = o * c := by
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have htM : t ∉ M := by
    intro htM
    have htfix : t • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 :=
      MulAction.mem_stabilizer_iff.mp (by simpa only [baseCoset_stabilizer] using htM)
    exact hb (htBase.symm.trans htfix)
  let u := MulAut.conj m z
  have huZ : u ∈ Z := h.invariant m z hz
  have huM : u ∈ M := M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm)
  have htuM : MulAut.conj t u ∉ M :=
    fun hh => htM ((h.conjugate_mem_iff u huZ huM t).mp hh)
  obtain ⟨s, hsZ, _, hsz⟩ := outside_conjugation_surjective h hz hzM
    (h.invariant t u huZ) htuM
  have si := (h.involutions s hsZ).inv_eq_self
  let o := t * s
  have hoz : MulAut.conj o z = u := by
    calc
      _ = MulAut.conj t (MulAut.conj s z) := by simp only [o, MulAut.conj_apply]; group
      _ = MulAut.conj t (MulAut.conj t u) := by rw [hsz]
      _ = u := by simp [MulAut.conj_apply, ti, mul_assoc, tt, ← mul_assoc t t]
  have hoM : o ∈ M := (h.conjugate_mem_iff z hz hzM o).mp (hoz ▸ huM)
  have hinv : t * o * t⁻¹ = o⁻¹ := by
    simp [o, mul_inv_rev, ti, si, ← mul_assoc, tt]
  have hDeq : theorem4bSection7D M beta = M ⊓ rightConjugate M t := by
    have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
      rw [← htBase]
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ti] using conjugateCoset_stabilizer M t
    exact congrArg (M ⊓ ·) hstab
  have hoD : o ∈ theorem4bSection7D M beta := by
    rw [hDeq]
    refine ⟨hoM, ?_⟩
    change o ∈ rightConjugate M t
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨o⁻¹, M.inv_mem hoM, ?_⟩
    change t⁻¹ * o⁻¹ * (t⁻¹)⁻¹ = o
    rw [ti]
    calc
      t * o⁻¹ * t⁻¹ = (t * o * t⁻¹)⁻¹ := by group
      _ = o := by rw [hinv, inv_inv]
  have hodd : Odd (orderOf o) := by
    have he : o = (s * t)⁻¹ := by simp [o, mul_inv_rev, si, ti]
    rw [he, orderOf_inv]
    apply productDisconnected_odd_orderOf_mul h hsZ ht htM (Or.inr ?_)
    have hh := M.inv_mem hoM
    simpa [o, mul_inv_rev, si, ti] using hh
  have hc : ⁅theorem4bSection7D M beta, Subgroup.zpowers t⁆ ≤
      corollary64OddCore (theorem4bSection7D M beta) := by
    apply hs.swapping_core t ht (QuotientGroup.mk 1) (by rwa [htBase])
    · simpa only [baseCoset_stabilizer, htBase, theorem4bSection7D] using
        (le_rfl : theorem4bSection7D M beta ≤ theorem4bSection7D M beta)
    · rw [hDeq]
      exact inf_rightConjugate_mem_normalizer_of_isInvolution M (h.involutions t ht)
  refine ⟨o, inverted_odd_mem_of_commutator_le hoD hodd hinv hc, hinv,
    o⁻¹ * m, ⟨M.mul_mem (M.inv_mem hoM) hm, ?_⟩, by simp⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    (o⁻¹ * m) * z * (o⁻¹ * m)⁻¹ = MulAut.conj o⁻¹ u := by
      simp only [u, MulAut.conj_apply]; group
    _ = z := by rw [← hoz]; simp [MulAut.conj_apply, mul_assoc]

/-- Proposition 3.6(b): actual elements of the odd core and the centralizer
multiply to every element of M. -/
public theorem action_oddCore_factorization
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {beta : G ⧸ M} (hb : beta ≠ QuotientGroup.mk 1)
    {m : G} (hm : m ∈ M) :
    ∃ o ∈ corollary64OddCore (theorem4bSection7D M beta),
      ∃ c ∈ elementCentralizerIn M z, m = o * c := by
  obtain ⟨t, ht, htBase⟩ := hs.swap (QuotientGroup.mk 1) beta hb.symm
  obtain ⟨o, ho, _, c, hc, he⟩ :=
    action_oddCore_factorization_inverted h hs hz hzM hb ht htBase hm
  exact ⟨o, ho, c, hc, he⟩

omit [Finite G] in
private theorem oddCore_le (D : Subgroup G) : corollary64OddCore D ≤ D := by
  exact Subgroup.map_subtype_le _

/-- Proposition 3.8(d), with both factors remaining in the two-point stabilizer. -/
public theorem action_twoPoint_oddCore_factorization
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {beta : G ⧸ M} (hb : beta ≠ QuotientGroup.mk 1)
    {m : G} (hm : m ∈ theorem4bSection7D M beta) :
    ∃ o ∈ corollary64OddCore (theorem4bSection7D M beta),
      ∃ c ∈ elementCentralizerIn (theorem4bSection7D M beta) z, m = o * c := by
  obtain ⟨o, ho, c, hc, he⟩ := action_oddCore_factorization h hs hz hzM hb hm.1
  refine ⟨o, ho, c, ⟨?_, hc.2⟩, he⟩
  have hcEq : c = o⁻¹ * m := by rw [he]; group
  rw [hcEq]
  exact (theorem4bSection7D M beta).mul_mem
    ((theorem4bSection7D M beta).inv_mem (oddCore_le _ ho)) hm

/-- The triple stabilizer supplements the odd core of the two-point stabilizer.
This is the hypothesis needed for core transfer, with no normality of E in D. -/
public theorem action_tripleStabilizer_supplement
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {beta : G ⧸ M} (hb : beta ≠ QuotientGroup.mk 1) :
    theorem4bSection7D M beta = corollary64OddCore (theorem4bSection7D M beta) ⊔
      (theorem4bSection7D M beta ⊓ theorem4bSection7E M z beta) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨o, ho, c, hc, rfl⟩ := action_twoPoint_oddCore_factorization h hs hz hzM hb hm
    apply Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
    apply Subgroup.mem_sup_right
    refine ⟨hc.1, ?_⟩
    have heq := theorem4b_tripleStabilizer_inf_centralizer_eq M z beta
    have hcE : c ∈ theorem4bSection7E M z beta ⊓ Subgroup.centralizer ({z} : Set G) := by
      rw [theorem4bSection7E, theorem4bSection7D, heq]
      exact hc
    exact hcE.1
  · exact sup_le (oddCore_le _) inf_le_left

/-- The source Corollary 6.4 placement of the commutator-saturated witness W.
Apply Section 3 inside the invariant triple stabilizer, then transfer its core
using the supplement identity. -/
public theorem actionCounterexample_le_oddCore
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    (d : ActionCounterexample Z M)
    {beta : G ⧸ M} (hbK : beta ∈ d.toTheorem4bSixA.kFixedPoints)
    (hb : beta ≠ QuotientGroup.mk 1) :
    d.W ≤ corollary64OddCore (theorem4bSection7D M beta) := by
  let D := theorem4bSection7D M beta
  let E := theorem4bSection7E M d.z beta
  have hWD : d.W ≤ D := by
    intro w hw
    exact ⟨d.hWM hw, MulAction.mem_stabilizer_iff.mpr
      (d.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbK w hw)⟩
  have hWE : d.W ≤ E :=
    theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer d.hzNorm hWD
  have hzMove : d.z • beta ≠ beta :=
    fun he => hb (action_fixedPoint_eq_base h d.hzZ d.hzM he)
  have hEc : ⁅E, Subgroup.zpowers d.z⁆ ≤ corollary64OddCore E := by
    apply hs.swapping_core d.z d.hzZ beta hzMove
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact theorem4b_mem_normalizer_tripleStabilizer d.hz d.hzM
  have hWcore : d.W ≤ corollary64OddCore E := by
    rw [← d.hcomm]
    exact (Subgroup.commutator_mono hWE le_rfl).trans hEc
  have htransfer : D ⊓ corollary64OddCore E ≤ corollary64OddCore D := by
    apply Subgroup.inf_pPrimeCore_map_le_of_supplement D E
    exact action_tripleStabilizer_supplement h hs d.hzZ d.hzM hb
  exact (le_inf hWD hWcore).trans htransfer

end BenderSuzuki.ZD
