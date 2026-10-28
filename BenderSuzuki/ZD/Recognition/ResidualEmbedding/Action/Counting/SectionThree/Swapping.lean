module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary

/-!
# Distinguished involutions interchange distinct points

An odd-order product of two distinguished involutions has a reflection which
conjugates one to the other. Apply this to the base involution and its conjugate
at another point. Its centralizer lies in the base stabilizer, so that this
reflection also interchanges the two cosets. Finally translate the base point.
This bypasses the coset-counting proof and needs only product disconnection.

Source: GLS, Volume 4, Chapter 2, Lemmas 3.2(b) and 3.4(c), pp.28--29.
The explicit power conjugator calculation follows
`Theory.GroupTheory.ZStar.OddProductConjugator`.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem distinguished_reflection (h : IsProductDisconnected Z M)
    {u z : G} (hu : u ∈ Z) (hz : z ∈ Z) (n : ℕ) : (u * z) ^ n * z ∈ Z := by
  have zi := (h.involutions z hz).inv_eq_self
  have ui := (h.involutions u hu).inv_eq_self
  have zz : z * z = 1 := by simpa [pow_two] using (h.involutions z hz).sq_eq_one
  have hmove : z * (u * z)⁻¹ = (u * z) * z := by
    rw [mul_inv_rev, zi, ui, ← mul_assoc, zz, one_mul, mul_assoc, zz, mul_one]
  induction n using Nat.twoStepInduction with
  | zero => simpa using hz
  | one => simpa [pow_one, mul_assoc, zz] using hu
  | more n hn _ =>
    have he : (u * z) ^ (n + 2) * z = MulAut.conj (u * z) ((u * z) ^ n * z) := by
      symm
      change (u * z) * ((u * z) ^ n * z) * (u * z)⁻¹ = _
      calc
        _ = (u * z) * ((u * z) ^ n * (z * (u * z)⁻¹)) := by group
        _ = (u * z) * ((u * z) ^ n * ((u * z) * z)) := by rw [hmove]
        _ = (u * z) ^ (n + 2) * z := by rw [pow_succ, pow_succ']; group
    rw [he]
    exact h.invariant _ _ hn

/-- The distinguished conjugator in Lemma 3.2(b). -/
public theorem sectionThree_distinguished_conjugator (h : IsProductDisconnected Z M)
    {z u : G} (hz : z ∈ Z) (hzM : z ∈ M) (hu : u ∈ Z) (huM : u ∉ M) :
    ∃ t ∈ Z, MulAut.conj t z = u := by
  have hodd : Odd (orderOf (u * z)) := by
    rw [show u * z = (z * u)⁻¹ by rw [mul_inv_rev, (h.involutions z hz).inv_eq_self, (h.involutions u hu).inv_eq_self], orderOf_inv]
    exact productDisconnected_odd_orderOf_mul h hz hu huM (Or.inl hzM)
  obtain ⟨a, ha⟩ := hodd
  have zi := (h.involutions z hz).inv_eq_self
  have ui := (h.involutions u hu).inv_eq_self
  have zz : z * z = 1 := by simpa [pow_two] using (h.involutions z hz).sq_eq_one
  have hsem : SemiconjBy z (u * z)⁻¹ (u * z) := by
    change z * (u * z)⁻¹ = (u * z) * z
    rw [mul_inv_rev, zi, ui, ← mul_assoc, zz, one_mul, mul_assoc, zz, mul_one]
  have he : (u * z) ^ (a + 1) * z * ((u * z) ^ (a + 1))⁻¹ = u := by
    have hexp : (a + 1) + (a + 1) = orderOf (u * z) + 1 := by omega
    calc
      _ = (u * z) ^ (a + 1) * ((u * z) ^ (a + 1) * z) := by
        rw [← inv_pow, mul_assoc, (hsem.pow_right (a + 1)).eq]
      _ = (u * z) ^ (orderOf (u * z) + 1) * z := by
        rw [← mul_assoc, ← pow_add, hexp]
      _ = u := by rw [pow_succ, pow_orderOf_eq_one, one_mul, mul_assoc, zz, mul_one]
  refine ⟨(u * z) ^ (a + 1) * z, distinguished_reflection h hu hz _, ?_⟩
  change ((u * z) ^ (a + 1) * z) * z * ((u * z) ^ (a + 1) * z)⁻¹ = u
  simpa only [mul_inv_rev, zi, mul_assoc, zz, one_mul] using he

/-- GLS Lemma 3.4(c), on the actual coset space. -/
public theorem sectionThree_swap (h : IsProductDisconnected Z M)
    (beta gamma : G ⧸ M) (hne : beta ≠ gamma) : ∃ t ∈ Z, t • beta = gamma := by
  have hbase : ∀ gamma : G ⧸ M, gamma ≠ QuotientGroup.mk 1 →
      ∃ t ∈ Z, t • (QuotientGroup.mk 1 : G ⧸ M) = gamma := by
    intro gamma hne
    induction gamma using Quotient.inductionOn with
    | h g =>
      obtain ⟨z, hz, hzM⟩ := h.nonempty
      have hg : g ∉ M := by
        intro hg
        exact hne (QuotientGroup.eq.mpr (by simpa using M.inv_mem hg))
      have huM : MulAut.conj g z ∉ M := fun hm => hg ((h.conjugate_mem_iff z hz hzM g).mp hm)
      obtain ⟨t, ht, he⟩ := sectionThree_distinguished_conjugator h hz hzM
        (h.invariant g z hz) huM
      have hc : MulAut.conj (g⁻¹ * t) z = z := by
        calc
          _ = MulAut.conj g⁻¹ (MulAut.conj t z) := by simp only [MulAut.conj_apply]; group
          _ = z := by rw [he]; simp [MulAut.conj_apply, mul_assoc]
      have hm : g⁻¹ * t ∈ M := h.centralizer_le hz hzM
        (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc))
      refine ⟨t, ht, ?_⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa only [mul_inv_rev, inv_inv] using M.inv_mem hm
  induction beta using Quotient.inductionOn with
  | h b =>
    have hn : b⁻¹ • gamma ≠ (QuotientGroup.mk 1 : G ⧸ M) := by
      intro he
      apply hne
      have hh := congrArg (fun q : G ⧸ M => b • q) he
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul] using hh.symm
    obtain ⟨t, ht, he⟩ := hbase (b⁻¹ • gamma) hn
    refine ⟨MulAut.conj b t, h.invariant b t ht, ?_⟩
    have hb : (QuotientGroup.mk b : G ⧸ M) = b • QuotientGroup.mk 1 := by
      simp [MulAction.Quotient.smul_mk, smul_eq_mul]
    change MulAut.conj b t • (QuotientGroup.mk b : G ⧸ M) = gamma
    rw [hb]
    change (b * t * b⁻¹) • (b • (QuotientGroup.mk 1 : G ⧸ M)) = gamma
    simp only [mul_smul, inv_smul_smul, he, smul_inv_smul]
end BenderSuzuki.ZD
