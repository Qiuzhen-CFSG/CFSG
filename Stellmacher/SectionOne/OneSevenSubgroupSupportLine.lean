module
public import Stellmacher.SectionOne.OneSevenSylowLines

/-!
# Nontrivial subgroup actions fill a Sylow support line

For an indexed internal product of normal one-seven factors, let U be the
support of one factor and let K lie in the intersection of the product with
an ambient Sylow two-subgroup. If K moves a member of U, every action
difference on U from that Sylow intersection belongs to the full K-action
commutator. The action and indexed factor family are retained exactly.

The Sylow support-line theorem puts all these differences in an order-two
coordinate line. The restricted K-action commutator lies in this line and
contains a nonidentity difference, so it equals the line. Its inclusion in
the full K-action commutator gives the result. No choice of factor or
identification of the Sylow intersection with J is made here.

This is the support-control implication used with the decomposition in
Stellmacher (8.4), source (1)--(2), Journal of Algebra 190 (1997), pp38--39.
It builds on the one-seven support-line calculation from Stellmacher (1.7).
-/

namespace Stellmacher.SectionOne
universe u

/-- A nontrivial subgroup action on one support contains every Sylow-intersection difference there. -/
public theorem oneSevenFactor_subgroup_support_line_control
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (T : Sylow 2 G) (E : Subgroup G) [E.Normal]
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D) (hinj : Function.Injective D)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i))
    (hDN : ∀ i, ((D i).subgroupOf E).Normal)
    (i : Fin n) (K : Subgroup G) (hKB : K ≤ (T : Subgroup G) ⊓ E)
    (hmove : ∃ k ∈ K, ∃ v ∈ commutatorAction (D i) V, k • v ≠ v) :
    ∀ b ∈ (T : Subgroup G) ⊓ E, ∀ v ∈ commutatorAction (D i) V,
      v⁻¹ * (b • v) ∈ commutatorAction K V := by
  let U := commutatorAction (D i) V
  let R := commutatorAction (↥((T : Subgroup G) ⊓ D i)) V
  let C := commutatorSubgroup K V U
  obtain ⟨hRcard, _, hcontrol, _⟩ :=
    oneSevenFactor_sylow_line_control h T E D hprod hinj hD hDN i
  change Nat.card R = 2 at hRcard
  have hCR : C ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, v, hv, rfl⟩
    exact hcontrol k (hKB k.property) v hv
  have hCne : C ≠ ⊥ := by
    intro hbot
    obtain ⟨k, hk, v, hv, hne⟩ := hmove
    have hmem : v⁻¹ * (k • v) ∈ C :=
      Subgroup.subset_closure ⟨⟨k, hk⟩, v, hv, rfl⟩
    rw [hbot] at hmem
    exact hne (inv_mul_eq_one.mp hmem).symm
  have hCcard : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot C).mpr hCne
  have hCe : C = R := Subgroup.eq_of_le_of_card_ge hCR (by omega)
  have hCfull : C ≤ commutatorAction K V := by
    apply Subgroup.closure_mono
    rintro v ⟨k, u, _, rfl⟩
    exact ⟨k, u, Subgroup.mem_top _, rfl⟩
  intro b hb v hv
  exact hCfull (hCe.symm ▸ hcontrol b hb v hv)

end Stellmacher.SectionOne
