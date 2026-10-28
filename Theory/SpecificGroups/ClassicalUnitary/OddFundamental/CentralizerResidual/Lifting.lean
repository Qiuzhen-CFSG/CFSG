module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.ResidualSetup
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Lifting the marked unitary centralizer

For the two-space fundamental subgroup in odd characteristic, commuting in
PSU already implies commuting in SU. The scalar commutator is a homomorphism
from the actual SU₂ into the projective kernel. SL₂ transvection generation
and the prime-to-characteristic order of that kernel make this homomorphism
trivial, including over the fixed field of order three.

The resulting surjection between the literal centralizers carries the covering
prime-to-r residual onto the projective residual. The complementary embeddings
commute with this surjection. The covering block calculation and generation of
the complementary SUₙ are separate inputs to the full residual computation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.17,
printed pp.38–39 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
open scoped commutatorElement

private theorem commute_sl2_of_central_kernel
    {E G H : Type*} [Field E] [Group G] [Group H]
    (p : ℕ) [CharP E p] (f : G →* H)
    (hc : f.ker ≤ center G) (hp : Nat.Coprime p (Nat.card f.ker))
    (k : SpecialLinearGroup (Fin 2) E →* G) (g : G)
    (hg : ∀ a, Commute (f (k a)) (f g)) : ∀ a, Commute (k a) g := by
  have hmem (a : SpecialLinearGroup (Fin 2) E) : ⁅k a, g⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hg a)
  let d : SpecialLinearGroup (Fin 2) E →* f.ker := {
    toFun a := ⟨⁅k a, g⁆, hmem a⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅k (a * b), g⁆ = ⁅k a, g⁆ * ⁅k b, g⁆
      rw [map_mul]
      have hz := mem_center_iff.mp (hc (hmem b)) (k a)
      rw [commutatorElement_mul_left_eq_conj_mul, hz, mul_inv_cancel_right]
      exact mem_center_iff.mp (hc (hmem a)) ⁅k b, g⁆ }
  intro a
  have hd : d a = 1 :=
    primeToResidual_le_ker (MonoidHom.id f.ker) hp (Matrix.SL2.map_mem_primeToResidual p d a)
  exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hd)

namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
variable {n : ℕ}

/-- The centralizer of the marked SU₂ in the covering SU group. -/
def coveringCentralizer := centralizer (left σ hσ (m := 2) (n := n)).range.carrier

/-- Restriction of the actual SU-to-PGL projection to the two centralizers. -/
def centralizerProjection : coveringCentralizer σ hσ (n := n) →*
    centralizer (projectLeft σ hσ (m := 2) (n := n)).range.carrier :=
  ((ProjectiveKernel.project _).comp (coveringCentralizer σ hσ).subtype).codRestrict _
    fun g => by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨a, rfl⟩
      exact congrArg (ProjectiveKernel.project _) (mem_centralizer_iff.mp g.property
        (left σ hσ a) ⟨a, rfl⟩)

/-- Every lift of a projective centralizer element commutes with the marked SU₂. -/
theorem centralizer_project_comap [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) :
    (centralizer (projectLeft σ hσ (m := 2) (n := n)).range.carrier).comap
      (ProjectiveKernel.project (form σ hσ (2+n))) = coveringCentralizer σ hσ := by
  have hq : IsPrimePow (r ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩
  have ho : Odd (r ^ e) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd σ hσ hq ho hc hj
  have hk : Nat.card (FixedBy.subfield F σ) = r ^ e :=
    (form σ hσ 2).fixed_card_prime_power hq hc hj
  let : Fintype (FixedBy.subfield F σ) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F σ) r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hk)
  let f := ProjectiveKernel.project (form σ hσ (2+n))
  have hpc : Nat.Coprime r (Nat.card f.ker) := by
    rw [ProjectiveKernel.card_project_kernel (form σ hσ (2+n)) hj hc]
    apply Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) ?_
    apply (Nat.coprime_pow_left_iff he r (r ^ e + 1)).mp
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  apply le_antisymm
  · intro g hg
    have hh : ∀ b, Commute (f (left σ hσ (a.symm b))) (f g) := by
      intro b
      exact mem_centralizer_iff.mp hg _ ⟨a.symm b, rfl⟩
    have hcomm := commute_sl2_of_central_kernel r f
      (ProjectiveKernel.project_kernel_le_center _) hpc
      ((left σ hσ).comp a.symm.toMonoidHom) g hh
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, rfl⟩
    simpa using (hcomm (a b)).eq
  · intro g hg
    exact (centralizerProjection σ hσ ⟨g, hg⟩).property

/-- Every projective centralizer element comes from the covering centralizer. -/
theorem centralizerProjection_surjective [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) :
    Function.Surjective (centralizerProjection σ hσ (n := n)) := by
  intro g
  obtain ⟨a, ha⟩ := ProjectiveKernel.project_surjective (form σ hσ (2+n)) g.val
  have hm : a ∈ coveringCentralizer σ hσ := by
    rw [← centralizer_project_comap σ hσ hr he hc hj]
    change ProjectiveKernel.project _ a ∈
      centralizer (projectLeft σ hσ (m := 2) (n := n)).range.carrier
    rw [ha]
    exact g.property
  exact ⟨⟨a, hm⟩, Subtype.ext ha⟩

/-- The complementary SUₙ inside the covering centralizer. -/
def complementInCoveringCentralizer : (form σ hσ n).specialSubgroup →*
    coveringCentralizer σ hσ (n := n) :=
  (right σ hσ).codRestrict _ fun b => by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    have h : Commute (a, (1 : (form σ hσ n).specialSubgroup))
        ((1 : (form σ hσ 2).specialSubgroup), b) := by
      change (a, 1) * (1, b) = (1, b) * (a, 1)
      simp
    exact (h.map (block σ hσ)).eq

/-- The complementary embedding retains exactly its original projective map. -/
theorem centralizerProjection_comp_complement :
    (centralizerProjection σ hσ (n := n)).comp (complementInCoveringCentralizer σ hσ) =
      complementInCentralizer σ hσ := rfl

/-- Coprime residuals descend through the actual centralizer projection. -/
theorem map_covering_primeToResidual [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) :
    (primeToResidual r (coveringCentralizer σ hσ (n := n))).map
      (centralizerProjection σ hσ) = residual σ hσ r :=
  map_primeToResidual_of_surjective r _ (centralizerProjection_surjective σ hσ hr he hc hj)

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
