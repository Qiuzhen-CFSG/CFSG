module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Restricting the pair stabilizer and controlling its inner kernel

The subgroup of Aut(Q) preserving S and R restricts onto the actual pair
automizer. Its map to Out(Q) has kernel acting trivially on R when every
inner automorphism preserving the pair centralizes R. Therefore a cyclic
outer group gives a cyclic pair automizer under this explicit kernel condition.

The last lemma derives that condition from a normalizer factorization and
disjointness: if R normalizes S, then N_S(R) = C_S(R). A factorization
N_Q(S) = S C with C centralizing R then disposes of every inner element
preserving the pair. Concrete Borel/Cartan calculations must supply the
normalization, factorization and outer cyclicity; PairInput does not assume them.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
universe u
variable {Q : Type u} [Group Q]

/-- Actual automorphisms of Q preserving both subgroups. -/
def pairStabilizer (S R : Subgroup Q) : Subgroup (MulAut Q) where
  carrier a := (∀ x, a x ∈ S ↔ x ∈ S) ∧ (∀ x, a x ∈ R ↔ x ∈ R)
  one_mem' := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun x => (ha.1 (b x)).trans (hb.1 x),
      fun x => (ha.2 (b x)).trans (hb.2 x)⟩
  inv_mem' := by
    intro a ha
    exact ⟨fun x => by simpa using (ha.1 (a⁻¹ x)).symm,
      fun x => by simpa using (ha.2 (a⁻¹ x)).symm⟩

/-- Restriction of a pair-preserving automorphism to R. -/
def restrictPair (S R : Subgroup Q) (a : pairStabilizer S R) : MulAut R where
  toFun x := ⟨a.val x, (a.property.2 x).mpr x.property⟩
  invFun x := ⟨a.val.symm x, by
    exact (a.property.2 (a.val.symm x)).mp (by simp)⟩
  left_inv x := by apply Subtype.ext; exact a.val.symm_apply_apply x
  right_inv x := by apply Subtype.ext; exact a.val.apply_symm_apply x
  map_mul' x y := by apply Subtype.ext; exact map_mul a.val (x : Q) (y : Q)

/-- Restriction lands in the extendible pair automizer. -/
def pairRestriction (S R : Subgroup Q) : pairStabilizer S R →* pairAutomizer S R where
  toFun a := ⟨restrictPair S R a, a.val, a.property.1, fun _ => rfl⟩
  map_one' := by apply Subtype.ext; ext x; rfl
  map_mul' a b := by apply Subtype.ext; ext x; rfl

/-- Every extendible pair automorphism comes from a pair-preserving automorphism of Q. -/
theorem pairRestriction_surjective (S R : Subgroup Q) :
    Function.Surjective (pairRestriction S R) := by
  rintro ⟨a, b, hbS, hab⟩
  have hbR : ∀ x, b x ∈ R ↔ x ∈ R := by
    intro x
    constructor
    · intro hx
      have he : b ((a.symm ⟨b x, hx⟩ : R) : Q) = b x := by
        rw [← hab]
        exact congrArg Subtype.val (a.apply_symm_apply ⟨b x, hx⟩)
      exact (b.injective he) ▸ (a.symm ⟨b x, hx⟩).property
    · intro hx
      rw [← hab ⟨x, hx⟩]
      exact (a ⟨x, hx⟩).property
  refine ⟨⟨b, hbS, hbR⟩, ?_⟩
  apply Subtype.ext
  ext x
  exact (hab x).symm

/-- The actual map from the pair stabilizer to the outer automorphism group. -/
def pairOuter (S R : Subgroup Q) : pairStabilizer S R →* MulAut.Outer Q :=
  (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp (pairStabilizer S R).subtype

/-- The inner kernel vanishes on R under the stated centralizer containment. -/
theorem pairOuter_kernel_le_restriction_kernel (S R : Subgroup Q)
    (hinner : normalizer S ⊓ normalizer R ≤ centralizer (R : Set Q)) :
    (pairOuter S R).ker ≤ (pairRestriction S R).ker := by
  intro a ha
  have hi : a.val ∈ MulAut.innerSubgroup Q := (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨g, hg⟩ := hi
  have hnorm : g ∈ normalizer S ⊓ normalizer R := by
    constructor
    · exact mem_normalizer_iff.mpr (fun x => by
        simpa only [← hg, MulAut.conj_apply] using (a.property.1 x).symm)
    · exact mem_normalizer_iff.mpr (fun x => by
        simpa only [← hg, MulAut.conj_apply] using (a.property.2 x).symm)
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change a.val x = (x : Q)
  rw [← hg]
  change g * (x : Q) * g⁻¹ = x
  rw [← hinner hnorm x x.property, mul_inv_cancel_right]

/-- Cyclicity descends through the outer quotient once its inner kernel acts trivially. -/
theorem pairAutomizer_isCyclic_of_outer (S R : Subgroup Q)
    (houter : IsCyclic (MulAut.Outer Q))
    (hinner : normalizer S ⊓ normalizer R ≤ centralizer (R : Set Q)) :
    IsCyclic (pairAutomizer S R) := by
  let _ := houter
  let f := pairOuter S R
  let r := pairRestriction S R
  have hk : f.ker ≤ r.ker := pairOuter_kernel_le_restriction_kernel S R hinner
  let _ : IsCyclic (pairStabilizer S R ⧸ f.ker) := isCyclic_of_injective
    (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  exact isCyclic_of_surjective (QuotientGroup.lift f.ker r hk)
    (QuotientGroup.lift_surjective_of_surjective f.ker r
      (pairRestriction_surjective S R) hk)

/-- A Borel factorization reduces the inner kernel to the disjoint normalizing factors. -/
theorem inner_centralizes_of_normalizer_factorization (S R : Subgroup Q)
    (hRS : R ≤ normalizer S) (hd : Disjoint S R)
    (hfactor : ∀ g ∈ normalizer S, ∃ s ∈ S,
      ∃ c ∈ centralizer (R : Set Q), s * c = g) :
    normalizer S ⊓ normalizer R ≤ centralizer (R : Set Q) := by
  have hSN : S ⊓ normalizer R ≤ centralizer (R : Set Q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hd.eq_bot]
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hRS)
  intro g hg
  obtain ⟨s, hs, c, hc, hsc⟩ := hfactor g hg.1
  have hsN : s ∈ normalizer R := by
    have hcN : c ∈ Subgroup.normalizer (R : Set Q) :=
      Subgroup.centralizer_le_normalizer (R : Set Q) hc
    have hh : g * c⁻¹ ∈ Subgroup.normalizer (R : Set Q) :=
      (Subgroup.normalizer (R : Set Q)).mul_mem hg.2
        ((Subgroup.normalizer (R : Set Q)).inv_mem hcN)
    rw [← hsc, mul_inv_cancel_right] at hh
    exact hh
  rw [← hsc]
  exact (centralizer (R : Set Q)).mul_mem (hSN ⟨hs, hsN⟩) hc

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
