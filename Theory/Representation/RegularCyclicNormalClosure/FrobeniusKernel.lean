module
public import Theory.Representation.RegularCyclicNormalClosure.Defs
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.SpecificGroups.Frobenius21.BinaryOvergroups

/-!
# A Frobenius factor detected by its complementary fixed summand

In a faithful binary action, the pointwise stabilizer of one of two
complementary summands acts faithfully on the other. If this stabilizer
normalizes a factor of order 21 and the other summand has dimension three,
self-normalization in GL₃(2) identifies the stabilizer with that factor.
For a permuted two-factor decomposition, pointwise fixation itself forces
preservation of both summands and normalization of the corresponding factor.

Source: Aschbacher–Smith, E.6.25, printed p.255, the action on V₁ of
C_{N_M(V)}(V₂). All actors and restricted representations remain literal.
-/

public section
namespace Representation.RegularCyclicNormalClosure
open Subgroup BinaryOffender
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A normal order-21 factor is the whole pointwise stabilizer of its complement. -/
theorem pointwise_kernel_le_card_twenty_one
    (hfaith : Function.Injective ρ) (F : Subgroup A)
    (S R : Submodule (ZMod 2) W) (hsplit : IsCompl S R)
    (hF : F ≤ subspaceKernel ρ R ⊤)
    (hS : subspaceKernel ρ R ⊤ ≤ subspaceStabilizer ρ S)
    (hN : subspaceKernel ρ R ⊤ ≤ normalizer (F : Set A))
    (hdim : Module.finrank (ZMod 2) S = 3) (hcard : Nat.card F = 21) :
    subspaceKernel ρ R ⊤ ≤ F := by
  let P := subspaceKernel ρ R ⊤
  let I := F.subgroupOf P
  let f : P →* LinearMap.GeneralLinearGroup (ZMod 2) S :=
    (stabilizerRepresentation ρ S).asGroupHom.comp (Subgroup.inclusion hS)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    apply Subtype.ext
    apply hfaith
    ext v
    obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ S ⊔ R by rw [hsplit.sup_eq_top]; trivial)
    have he := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) S =>
      ((g : Module.End (ZMod 2) S) ⟨s, hs⟩ : S)) ha
    have he' := congrArg Subtype.val he
    change ρ (a : A) s = s at he'
    simp only [Subgroup.coe_one, map_one, Module.End.one_apply, map_add,
      he', a.property.2 r hr]
  have hI : I.Normal := (normal_subgroupOf_iff_le_normalizer hF).mpr hN
  let := hI
  have hIcard : Nat.card (I.map f) = 21 := by
    rw [Subgroup.card_map_of_injective hf]
    exact (Nat.card_congr (subgroupOfEquivOfLe hF).toEquiv).trans hcard
  intro a ha
  have he : f ⟨a, ha⟩ ∈ normalizer (I.map f : Set _) := by
    apply Subgroup.le_normalizer_map f
    exact ⟨⟨a, ha⟩, by rw [I.normalizer_eq_top]; trivial, rfl⟩
  rw [Frobenius21.binary_normalizer_of_card S hdim (I.map f) hIcard] at he
  obtain ⟨b, hb, hba⟩ := he
  change (b : A) ∈ F at hb
  simpa only [hf hba] using hb

/-- In a permuted two-factor decomposition, the complementary pointwise kernel lies in the factor. -/
theorem Decomposition.pointwise_kernel_le_factor
    (D : Decomposition ρ C) (hfaith : Function.Injective ρ)
    (i j : Fin D.size) (hij : i ≠ j) (htwo : ∀ k, k = i ∨ k = j)
    (hsplit : IsCompl (D.summand i) (D.summand j))
    (hdim : Module.finrank (ZMod 2) (D.summand i) = 3)
    (hcard : Nat.card (D.factor i) = 21) :
    subspaceKernel ρ (D.summand j) ⊤ ≤ D.factor i := by
  have hne : D.summand i ≠ D.summand j := by
    intro he
    have hb : D.summand i = ⊥ := by
      have hd := hsplit.disjoint
      rw [← he] at hd
      exact disjoint_self.mp hd
    rw [hb, finrank_bot] at hdim
    omega
  have hpres (a : A) (ha : a ∈ subspaceKernel ρ (D.summand j) ⊤) :
      (D.factor i).map (MulAut.conj a).toMonoidHom = D.factor i ∧
      (D.summand i).map (ρ a) = D.summand i := by
    obtain ⟨σ, hσ⟩ := D.permuted a
    have hr : (D.summand j).map (ρ a) = D.summand j := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        rw [ha.2 v hv]
        exact hv
      · intro v hv
        exact ⟨v, hv, ha.2 v hv⟩
    have hj : σ j = j := by
      rcases htwo (σ j) with he | he
      · have hbad := (hσ j).2
        rw [hr, he] at hbad
        exact False.elim (hne hbad.symm)
      · exact he
    have hi : σ i = i := by
      rcases htwo (σ i) with he | he
      · exact he
      · exact False.elim (hij (σ.injective (he.trans hj.symm)))
    simpa only [hi] using hσ i
  apply pointwise_kernel_le_card_twenty_one hfaith (D.factor i)
    (D.summand i) (D.summand j) hsplit
  · intro a ha
    exact ⟨mem_top _, D.cross_fixed i j hij a ha⟩
  · apply le_subspaceStabilizer
    intro a ha v hv
    rw [← (hpres a ha).2]
    exact Submodule.mem_map_of_mem hv
  · intro a ha
    exact mem_normalizer_iff_map_conj_eq.mpr (hpres a ha).1
  · exact hdim
  · exact hcard
end Representation.RegularCyclicNormalClosure
