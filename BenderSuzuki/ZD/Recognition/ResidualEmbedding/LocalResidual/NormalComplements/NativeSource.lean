module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceCensus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeOuter
/-!
# Section 16 local normal complements from the marked Sylow geometry

The source pair rank, actual Sylow omega containment and Q conjugacy now
produce marked fusion u ~ uz, the two global involution classes, and the
four-group incidence assertion. The actual outer-action argument then
supplies cyclic Sylow two-subgroups and a normal two-complement for every
subgroup with trivial distinguished circle, including the internal pair
stabilizer in M. The preceding rank, omega and centralizer-size source
inputs remain explicit until Lemmas 16.3–16.5 and 16.6(a,b) are completed.

Source: GLS IV, Chapter 2, Corollary 16.6(c–e).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

public theorem source16_global_classes_of_sylow_omega
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u z : G} (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hz : z ∈ Z)
    (hD : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (T : Sylow 2 (centralizer ({u} : Set G))) (Q : Subgroup G)
    (hQB : Q ≤ centralizer ({u} : Set G))
    (hOmega : ∀ w : T, PFAppendixIII.IsInvolution ((w : centralizer ({u} : Set G)) : G) →
      ((w : centralizer ({u} : Set G)) : G) ∈ Q ⊔ zpowers u)
    (hQclass : ∀ q ∈ Q, q ≠ 1 →
      ∃ b ∈ centralizer ({u} : Set G), MulAut.conj b q = z) :
    IsConj u (u*z) ∧ (∀ v : G, PFAppendixIII.IsInvolution v → v ∈ Z ∨ IsConj u v) ∧
      ∀ E : Subgroup G, Nat.card E = 4 → (∀ x : E, x ^ 2 = 1) → ∃ z ∈ E, z ∈ Z := by
  have hcensus := source16_centralizer_census_of_sylow_omega h hu hz T Q hQB hOmega hQclass
  have hfusion := source16_marked_fusion h r hu
    (not_mem_Z_of_mem_residualPairStabilizer h htM huD) hcensus
  have hclasses : ∀ v : G, PFAppendixIII.IsInvolution v → v ∈ Z ∨ IsConj u v := by
    intro v hv
    obtain ⟨x, hxB, hvx⟩ := source16_involution_conjugate_into_centralizer h r ha htM huD hu hD hv
    have hxi : PFAppendixIII.IsInvolution x := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hvx
      have hh := IsInvolution.map_of_injective hv (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      change PFAppendixIII.IsInvolution (MulAut.conj g v) at hh
      simpa only [MulAut.conj_apply, hg] using hh
    rcases hcensus x hxB hxi with rfl | hxZ | hux
    · exact Or.inr hvx.symm
    · left
      obtain ⟨g, hg⟩ := isConj_iff.mp hvx
      have hh := h.invariant g⁻¹ x hxZ
      rw [← hg] at hh
      simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using hh
    · exact Or.inr ((hfusion.trans hux).trans hvx.symm)
  refine ⟨hfusion, hclasses, source16_four_meets_distinguished h hu hclasses T Q hQB hOmega ?_⟩
  intro q hq hqn
  obtain ⟨b, _, hb⟩ := hQclass q hq hqn
  have hh := h.invariant b⁻¹ z hz
  rw [← hb] at hh
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using hh

/-- The local conclusion of 16.6(e), with its global class and four-incidence
premises discharged by the marked Sylow geometry. -/
public theorem source16_local_normalComplement_cyclicSylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u z : G} (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hz : z ∈ Z)
    (hD : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hne : ∃ a ∈ Z, a ∈ centralizer ({u} : Set G) ∧ a ∈ M)
    (T : Sylow 2 (centralizer ({u} : Set G))) (Q : Subgroup G)
    (hQB : Q ≤ centralizer ({u} : Set G))
    (hOmega : ∀ w : T, PFAppendixIII.IsInvolution ((w : centralizer ({u} : Set G)) : G) →
      ((w : centralizer ({u} : Set G)) : G) ∈ Q ⊔ zpowers u)
    (hQclass : ∀ q ∈ Q, q ≠ 1 →
      ∃ b ∈ centralizer ({u} : Set G), MulAut.conj b q = z)
    (hJ : ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer
      (localCircle Z (centralizer ({u} : Set G)))), IsCyclic S) :
    ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S := by
  obtain ⟨_, hclasses, hfour⟩ := source16_global_classes_of_sylow_omega
    h r ha htM huD hu hz hD T Q hQB hOmega hQclass
  exact local_normalComplement_cyclicSylow_of_marked_outer
    h r hu hBM hne hfour hclasses hJ hOuter

/-- The actual internal two-point subgroup receives all three source conclusions;
normality in the normal-complement clause is inside that subgroup. -/
public theorem source16_residualPairIn_normalComplement_cyclicSylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M)
    {t u z : G} (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hz : z ∈ Z)
    (hD : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hne : ∃ a ∈ Z, a ∈ centralizer ({u} : Set G) ∧ a ∈ M)
    (T : Sylow 2 (centralizer ({u} : Set G))) (Q : Subgroup G)
    (hQB : Q ≤ centralizer ({u} : Set G))
    (hOmega : ∀ w : T, PFAppendixIII.IsInvolution ((w : centralizer ({u} : Set G)) : G) →
      ((w : centralizer ({u} : Set G)) : G) ∈ Q ⊔ zpowers u)
    (hQclass : ∀ q ∈ Q, q ≠ 1 →
      ∃ b ∈ centralizer ({u} : Set G), MulAut.conj b q = z)
    (hJ : ∀ S : Sylow 2 (centralizer
      (localCircle Z (centralizer ({u} : Set G)) : Set (centralizer ({u} : Set G)))),
      Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer
      (localCircle Z (centralizer ({u} : Set G)))), IsCyclic S) :
    HasNormalPComplement 2 (residualPairIn M t) ∧
      2 ∣ Nat.card (residualPairIn M t) ∧
      ∀ S : Sylow 2 (residualPairIn M t), IsCyclic S := by
  obtain ⟨_, hclasses, hfour⟩ := source16_global_classes_of_sylow_omega
    h r ha htM huD hu hz hD T Q hQB hOmega hQclass
  exact residualPairIn_normalComplement_cyclicSylow_of_marked_outer
    h r ha hn hu hBM hne hfour hclasses hJ hOuter htM

end BenderSuzuki.ZD
