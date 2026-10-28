module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.SuzukiGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Covers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryCovers.Source

/-!
# Section 16 geometry from the original odd central cover

The quotient's genuine three-family model equivalences, perfectness and odd
center identify the covering group as PSL₂, Suzuki, PSU₃ or SU₃. Applying the
intrinsic Sylow and two-point calculations to those equivalences gives the
common omega, torus and marked-generation conclusions. In the unitary case
the root-generated subgroup is an actual PSL₂ subgroup of the covering group
and is fixed by every square-one automorphism fixing the marked pair.

Source: GLS IV, Chapter 4, Lemmas 2.8(a), 3.2(b–e,h), 3.4(f); the concrete
inputs to Chapter 2, Lemmas 16.2–16.4 and Proposition 16.5. The ambient ZD
recognition and centralizer arguments remain with their source assembly.
-/

public section
namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup _root_.BenderSuzuki.MatrixGroups PFchapter1section1 PFAppendixIII

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

/-- The four actual covering models, preserving the source exponent and the
center-three, odd-exponent distinction in the special unitary branch. -/
theorem oddCentralCover_model_cases (hn : 2 ≤ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ center G)) :
    (center G = ⊥ ∧ Nonempty (G ≃* PSL2BinaryMatrixGroup n)) ∨
    (center G = ⊥ ∧ ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
      Nonempty (G ≃* SuzukiMatrixGroup m)) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      ((center G = ⊥ ∧ Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) ∨
       (Nat.card (center G) = 3 ∧ Odd n ∧ Nonempty (G ≃* J.specialSubgroup)))) := by
  rcases hmodel with hlinear | hsuzuki | hunitary
  · obtain ⟨e⟩ := hlinear
    exact Or.inl (linear_oddCentralCover hn hperfect hodd e)
  · obtain ⟨m, hnm, ⟨e⟩⟩ := hsuzuki
    have hm : 1 ≤ m := by omega
    obtain ⟨hc, he⟩ := suzuki_oddCentralCover m hm hperfect hodd e
    exact Or.inr (Or.inl ⟨hc, m, hm, hnm, he⟩)
  · obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩ := hunitary
    exact Or.inr (Or.inr ⟨E, hfield, hfinite, J, hJ, hcard, hfixed,
      unitary_centralCover_cases_of_odd_center J hn hcard hfixed hperfect hodd e⟩)

/-- The literal ambient omega subgroup, center and normalizer involution core
for every Sylow subgroup of the original odd central cover. -/
theorem oddCentralCover_omega_geometry (hn : 2 ≤ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ center G)) (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) ∧
      Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ n ∧
      omegaOneAmbient (P : Subgroup G) =
        (involutionCore (normalizer (P : Set G))).map (normalizer (P : Set G)).subtype := by
  rcases oddCentralCover_model_cases hn hperfect hodd hmodel with
    ⟨_, ⟨e⟩⟩ | ⟨_, m, hm, rfl, ⟨e⟩⟩ | ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, he⟩
  · obtain ⟨_, hc, hel, hq⟩ := LinearGeometry.omega_geometry (by omega) e P
    exact ⟨hc, hel, hq, (normalizer_involutionCore_eq_omega P).symm⟩
  · obtain ⟨hc, hel, hq, _, hi⟩ := suzuki_omega_geometry hm e P
    exact ⟨hc, hel, hq, hi.symm⟩
  · rcases he with ⟨_, ⟨e⟩⟩ | ⟨_, _, ⟨e⟩⟩
    · exact unitary_projective_omega_geometry J hn hJ hcard hfixed e P
    · exact unitary_special_omega_geometry J hn hJ hcard hfixed e P

/-- Common two-point geometry on the original covering group: the commutator
torus has order q−1, the marked generators give precisely L₀, and the common
centralizer of the marked involutions has odd order. -/
theorem oddCentralCover_pair_geometry (hn : 2 ≤ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ center G))
    (P : Sylow 2 G) (z t : G) (hzP : z ∈ P) (hz : IsInvolution z)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    let D := twoPoint (normalizer (P : Set G)) t
    IsCyclic D ∧ IsCyclic (⁅D, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅D, zpowers t⁆ : Subgroup G) = 2 ^ n - 1 ∧
      (∀ x ∈ ⁅D, zpowers t⁆, rightConjugateElem x t = x⁻¹) ∧
      (zpowers z ⊔ zpowers t ⊔ ⁅D, zpowers t⁆ = rootGenerated (P : Subgroup G) t) ∧
      Odd (Nat.card (centralizer ({z,t} : Set G))) ∧
      ⁅D, zpowers t⁆ ≤ rootGenerated (P : Subgroup G) t := by
  have hcentral : centralizer ({z,t} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
    ext x
    simp [mem_centralizer_iff]
  have finish {D : Subgroup G} (hD : IsCyclic D)
      (hT : IsCyclic (⁅D, zpowers t⁆ : Subgroup G))
      (hcard : Nat.card (⁅D, zpowers t⁆ : Subgroup G) = 2 ^ n - 1)
      (hinv : ∀ x ∈ ⁅D, zpowers t⁆, rightConjugateElem x t = x⁻¹)
      (hgen : zpowers z ⊔ zpowers t ⊔ ⁅D, zpowers t⁆ = rootGenerated (P : Subgroup G) t)
      (hc : Odd (Nat.card (centralizer ({z,t} : Set G)))) :=
    And.intro hD (And.intro hT (And.intro hcard (And.intro hinv
      (And.intro hgen (And.intro hc (hgen ▸ (le_sup_right :
        ⁅D, zpowers t⁆ ≤ zpowers z ⊔ zpowers t ⊔ ⁅D, zpowers t⁆)))))))
  rcases oddCentralCover_model_cases hn hperfect hodd hmodel with
    ⟨_, ⟨e⟩⟩ | ⟨_, m, hm, hnm, ⟨e⟩⟩ | ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, he⟩
  · obtain ⟨hD, hq⟩ := LinearGeometry.twoPoint_cyclic_card (by omega) e P ht htB
    have hc := LinearGeometry.twoPoint_commutator (by omega) e P ht htB
    apply finish hD (hc.symm ▸ hD) (hc.symm ▸ hq)
    · intro x hx
      exact LinearGeometry.twoPoint_inverted e P ht htB (hc ▸ hx)
    · exact LinearGeometry.marked_generation (by omega) e P hz hzP ht htB
    · simpa only [hcentral] using
        LinearGeometry.common_centralizer_odd e P hz hzP htB
  · obtain ⟨hD, hq, hi, hc⟩ := suzuki_twoPoint_geometry hm e P t ht htB
    rw [← hnm] at hq
    apply finish hD (hc.symm ▸ hD) (hc.symm ▸ hq)
    · intro x hx
      exact hi x (hc ▸ hx)
    · exact suzuki_marked_generation hm e P t ht htB hzP hz
    · simpa only [hcentral] using
        suzuki_common_centralizer_odd hm e P hzP hz htB
  · rcases he with ⟨_, ⟨e⟩⟩ | ⟨_, _, ⟨e⟩⟩
    · obtain ⟨hD, _, hT, hq, hi, _⟩ :=
        unitary_projective_tori_of_equiv J hn hJ hcard hfixed e P t ht htB
      obtain ⟨hgen, hc⟩ :=
        unitary_projective_marked_pair_of_equiv J hn hJ hcard hfixed e P z t hzP hz ht htB
      exact finish hD hT hq hi hgen hc
    · obtain ⟨hD, _, hT, hq, hi, _⟩ :=
        unitary_special_tori_of_equiv J hn hJ hcard hfixed e P t ht htB
      obtain ⟨hgen, hc⟩ :=
        unitary_special_marked_pair_of_equiv J hn hJ hcard hfixed e P z t hzP hz ht htB
      exact finish hD hT hq hi hgen hc

/-- The model alternatives for L₀ in 16.2, with the unitary fixed-pair
conclusion proved for every automorphism of the original covering group. -/
theorem oddCentralCover_root_cases (hn : 2 ≤ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (hmodel : IsSimpleBenderGroupAtExponent n (G ⧸ center G))
    (P : Sylow 2 G) (z t : G) (hzP : z ∈ P) (hz : IsInvolution z)
    (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G)) :
    (rootGenerated (P : Subgroup G) t = ⊤ ∧ Nonempty (G ≃* PSL2BinaryMatrixGroup n)) ∨
    (rootGenerated (P : Subgroup G) t = ⊤ ∧ ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧
      Nonempty (G ≃* SuzukiMatrixGroup m)) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      Nonempty ((G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∧
      Nonempty (rootGenerated (P : Subgroup G) t ≃* PSL2BinaryMatrixGroup n) ∧
      ∀ a : MulAut G, a ^ 2 = 1 → a z = z → a t = t →
        rootGenerated (P : Subgroup G) t ≤ a.fixedSubgroup) := by
  rcases hmodel with hlinear | hsuzuki | hunitary
  · obtain ⟨e⟩ := hlinear
    obtain ⟨_, ⟨f⟩⟩ := linear_oddCentralCover hn hperfect hodd e
    exact Or.inl ⟨LinearGeometry.rootGenerated_eq_top f P htB, ⟨f⟩⟩
  · obtain ⟨m, hnm, ⟨e⟩⟩ := hsuzuki
    have hm : 1 ≤ m := by omega
    obtain ⟨_, ⟨f⟩⟩ := suzuki_oddCentralCover m hm hperfect hodd e
    exact Or.inr (Or.inl ⟨suzuki_rootGenerated_eq_top hm f P t htB, m, hm, hnm, ⟨f⟩⟩)
  · obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩ := hunitary
    refine Or.inr (Or.inr ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩, ?_⟩)
    rcases unitary_centralCover_alternative_of_odd_center J hn hcard hfixed hperfect hodd e
      with hf | hf
    · obtain ⟨f⟩ := hf
      refine ⟨⟨unitary_projective_rootGenerated_equiv_of_equiv
        J hn hJ hcard hfixed f P t ht htB⟩, ?_⟩
      intro a ha haz hat
      exact unitary_projective_rootGenerated_fixed J hn hJ hcard hfixed
        f P z hzP hz.1 hz.2 a ha haz t hat
    · obtain ⟨f⟩ := hf
      refine ⟨⟨unitary_special_rootGenerated_equiv_of_equiv
        J hn hJ hcard hfixed f P t ht htB⟩, ?_⟩
      intro a ha haz hat
      exact unitary_special_rootGenerated_fixed J hn hJ hcard hfixed
        f P z hzP hz.1 hz.2 a ha haz t hat

end BenderSuzuki.ZD.RankOneModelGeometry
