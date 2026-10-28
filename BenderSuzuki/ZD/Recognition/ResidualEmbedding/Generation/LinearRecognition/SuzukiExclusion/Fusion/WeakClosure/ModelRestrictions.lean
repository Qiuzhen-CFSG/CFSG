module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Complements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Embedding
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Outer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.NormalComplements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.ExceptionalOrder

/-!
# Suzuki subgroup restrictions for the complement and weak-closure arguments

The actual embedding J → L ≃ Sz(q), solvability of J, and its elementary
Sylow subgroup imply that U is normal in J when |U| > 2. Solvability and
the common prime then construct a nontrivial odd complement Y. The
assembled witness is cyclic of order dividing q-1 and acts freely on U#.
It also supplies every geometric premise of the Hall adjustment: normality
of U in D, membership and the Hall property in R = C_M(M°) ∩ N_M(M°U),
solvability of R, and preservation of M°U by M ∩ N_G(L). The final theorem
applies that adjustment with the normal-Sylow premise discharged.

The re-exported normal-complement restrictions apply to every odd complement
when U is normal, including without the size condition |U| > 2. In the
independent exceptional branch m = 1 and |U| = 2, standard Suzuki subgroup
containment proves |J| = 14. The actual action gives |D : K × J| dividing
2m+1, hence |D| dividing 294, and the exceptional prime-power obstruction.

Source: GLS4, Chapter 2, Lemmas 14.7–14.9, using Chapter 4, Lemma 3.8;
refs/KGroup/GLS4/Chapter2.tex and Chapter4.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Construct the odd complement and discharge all Hall-adjustment geometry
under the remaining normal-Sylow premise of the Suzuki model argument. -/
public theorem Context.exists_hall_complement_of_U_normal
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    ∃ Y : Subgroup G, Y ≤ centralizer (residualGenerated M z t : Set G) ∧
      Y ≠ ⊥ ∧ Odd (Nat.card Y) ∧
      (centralizer (residualGenerated M z t : Set G) : Set G) =
        (g.U : Set G) * (Y : Set G) ∧
      (g.U.subgroupOf (residualPairStabilizer M t)).Normal ∧
      Y ≤ complementFusionGroup g ∧ Group.IsSolvable (complementFusionGroup g) ∧
      IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
        (Y.subgroupOf (complementFusionGroup g)) ∧
      M ⊓ normalizer (residualGenerated M z t : Set G) ≤
        normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
  obtain ⟨Y, hYJ, hYne, hodd, hprod⟩ := s.exists_nontrivial_odd_complement g
  exact ⟨Y, hYJ, hYne, hodd, hprod, d.U_normal_pair_of_normal g hU,
    hYJ.trans (d.centralizer_le_complementFusionGroup_of_normal g hU),
    d.complementFusionGroup_solvable_of_normal g s hU,
    d.complementFusionGroup_hall_of_normal g s hU Y hYJ hodd hprod,
    d.local_normalizer_preserves_closure_sup_U_of_normal g hU⟩

/-- The source |U| > 2 branch, with the intrinsic Suzuki restrictions and
all Hall-adjustment geometry for the same constructed complement. No
normality or complement-existence premise remains. -/
public theorem Context.exists_cyclic_hall_complement_of_two_lt_card
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hcard : 2 < Nat.card g.U) :
    (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal ∧
      (g.U.subgroupOf (residualPairStabilizer M t)).Normal ∧
      ∃ Y : Subgroup G, Y ≤ centralizer (residualGenerated M z t : Set G) ∧
        Y ≠ ⊥ ∧ Odd (Nat.card Y) ∧
        (centralizer (residualGenerated M z t : Set G) : Set G) =
          (g.U : Set G) * (Y : Set G) ∧
        IsCyclic Y ∧ Nat.card Y ∣ 2 ^ (2 * m + 1) - 1 ∧
        (∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1) ∧
        Y ≤ complementFusionGroup g ∧ Group.IsSolvable (complementFusionGroup g) ∧
        IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
          (Y.subgroupOf (complementFusionGroup g)) ∧
        M ⊓ normalizer (residualGenerated M z t : Set G) ≤
          normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
  have hn := d.U_normal_centralizer_of_two_lt_card g f hf hcard
  obtain ⟨Y, hYJ, hYne, hodd, hprod, hUD, hYR, hsol, hhall, hLF⟩ :=
    d.exists_hall_complement_of_U_normal g s hn
  obtain ⟨hcyclic, hdiv, hfree⟩ :=
    d.normal_complement_restrictions g f hf hn Y hYJ hYne hodd hprod
  exact ⟨hn, hUD, Y, hYJ, hYne, hodd, hprod, hcyclic, hdiv, hfree,
    hYR, hsol, hhall, hLF⟩

/-- Apply Hall adjustment to any source odd complement when |U| > 2.
Normality of U and all auxiliary Hall geometry follow from the embedded
Suzuki model and the earlier Sylow geometry. -/
public theorem complement_conjugate_eq_of_two_lt_U_card
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hcard : 2 < Nat.card g.U)
    (E Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hodd : Odd (Nat.card Y))
    (hJ : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G))
    (hYE : Y ≤ normalizer (E : Set G))
    (x : G) (hxM : x ∈ M)
    (hEF : E.conjBy x = closure (Z ∩ (M : Set G)) ⊔ g.U) :
    E = closure (Z ∩ (M : Set G)) ⊔ g.U :=
  complement_conjugate_eq_of_normal_complement d g s
    (d.U_normal_centralizer_of_two_lt_card g f hf hcard)
    E Y hYJ hYne hodd hJ hYE x hxM hEF

end BenderSuzuki.ZD.SuzukiExclusion
