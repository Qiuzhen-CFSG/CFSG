module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# A coprime actor excludes a nonzero fixed commutator layer

Suppose B and Y act on Z, their mutual displacement centralizes Z, and B
centralizes [Y,Z]. The three-subgroup lemma makes [Z,B] centralize Y. If B
has a fixed-point-free element on a marked section of Z whose denominator
also centralizes Y, the coprime fixed/moved decomposition then forces
[Y,Z]=1. The section may lie inside a larger marked module.

Source application: DGS, *Groups and Graphs* (1985), proof of (8.3), p.136.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U N : Subgroup G} {ρ : Representation (ZMod 2) H W}

private theorem finite_coprime_decomposition (Z B : Subgroup G) [Finite Z] [Finite B]
    (hn : B ≤ normalizer (Z : Set G)) (hs : Group.IsSolvable Z)
    (hc : Nat.Coprime (Nat.card B) (Nat.card Z)) :
    Z = ⁅Z,B⁆ ⊔ (Z ⊓ centralizer (B : Set G)) := by
  let _ : Normalizes B Z := ⟨hn⟩
  have hd := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := Z) (A := B) hs hc
  have hf : (FixedPoints.subgroup B Z).map Z.subtype = Z ⊓ centralizer (B : Set G) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      intro b hb
      have hh := congrArg Subtype.val (hx ⟨b,hb⟩)
      change b * (x : G) * b⁻¹ = x at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · rintro ⟨hz,hc⟩
      refine ⟨⟨z,hz⟩,?_ ,rfl⟩
      intro b
      apply Subtype.ext
      change (b : G) * z * (b : G)⁻¹ = z
      rw [hc b b.property,mul_inv_cancel_right]
  change FixedPoints.subgroup B Z ⊔ commutatorAction B Z = ⊤ at hd
  have hh := congrArg (Subgroup.map Z.subtype) hd
  rw [Subgroup.map_sup,hf,commutatorAction_subgroup_conj_map_eq_commutator Z B hn,
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hh
  exact hh.symm

/-- A fixed-free section actor and coprime splitting turn the
three-subgroup identity into centralization of the whole original seed. -/
theorem commutator_eq_bot_of_coprime_fixedFree_section
    (c : BinaryConjugationSection H U N ρ)
    (Z Y B : Subgroup G) [Finite Z] [Finite B]
    (hs : Group.IsSolvable Z) (hcop : Nat.Coprime (Nat.card B) (Nat.card Z))
    (hZU : Z ≤ U) (hBZ : B ≤ normalizer (Z : Set G))
    (hBN : Z ⊓ N ≤ centralizer (B : Set G))
    (hYN : Z ⊓ N ≤ centralizer (Y : Set G))
    (hYZ : ⁅Y,Z⁆ ≤ Z ⊓ N)
    (hBY : ⁅B,Y⁆ ≤ centralizer (Z : Set G))
    (t : H) (ht : (t : G) ∈ B)
    (hfree : ∀ v, ρ t v = v → v = 0) : ⁅Y,Z⁆ = ⊥ := by
  have h1 : ⁅⁅B,Y⁆,Z⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hBY
  have h2 : ⁅⁅Y,Z⁆,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hYZ.trans hBN)
  have hmove : ⁅Z,B⁆ ≤ centralizer (Y : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_commutator_eq_bot_of_rotate h1 h2)
  have hfix : Z ⊓ centralizer (B : Set G) ≤ Z ⊓ N := by
    intro z hz
    refine ⟨hz.1,?_⟩
    apply (c.coordinates_eq_one_iff ⟨z,hZU hz.1⟩).mp
    change (c.coordinates ⟨z,hZU hz.1⟩).toAdd = 0
    apply hfree
    have he : (t : G) * z * (t : G)⁻¹ = z := by
      rw [hz.2 t ht,mul_inv_cancel_right]
    have hh := c.equivariant t ⟨z,hZU hz.1⟩
    have heq : (⟨(t : G) * z * (t : G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized t.property) z).mp (hZU hz.1)⟩ : U) = ⟨z,hZU hz.1⟩ :=
      Subtype.ext he
    rw [heq] at hh
    exact hh.symm
  have hZY : Z ≤ centralizer (Y : Set G) := by
    rw [finite_coprime_decomposition Z B hBZ hs hcop]
    exact sup_le hmove (hfix.trans hYN)
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hZY

end Representation.BinaryConjugationSection
