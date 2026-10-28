module

public import Theory.Representation.SL2.EightTripleTorus
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import Theory.Representation.NormalInvariants
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# The two root fixed lines in the order-seven fixed plane

Each actual root of order eight fixes a binary line in the irreducible
degree-eight module. A normalizing subgroup fixes that line pointwise because
the field is binary. Two distinct roots generate the whole rank-one group,
so their fixed lines are disjoint. For a common torus of order seven, these
two lines therefore span its entire two-dimensional fixed space.
-/

noncomputable section
open Module Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2.BinarySmall

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem binary_normalizer_fixes_line
    {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
    (R C : Subgroup G) (hn : C ≤ normalizer (R : Set G))
    (hd : finrank (ZMod 2) (fixedSpace ρ R) = 1) :
    fixedSpace ρ R ≤ fixedSpace ρ C := by
  classical
  let D := fixedSpace ρ R
  have hc : Nat.card D = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    rfl
  intro v hv c
  have hm : ρ c v ∈ D := by
    intro r
    have hr : (c : G)⁻¹ * r * c ∈ R := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hn (C.inv_mem c.property)) r).mp r.property
    have hf := hv ⟨_,hr⟩
    change ρ r (ρ c v) = ρ c v
    calc
      _ = ρ c (ρ ((c : G)⁻¹ * r * c) v) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      _ = _ := congrArg (ρ c) hf
  let x : D := ⟨v,hv⟩
  let y : D := ⟨ρ c v,hm⟩
  by_cases hx : x = 0
  · have hz : v = 0 := congrArg Subtype.val hx
    simp [hz]
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' (0 : D)).mp hc
  have hy : y ≠ 0 := by
    intro he
    apply hx
    apply Subtype.ext
    have hh : ρ c v = 0 := congrArg Subtype.val he
    apply (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom c)).injective
    change ρ c v = ρ c 0
    rw [hh,map_zero]
  exact congrArg Subtype.val ((hu y hy).trans (hu x hx).symm)

/-- The two literal root fixed lines span the entire fixed plane of their
common order-seven torus in the original irreducible binary action. -/
public theorem eight_irreducible_torus_root_lines
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : finrank (ZMod 2) V = 8)
    (R S C : Subgroup SL(2,GaloisField 2 3))
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hr : Nat.card R = 8) (hs : Nat.card S = 8) (hne : R ≠ S)
    (hc : Nat.card C = 7)
    (hnR : C ≤ normalizer (R : Set SL(2,GaloisField 2 3)))
    (hnS : C ≤ normalizer (S : Set SL(2,GaloisField 2 3))) :
    finrank (ZMod 2) (fixedSpace ρ R) = 1 ∧
      finrank (ZMod 2) (fixedSpace ρ S) = 1 ∧
      Disjoint (fixedSpace ρ R) (fixedSpace ρ S) ∧
      fixedSpace ρ R ⊔ fixedSpace ρ S = fixedSpace ρ C := by
  have hdim (P : Subgroup SL(2,GaloisField 2 3))
      (hp : IsPGroup 2 P) (hcard : Nat.card P = 8) :
      finrank (ZMod 2) (fixedSpace ρ P) = 1 := by
    have h := TripleFixedSpaces.binary_fixed_mul_card
      (GaloisField.card 2 3 (by decide)) ρ (eight_irreducible_isTriple ρ hd) P hp
    rw [hcard] at h
    omega
  have hdr := hdim R hR hr
  have hds := hdim S hS hs
  have hjoin : R ⊔ S = ⊤ := by
    obtain ⟨P,hP⟩ := hR.exists_le_sylow
    obtain ⟨Q,hQ⟩ := hS.exists_le_sylow
    have hcard (X : Sylow 2 SL(2,GaloisField 2 3)) : Nat.card X = 8 := by
      rw [← Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive
        (GaloisField 2 3) 2 X).toEquiv]
      exact GaloisField.card 2 3 (by decide)
    have hrP : R = (P : Subgroup SL(2,GaloisField 2 3)) :=
      eq_of_le_of_card_ge hP (by rw [hr,hcard P])
    have hsQ : S = (Q : Subgroup SL(2,GaloisField 2 3)) :=
      eq_of_le_of_card_ge hQ (by rw [hs,hcard Q])
    rw [hrP,hsQ]
    apply Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 P Q
    intro he
    exact hne (hrP.trans ((congrArg Sylow.toSubgroup he).trans hsQ.symm))
  have htop : fixedSpace ρ ⊤ = ⊥ := by
    by_contra hfix
    have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ hfix
    have hrt : fixedSpace ρ R = ⊤ := by
      apply top_unique
      intro v _ r
      have he : ρ r = 1 := hk (mem_top (r : SL(2,GaloisField 2 3)))
      change ρ r v = v
      rw [he,Module.End.one_apply]
    rw [hrt,finrank_top,hd] at hdr
    contradiction
  have hi : fixedSpace ρ R ⊓ fixedSpace ρ S = ⊥ := by
    have he : fixedSpace ρ (R ⊔ S) = fixedSpace ρ R ⊓ fixedSpace ρ S :=
      ρ.invariants_comp_sup R S
    rw [hjoin,htop] at he
    exact he.symm
  have hle : fixedSpace ρ R ⊔ fixedSpace ρ S ≤ fixedSpace ρ C :=
    sup_le (binary_normalizer_fixes_line ρ R C hnR hdr)
      (binary_normalizer_fixes_line ρ S C hnS hds)
  refine ⟨hdr,hds,disjoint_iff.mpr hi,Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  have hh := (fixedSpace ρ R).finrank_sup_add_finrank_inf_eq (fixedSpace ρ S)
  rw [hi,finrank_bot,hdr,hds] at hh
  have hc2 := TripleFixedSpaces.eight_irreducible_seven_fixed_finrank ρ hd C hc
  omega

end Representation.SL2.BinarySmall
