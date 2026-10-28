module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.CharacterData
public import Theory.Character.MinimalDegree
public import Theory.Character.PermutationActionCharacter
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalConfiguration
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.CharacterFixedDimension
public import Theory.Character.Multiplicity

/-!
# Janko's fixed-space construction of an index-22 subgroup

The three local element censuses and the degree-21 character give fixed-space
dimensions 2, 3, and 4. Since 2 + 3 > 4, the generated subgroup has a nonzero
fixed vector. Orthogonality to the principal character makes it proper.

Its order is at least 20160. Together with ambient order 443520 this bounds
its index by 22. The minimum nonprincipal degree of 21 rules out every
smaller nontrivial coset action, so the index is exactly 22. This replaces
the final Sylow arithmetic in the printed proof with character degree counting.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1,
Section 8, pp.16--17. These implications retain explicit character and
local-configuration inputs; their existence from `LocalData` is not proved here.
-/

noncomputable section
open Representation
open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
universe u
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] Fintype.ofFinite

/-- Minimum character degree and a subgroup-size lower bound pin down the index. -/
public theorem Degree21Character.index_eq_of_large_proper (C : Degree21Character G)
    (hG : Nat.card G = 443520) (H : Subgroup G) (hproper : H ≠ ⊤)
    (hlarge : 20160 ≤ Nat.card H) : H.index = 22 := by
  classical
  have hmul := H.card_mul_index
  rw [hG] at hmul
  have hupper : H.index ≤ 22 := by nlinarith
  have hlower : 1 < H.index := H.one_lt_index_of_ne_top hproper
  let d := H.index - 1
  have hdegree : (permutationAction G (G ⧸ H)).character 1 = (d + 1 : ℕ) := by
    rw [char_one]
    simp only [Module.finrank_pi]
    have hc : Fintype.card (G ⧸ H) = d + 1 := by
      rw [← Nat.card_eq_fintype_card, ← H.index_eq_card]
      dsimp [d]
      omega
    exact_mod_cast hc
  have hp := permutationAction_scalarProduct_one_of_pretransitive G (G ⧸ H)
  obtain ⟨theta, hirr, hdeg, htheta⟩ := Theory.Character.eq_one_add_irreducible_of_min_degree
    (permutationAction G (G ⧸ H)) d (by dsimp [d]; omega) hdegree hp
    (fun theta hi hn => le_trans (by exact_mod_cast (show d ≤ 21 by dsimp [d]; omega))
      (C.minimum theta hi hn))
  have hne : theta ≠ 1 := by
    intro he
    have heq : (permutationAction G (G ⧸ H)).character =
        (1 : ClassFunction G) + 1 := by
      funext g
      simpa [he] using htheta g
    have h1 : scalarProduct G (1 : ClassFunction G) 1 = 1 := by
      simp [scalarProduct, ← Nat.card_eq_fintype_card]
    rw [heq, scalarProduct_add_left, h1] at hp
    norm_num at hp
  have hmin := C.minimum theta hirr hne
  rw [hdeg] at hmin
  have : 21 ≤ d := by exact_mod_cast hmin
  dsimp [d] at this
  omega

private theorem sum_indicator (H : Type*) [Fintype H] (p : H → Prop) [DecidablePred p]
    (a : ℂ) : (∑ x : H, if p x then a else 0) =
      (Nat.card {x : H // p x} : ℂ) * a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Evaluate the degree-21 character sum from the complete local order census. -/
public theorem Degree21Character.sum_of_census (C : Degree21Character G)
    (H : Subgroup G) (a2 a3 a4 a5 : ℕ)
    (hc : ∀ k : ℕ, Nat.card {x : H // orderOf x = k} = localOrderCount a2 a3 a4 a5 k) :
    ∑ x : H, C.chi (x : G) = 21 + 5 * a2 + 3 * a3 + a4 + a5 := by
  classical
  have hv (x : H) : C.chi (x : G) =
      (if orderOf x = 1 then 21 else 0) + (if orderOf x = 2 then 5 else 0) +
      (if orderOf x = 3 then 3 else 0) + (if orderOf x = 4 then 1 else 0) +
      (if orderOf x = 5 then 1 else 0) + (if orderOf x = 6 then -1 else 0) +
      (if orderOf x = 8 then -1 else 0) + (if orderOf x = 11 then -1 else 0) := by
    rcases C.values (x : G) with ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ |
      ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩
    all_goals
      rw [Subgroup.orderOf_coe] at ho
      simp [ho, hv]
  simp_rw [hv, Finset.sum_add_distrib, sum_indicator, hc]
  simp only [localOrderCount]
  norm_num
  ring

/-- An actual representation affording the nonprincipal character has no global invariants. -/
public theorem Degree21Character.invariants_eq_bot (C : Degree21Character G)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ)) (hrho : C.chi = rho.character) :
    rho.invariants = ⊥ := by
  have hne : C.chi ≠ 1 := by
    intro he
    have hh := C.degree
    simp [he] at hh
  have hs := (scalarProduct_principal_eq_zero_iff C.chi).mp
    (C.irreducible.scalarProduct_principal_eq_zero hne)
  apply Submodule.finrank_eq_zero.mp
  apply finrank_invariants_eq_of_sum_character rho 0
  simpa only [← hrho, Nat.cast_zero, mul_zero] using hs

/-- The fixed spaces of dimensions two and three overlap over the common four-space. -/
public theorem LocalConfiguration.generated_proper (L : LocalConfiguration G)
    (C : Degree21Character G) : L.X ⊔ L.Y ≠ ⊤ := by
  obtain ⟨n, rho, _, hrho⟩ := C.irreducible
  have hX : Module.finrank ℂ (invariants (rho.comp L.X.subtype)) = 2 := by
    apply finrank_invariants_eq_of_sum_character
    have hh := C.sum_of_census L.X 75 320 180 384 L.X_count
    rw [L.X_card]
    norm_num only [hrho, character, MonoidHom.comp_apply, Subgroup.subtype_apply,
      Nat.cast_ofNat, Nat.cast_zero] at hh ⊢
    exact hh
  have hY : Module.finrank ℂ (invariants (rho.comp L.Y.subtype)) = 3 := by
    apply finrank_invariants_eq_of_sum_character
    have hh := C.sum_of_census L.Y 27 32 36 0 L.Y_count
    rw [L.Y_card]
    norm_num only [hrho, character, MonoidHom.comp_apply, Subgroup.subtype_apply,
      Nat.cast_ofNat, Nat.cast_zero] at hh ⊢
    exact hh
  have hB : Module.finrank ℂ (invariants (rho.comp L.B.subtype)) = 4 := by
    apply finrank_invariants_eq_of_sum_character
    have hh := C.sum_of_census L.B 15 32 0 0 L.B_count
    rw [L.B_card]
    norm_num only [hrho, character, MonoidHom.comp_apply, Subgroup.subtype_apply,
      Nat.cast_ofNat, Nat.cast_zero] at hh ⊢
    exact hh
  apply rho.sup_ne_top_of_invariants_dimension (C.invariants_eq_bot rho hrho)
    L.X L.Y L.B L.B_le_X L.B_le_Y
  rw [hX, hY, hB]
  decide

/-- The subgroup generated by the actual local configuration has index 22. -/
public theorem LocalConfiguration.generated_index (L : LocalConfiguration G)
    (C : Degree21Character G) (hG : Nat.card G = 443520) :
    (L.X ⊔ L.Y).index = 22 :=
  C.index_eq_of_large_proper hG (L.X ⊔ L.Y) (L.generated_proper C) L.generated_card_lower

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
