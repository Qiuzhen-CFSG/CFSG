module
public import Theory.GroupAction.RankThreeBinaryFactorOrbit
public import Theory.GroupAction.RankThreeBinaryInvariantCubicFactor
/-!
# A single orbit of invariant cubic lines

Retain elementary binary A of order eight acting faithfully on elementary
cubic F, with compatible actions of T on A and F. Whole-A fixed freedom,
nonidentity fixed bounds of nine, and T-irreducibility imply that any two
A-invariant order-three subgroups of F are carried to one another by T.

Each invariant cubic line is a coatom fixed factor. The preceding orbit
theorem puts their actor coatoms in one T-orbit. Compatibility transports
fixed subgroups, so the element carrying one coatom to the other carries
their cubic lines as well. T need not be a two-group for this conclusion.

This packages the action-property transport used in Stellmacher (8.6)(c3),
following (21) on printed p.45. All three actions and both given subgroups
are retained literally; no conjugacy is assumed.
-/

open scoped Pointwise
public theorem rank_three_binary_invariant_cubic_subgroups_same_orbit
    {A F T : Type*} [Group A] [Finite A] [Group F] [Finite F] [Nontrivial F]
    [Group T] [Finite T] [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F]
    [MulDistribMulAction T A] [MulDistribMulAction T F] [MulDistribMulAction A F]
    [FaithfulSMul A F]
    (hA : Nat.card A = 8)
    (hcompat : ∀ (t : T) (a : A) (x : F), t • (a • x) = (t • a) • (t • x))
    (hfixed : ∀ a : A, a ≠ 1 → Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) F) ≤ 9)
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (hirr : ∀ H : Subgroup F, IsInvariant T F H → H = ⊥ ∨ H = ⊤)
    (H₁ H₂ : Subgroup F) (h₁ : IsInvariant A F H₁) (h₂ : IsInvariant A F H₂)
    (hc₁ : Nat.card H₁ = 3) (hc₂ : Nat.card H₂ = 3) :
    ∃ t : T, t • H₁ = H₂ := by
  classical
  have htransport_le (t : T) (K : Subgroup A) :
      t • FixedPoints.subgroup K F ≤ FixedPoints.subgroup (t • K : Subgroup A) F := by
    intro y hy a
    obtain ⟨x,hx,rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists y t _).mp hy
    obtain ⟨b,hb,heq⟩ := (Subgroup.mem_smul_pointwise_iff_exists (a:A) t K).mp a.property
    change (a:A) • (t • x) = t • x
    rw [←heq,←hcompat]
    exact congrArg (fun z : F => t • z) (hx ⟨b,hb⟩)
  have htransport (t : T) (K : Subgroup A) :
      t • FixedPoints.subgroup K F = FixedPoints.subgroup (t • K : Subgroup A) F := by
    apply le_antisymm (htransport_le t K)
    rw [Subgroup.subset_pointwise_smul_iff]
    exact (htransport_le t⁻¹ (t • K)).trans_eq
      (congrArg (fun M : Subgroup A => FixedPoints.subgroup M F) (inv_smul_smul t K))
  obtain ⟨K₁,hK₁,hHK₁⟩ := rank_three_binary_invariant_cubic_eq_fixed_factor hA
    (IsElementaryAbelian.isPGroup 3 F) hfixed hfull H₁ h₁ hc₁
  obtain ⟨K₂,hK₂,hHK₂⟩ := rank_three_binary_invariant_cubic_eq_fixed_factor hA
    (IsElementaryAbelian.isPGroup 3 F) hfixed hfull H₂ h₂ hc₂
  have hne (H : Subgroup F) (hc : Nat.card H = 3) : H ≠ ⊥ := by
    intro hh
    have hone := Subgroup.card_eq_one.mpr hh
    omega
  obtain ⟨K,_hK,_hKne,horbit⟩ :=
    rank_three_binary_fixed_factors_single_orbit hA hcompat hfull hirr
  have h₁orbit : K₁ ∈ MulAction.orbit T K := horbit ▸
    (show K₁ ∈ {L : Subgroup A | L.index = 2 ∧ FixedPoints.subgroup L F ≠ ⊥} from
      ⟨hK₁,hHK₁ ▸ hne H₁ hc₁⟩)
  have h₂orbit : K₂ ∈ MulAction.orbit T K := horbit ▸
    (show K₂ ∈ {L : Subgroup A | L.index = 2 ∧ FixedPoints.subgroup L F ≠ ⊥} from
      ⟨hK₂,hHK₂ ▸ hne H₂ hc₂⟩)
  obtain ⟨t₁,ht₁⟩ := h₁orbit
  obtain ⟨t₂,ht₂⟩ := h₂orbit
  change t₁ • K = K₁ at ht₁
  change t₂ • K = K₂ at ht₂
  refine ⟨t₂ * t₁⁻¹,?_⟩
  rw [hHK₁,hHK₂,htransport,←ht₁,mul_smul,inv_smul_smul,ht₂]
