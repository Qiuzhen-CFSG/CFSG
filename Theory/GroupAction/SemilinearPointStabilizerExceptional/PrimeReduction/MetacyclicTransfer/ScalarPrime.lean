module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Basic
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.PGroup.OmegaAction

/-!
# The central weakly closed scalar subgroup

For p dividing the scalar order, the scalar images of the pth roots of
unity form a subgroup Z of order p. The zero stabilizer B normalizes Z,
so Z lies in every Sylow p-subgroup R of B. Counting conjugation orbits
modulo p shows that R centralizes Z. The proof identifies Z with the
literal ambient image of Ω₁(R ∩ K).

A nonidentity scalar fixes only zero. Thus if a conjugate of Z lies in B,
the conjugating element fixes zero and belongs to B; as B normalizes Z,
this proves weak closure. This direct argument supplies the same Z used
in GLS, Volume 4, Chapter 1, Lemma 3.9 without needing the classification
of the other order-p subgroups of R.

Source: `refs/KGroup/GLS4/Chapter1.tex`, lines 437–441; the central
weak-closure fusion route is GLS2, Chapter D, Lemma 16.9.
-/

open scoped IsMulCommutative
namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Finite X] [Field F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)

omit [Finite X] in
/-- A conjugate of a nontrivial scalar subgroup lies in B only if the conjugator lies in B. -/
public theorem conjugator_mem_stabilizer_of_scalar_conjugate_le
    {Z : Subgroup X} (hZ : Z ≤ c.scalarSubgroup) (hne : Z ≠ ⊥)
    {g : X} (hg : Z.map (MulAut.conj g).toMonoidHom ≤ stabilizer X (0 : F)) :
    g ∈ stabilizer X (0 : F) := by
  obtain ⟨z, hz, hz1⟩ := (Z.bot_or_exists_ne_one).resolve_left hne
  obtain ⟨a, ha⟩ := hZ hz
  have ha1 : a ≠ 1 := by
    intro h
    exact hz1 (by simpa [h] using ha.symm)
  have hfix : (g * z * g⁻¹) • (0 : F) = 0 :=
    mem_stabilizer_iff.mp (hg ⟨z, hz, rfl⟩)
  have hzero : g⁻¹ • (0 : F) = 0 := by
    apply (c.scalar_fixed_iff a ha1 _).mp
    have hh := congrArg (fun x : F => g⁻¹ • x) hfix
    simpa only [ha, mul_smul, inv_smul_smul] using hh
  exact mem_stabilizer_iff.mpr (by
    have hh := congrArg (fun x : F => g • x) hzero
    simpa only [smul_inv_smul] using hh.symm)

/-- The actual scalar omega subgroup has order p, centralizes R, and is weakly closed in R. -/
public theorem exists_central_weakly_closed_scalar [Finite F]
    {p : ℕ} [Fact p.Prime] (hpK : p ∣ Nat.card F - 1)
    (R : Sylow p X) (hRB : (R : Subgroup X) ≤ stabilizer X (0 : F)) :
    ∃ Z : Subgroup X, Nat.card Z = p ∧ Z ≤ c.scalarSubgroup ∧
      Z ≤ (R : Subgroup X) ∧
      (omega ↥((R : Subgroup X) ⊓ c.scalarSubgroup) (p := p) 1).map
        ((R : Subgroup X) ⊓ c.scalarSubgroup).subtype = Z ∧
      (R : Subgroup X) ≤ Subgroup.centralizer (Z : Set X) ∧
      (∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup X) →
        g ∈ Subgroup.normalizer (Z : Set X)) := by
  let U : Subgroup Fˣ := (powMonoidHom p : Fˣ →* Fˣ).ker
  let Z : Subgroup X := U.map c.scalar
  have hZK : Z ≤ c.scalarSubgroup := Subgroup.map_le_range c.scalar U
  have hcard : Nat.card Z = p := by
    dsimp [Z, U]
    rw [Subgroup.card_map_of_injective c.scalar_injective,
      IsCyclic.card_powMonoidHom_ker, Nat.card_units]
    exact Nat.gcd_eq_right hpK
  have hnorm : stabilizer X (0 : F) ≤ Subgroup.normalizer (Z : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    rintro g hg z ⟨a, ha, rfl⟩
    obtain ⟨b, σ, hσ⟩ := c.semilinear g (mem_stabilizer_iff.mp hg)
    refine ⟨Units.map σ.toMonoidHom a, ?_, (c.conj_scalar g b σ hσ a).symm⟩
    change (Units.map σ.toMonoidHom a) ^ p = 1
    change a ^ p = 1 at ha
    rw [← map_pow, ha, map_one]
  have hZB := hZK.trans c.scalarSubgroup_le_stabilizer
  let ZB := Z.subgroupOf (stabilizer X (0 : F))
  let : ZB.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZB).mpr hnorm
  have hZBp : IsPGroup p ZB := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hcard, pow_one])
  have hZR : Z ≤ (R : Subgroup X) := by
    intro z hz
    exact hZBp.le_sylow_of_normal (R.subtype hRB)
      (show (⟨z, hZB hz⟩ : stabilizer X (0 : F)) ∈ ZB from hz)
  have hmem (x : X) : x ∈ Z ↔ x ∈ c.scalarSubgroup ∧ x ^ p = 1 := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, rfl⟩, ?_⟩
      rw [← map_pow, show a ^ p = 1 from ha, map_one]
    · rintro ⟨⟨a, rfl⟩, ha⟩
      refine ⟨a, ?_, rfl⟩
      change a ^ p = 1
      apply c.scalar_injective
      simpa only [map_pow, map_one] using ha
  let D := (R : Subgroup X) ⊓ c.scalarSubgroup
  let : IsCyclic c.scalarSubgroup := c.scalarSubgroup_isCyclic
  let : IsCyclic D := isCyclic_of_injective
    (Subgroup.inclusion (show D ≤ c.scalarSubgroup from inf_le_right))
    (Subgroup.inclusion_injective _)
  have hOmega : (omega D (p := p) 1).map D.subtype = Z := by
    rw [OmegaAction.omega_eq_pow_ker]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (hmem u).mpr
      refine ⟨u.property.2, ?_⟩
      have hu' : u ^ (p ^ 1) = 1 := hu
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one] using congrArg Subtype.val hu'
    · intro hx
      refine ⟨⟨x, hZR hx, (hmem x).mp hx |>.1⟩, ?_, rfl⟩
      change (⟨x, hZR hx, (hmem x).mp hx |>.1⟩ : D) ^ (p ^ 1) = 1
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one] using ((hmem x).mp hx).2
  have hcentral : (R : Subgroup X) ≤ Subgroup.centralizer (Z : Set X) := by
    have hm := Subgroup.card_modEq_card_inf_centralizer (R : Subgroup X) Z
      R.isPGroup' (hRB.trans hnorm)
    have hd : p ∣ Nat.card ↥(Z ⊓ Subgroup.centralizer (R : Set X)) := by
      apply Nat.modEq_zero_iff_dvd.mp
      calc
        Nat.card ↥(Z ⊓ Subgroup.centralizer (R : Set X)) ≡ Nat.card Z [MOD p] := hm.symm
        _ ≡ 0 [MOD p] := by rw [hcard]; exact Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    have heq : Z ⊓ Subgroup.centralizer (R : Set X) = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left
        (hcard.trans_le (Nat.le_of_dvd Nat.card_pos hd))
    intro r hr z hz
    exact (heq.symm ▸ hz).2 r hr |>.symm
  have hne : Z ≠ ⊥ := by
    intro hh
    have hc : Nat.card Z = 1 := by rw [hh]; exact Subgroup.card_bot
    exact (Fact.out : p.Prime).ne_one (hcard.symm.trans hc)
  exact ⟨Z, hcard, hZK, hZR, hOmega, hcentral, fun g hg =>
    hnorm (c.conjugator_mem_stabilizer_of_scalar_conjugate_le hZK hne (hg.trans hRB))⟩
end MulAction.SemilinearPointStabilizer.Coordinates
