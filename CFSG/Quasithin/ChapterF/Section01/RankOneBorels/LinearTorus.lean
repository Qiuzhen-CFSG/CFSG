module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting

/-!
# Cartan divisors in lifted binary rank-one Borels

Conjugate the prescribed quotient Sylow to the matrix upper-unipotent
Sylow. Its normalizer contains the actual torus of order 2^n - 1.
The surjective Sylow-normalizer projection lifts this divisor through the
two-core, and the subtype embedding gives the literal ambient Borel.
No splitting or generation-parameter identity is required.

Source: Aschbacher--Smith F.1.3(1), printed pp.259--260; application to
original 8.3.7, pp.724--725, in QuietTensorBinaryNumerical.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
open BenderSuzuki.Converse
variable {F : Type*} [Field F] [Finite F]

/-- The full Cartan order divides the order of every binary PSL₂ Sylow normalizer. -/
theorem linear_torus_dvd_sylowNormalizer {n : ℕ} (_hn : 0 < n)
    (hF : Nat.card F = 2^n) (S : Sylow 2 (PSL2 F)) :
    2^n - 1 ∣ Nat.card (sylowNormalizer S) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (PSL2 F) S (Linear.projectiveSylow F)
  let c := MulAut.conj g
  have hS : (S : Subgroup (PSL2 F)).map c.toMonoidHom =
      (Linear.projectiveSylow F : Subgroup (PSL2 F)) := congrArg Sylow.toSubgroup hg
  have hN : (sylowNormalizer S).map c.toMonoidHom = PBorel F := by
    change (normalizer ((S : Subgroup (PSL2 F)) : Set _)).map c.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hS]
    exact Linear.projectiveSylow_normalizer F
  have hc := Nat.card_congr ((sylowNormalizer S).equivMapOfInjective c.toMonoidHom c.injective).toEquiv
  rw [hN] at hc
  rw [hc]
  have hd := card_dvd_of_le (PTorus_le_PBorel (F := F))
  simpa only [PTorus_card,Nat.card_units,hF] using hd

/-- The actual binary Cartan order survives lifting through the two-core. -/
theorem linear_torus_dvd_lifted_normalizer
    {K : Type*} [Group K] [Finite K] (S : Sylow 2 K)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (c : (K ⧸ pCore 2 K) ≃* PSL2 F) :
    2^n - 1 ∣ Nat.card (sylowNormalizer S) := by
  let R := quotientSylow S
  let R' := R.mapSurjective (f := c.toMonoidHom) c.surjective
  have hN : (sylowNormalizer R).map c.toMonoidHom = sylowNormalizer R' := by
    change (normalizer ((R : Subgroup (K ⧸ pCore 2 K)) : Set _)).map c.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    rfl
  have hc := Nat.card_congr ((sylowNormalizer R).equivMapOfInjective c.toMonoidHom c.injective).toEquiv
  rw [hN] at hc
  have hd : 2^n - 1 ∣ Nat.card (sylowNormalizer R) :=
    hc.symm ▸ linear_torus_dvd_sylowNormalizer hn hF R'
  exact hd.trans (card_dvd_of_surjective (normalizerProjection S) (normalizerProjection_surjective S))

/-- The Cartan divisor in the literal ambient component Borel, with its prescribed Sylow. -/
theorem linear_torus_dvd_borel
    {G : Type*} [Group G] (K U : Subgroup G) [Finite K]
    (S : Sylow 2 K) (hS : (S : Subgroup K).map K.subtype = U ⊓ K)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (c : (K ⧸ pCore 2 K) ≃* PSL2 F) :
    2^n - 1 ∣ Nat.card (borel K U) := by
  have hN : (sylowNormalizer S).map K.subtype = borel K U := by
    have hc : (U ⊓ K).subgroupOf K = (S : Subgroup K) := by
      rw [←hS]
      exact comap_map_eq_self_of_injective K.subtype_injective _
    change (normalizer ((S : Subgroup K) : Set K)).map K.subtype = _
    rw [←hc,←subgroupOf_normalizer_eq inf_le_right,
      subgroupOf,map_comap_eq,range_subtype]
    rfl
  have hc := Nat.card_congr ((sylowNormalizer S).equivMapOfInjective K.subtype K.subtype_injective).toEquiv
  rw [hN] at hc
  exact hc ▸ linear_torus_dvd_lifted_normalizer S hn hF c

end CFSG.Quasithin.ChapterF.Source
