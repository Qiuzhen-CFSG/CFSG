module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.Basic
public import Theory.SpecificGroups.PSL2.PrimeSylowMaximal
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.FermatMersenne

/-!
# Excluding the large odd linear-two components

For a Fermat or Mersenne prime p > 7, an adjacent integer is a power of
two at least sixteen. Dickson's proved subgroup classification makes each
Sylow two-subgroup of PSL₂(p) maximal. Since `M ∩ L` is proper and
contains `S ∩ L`, it is that Sylow subgroup. Thus `Y₊` is a two-group,
contrary to `|Y₊ : O₂(Y₊)| = 3`.

The prime-field and arbitrary-field statements retain primality and actual
multiplicative equivalences. This is the large L₂(p) branch of
Aschbacher--Smith 15.3.43, printed p.1140, with parameters from 1.1.5(3)(e),
printed p.502. The intrinsic maximality proof is in
`Theory.SpecificGroups.PSL2.PrimeSylowMaximal`.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

theorem not_of_maximal_component_sylows (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (hmax : ∀ P : Sylow 2 L, IsCoatom (P : Subgroup L)) : False := by
  obtain ⟨P, hP⟩ := component_sylow c
  have hPM : (P : Subgroup L) ≤ M.subgroupOf L := by
    intro x hx
    exact c.sylow_le_M ((hP ▸ mem_map_of_mem L.subtype hx).1)
  have hM : M.subgroupOf L ≠ ⊤ := fun h => c.component_outside (subgroupOf_eq_top.mp h)
  have hMP : M.subgroupOf L ≤ P := (isCoatom_iff_ge_of_le.mp (hmax P)).2 _ hM hPM
  have hYM : Yplus ≤ M := by
    rw [c.residual]
    exact (map_subtype_le _).trans inf_le_left
  have hYP : Yplus ≤ (P : Subgroup L).map L.subtype := by
    intro x hx
    exact mem_map.mpr ⟨⟨x, c.y_le_component hx⟩, hMP (hYM hx), rfl⟩
  have hy : IsPGroup 2 Yplus := (P.isPGroup'.map L.subtype).to_le hYP
  obtain ⟨n, hn⟩ := hy.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn, ← c.index]
    exact (pCore 2 Yplus).index_dvd_card
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

theorem adjacent_power_of_large_fermatMersenne {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 < p) :
    ∃ k : ℕ, 4 ≤ k ∧ (p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) := by
  have he : ∃ k : ℕ, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
    rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨2 ^ a, Or.inl (by omega)⟩
    · exact ⟨a, Or.inr ha⟩
  obtain ⟨k, hk⟩ := he
  refine ⟨k, ?_, hk⟩
  by_contra! h
  have hp9 : p ≠ 9 := by intro h; have hh := hp.1; rw [h] at hh; norm_num at hh
  interval_cases k <;> norm_num at hk <;> omega

theorem not_linear_two (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {p : ℕ} [Fact p.Prime] (hp : IsFermatOrMersennePrime p) (hp7 : 7 < p)
    (e : L ≃* PSL(2, ZMod p)) : False := by
  obtain ⟨k, hk, hpk⟩ := adjacent_power_of_large_fermatMersenne hp hp7
  apply not_of_maximal_component_sylows c
  intro P
  have h := Matrix.ProjectiveSpecialLinearGroup.sylow_two_isCoatom_of_adjacent_power hk hpk
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp h

theorem not_linear_two_field (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hp7 : 7 < p) (hF : Nat.card F = p)
    (e : L ≃* PSL(2, F)) : False := by
  let : Fact p.Prime := ⟨hp.1⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact not_linear_two c hp hp7 (e.trans (Atlas.fieldEquivPSL 2 f))

end CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
