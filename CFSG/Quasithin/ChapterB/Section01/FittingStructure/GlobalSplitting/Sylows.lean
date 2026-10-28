module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.Identification

/-!
# The symmetric factors and their exact Sylow offender families

Identification with XA supplies the actual S₃ models and identifies each
cubic X as the embedded odd core of G_X. An offender in the defining family
has order two, so is Sylow in G_X, which has order six. Conversely every
Sylow two-subgroup is conjugate inside G_X to one of these offenders.
G_X normalizes X, and the offender family is stable under this conjugation.
Thus the entire Sylow family, not just a selected Sylow subgroup, is obtained.

Source: Aschbacher–Smith, B.1.9(1–4), printed p.71.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem planeGroup_model (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    Nonempty (planeGroup ρ X ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨A, hA, hn, he⟩ := hX
  obtain ⟨d⟩ := hlocal A hA hn
  rw [planeGroup_eq_local ρ hρ hlocal ⟨hA, hn, he.symm⟩, he]
  exact ⟨d.model⟩

theorem planeGroup_card (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) : Nat.card (planeGroup ρ X) = 6 := by
  obtain ⟨e⟩ := planeGroup_model ρ hρ hlocal hX
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  decide

theorem planeGroup_oddCore_eq (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    X = (pPrimeCore 2 (planeGroup ρ X)).map (planeGroup ρ X).subtype := by
  obtain ⟨A, hA, hn, he⟩ := hX
  obtain ⟨d⟩ := hlocal A hA hn
  rw [planeGroup_eq_local ρ hρ hlocal ⟨hA, hn, he.symm⟩, he]
  exact d.oddCore_eq

theorem planeGroup_sylow_card (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) (S : Sylow 2 (planeGroup ρ X)) :
    Nat.card S = 2 := by
  rw [S.card_eq_multiplicity, planeGroup_card ρ hρ hlocal hX]
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization, Nat.prime_three.factorization]
  norm_num

/-- A defining offender is an actual Sylow subgroup under the literal inclusion. -/
theorem planeOffender_is_sylow (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X A : Subgroup G} (hA : A ∈ planeOffenders ρ X) :
    ∃ S : Sylow 2 (planeGroup ρ X), (S : Subgroup (planeGroup ρ X)).map
      (planeGroup ρ X).subtype = A := by
  have hle := offender_le_planeGroup ρ hA
  let R := A.subgroupOf (planeGroup ρ X)
  obtain ⟨d⟩ := hlocal A hA.1 hA.2.1
  have hR : Nat.card R = 2 := (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans d.actor_card
  have hp : IsPGroup 2 R := IsPGroup.of_card (n := 1) (by simpa using hR)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have he : R = (S : Subgroup (planeGroup ρ X)) := eq_of_le_of_card_ge hS (by
    rw [hR]
    exact (planeGroup_sylow_card ρ hρ hlocal ⟨A, hA.1, hA.2.1, hA.2.2.symm⟩ S).le)
  exact ⟨S, he ▸ map_subgroupOf_eq_of_le hle⟩

/-- All Sylow subgroups occur, by conjugacy inside the source group G_X. -/
theorem sylow_mem_planeOffenders (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) (S : Sylow 2 (planeGroup ρ X)) :
    (S : Subgroup (planeGroup ρ X)).map (planeGroup ρ X).subtype ∈ planeOffenders ρ X := by
  obtain ⟨A, hA, hn, he⟩ := hX
  have hAf : A ∈ planeOffenders ρ X := ⟨hA, hn, he.symm⟩
  obtain ⟨S₀, hS₀⟩ := planeOffender_is_sylow ρ hρ hlocal hAf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (planeGroup ρ X) S₀ S
  have hmap : (S : Subgroup (planeGroup ρ X)).map (planeGroup ρ X).subtype =
      A.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [← hg]
    change ((S₀ : Subgroup (planeGroup ρ X)).map (MulAut.conj g).toMonoidHom).map
      (planeGroup ρ X).subtype = _
    have hc : (planeGroup ρ X).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp (planeGroup ρ X).subtype := by
      ext a
      rfl
    rw [map_map, hc, ← map_map, hS₀]
  have hfix : X.map (MulAut.conj (g : G)).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (planeGroup_normalizes_cubic ρ X g.property)
  rw [hmap]
  have hf := planeOffenders_map_conj ρ hAf (g : G)
  rw [hfix] at hf
  exact hf

/-- Exact equality of the source Pᵢ* with the embedded Sylow-two family. -/
theorem planeOffenders_iff_sylow (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) (A : Subgroup G) :
    A ∈ planeOffenders ρ X ↔ ∃ S : Sylow 2 (planeGroup ρ X),
      (S : Subgroup (planeGroup ρ X)).map (planeGroup ρ X).subtype = A := by
  constructor
  · exact planeOffender_is_sylow ρ hρ hlocal
  · rintro ⟨S, rfl⟩
    exact sylow_mem_planeOffenders ρ hρ hlocal hX S

/-- B.1.9(4), with the actual source factors indexed by their distinct cubics. -/
theorem noncentral_minimal_iff_planeGroup_sylow
    (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) (A : Subgroup G) :
    (IsMinimalBestOffender ρ A ∧ ⁅fittingSubgroup G, A⁆ ≠ ⊥) ↔
      ∃ i, ∃ S : Sylow 2 (planeGroup ρ (cubicFactor ρ i)),
        (S : Subgroup (planeGroup ρ (cubicFactor ρ i))).map
          (planeGroup ρ (cubicFactor ρ i)).subtype = A := by
  constructor
  · rintro ⟨hA, hn⟩
    have hm : ⁅fittingSubgroup G, A⁆ ∈ minimalMovedFactors ρ := ⟨A, hA, hn, rfl⟩
    obtain ⟨i, hi⟩ := (range_cubicFactor ρ).symm ▸ hm
    exact ⟨i, planeOffender_is_sylow ρ hρ hlocal ⟨hA, hn, hi.symm⟩⟩
  · rintro ⟨i, S, rfl⟩
    have h := sylow_mem_planeOffenders ρ hρ hlocal (cubicFactor_mem ρ i) S
    exact ⟨h.1, h.2.1⟩

end CFSG.Quasithin.ChapterB.FittingStructure
