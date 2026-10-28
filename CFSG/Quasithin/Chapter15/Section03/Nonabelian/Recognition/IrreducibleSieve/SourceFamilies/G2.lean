module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Quadratic
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.FrobeniusParameters
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.OrbitBounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.SpecificGroups.G2Even.TwoRank.SourceBound
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import Theory.Representation.G2DerivedPermutationFiltration
public import Theory.Representation.G2NaturalTransitivity
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# The source G₂ exclusions in the irreducible sieve

For nonbinary fields, the actual automorphism two-rank and source actor rank
bound the degree. The exhaustive tensor classification then forces the natural
octonion module; its nonzero-vector transitivity contradicts the invariant
nonsingular quadratic form in `SourceData`.

At the binary endpoint, the checked flag-module filtration and source degree
bound force degree six. Factor maps recognize the derived natural action, giving
the same contradiction. Both results retain the literal source action.

Source: Aschbacher--Smith, G.9.3(10), printed pp.354,356--357, and the
irreducible branch of 15.3.58, printed p.1149.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open Subgroup Representation ChapterG.Section09 Theory.GroupTheory
open ChapterG.Section09.DefiningCharacteristic
attribute [local instance] ZMod.algebra

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The nonbinary G₂ component has no source-compatible irreducible action. -/
theorem SourceData.not_g2_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassificationModels.IsG2At K (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hr := h.setup.rank_le_automorphisms (L := K) (by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK.normal]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hb := hr.trans (Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le F hn hF)
  have hsmall : Module.finrank (ZMod 2) W ≤ 6 * n + 2 := by
    have hd := h.dimension
    omega
  let σ := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  have hfaith : Function.Injective σ :=
    h.faithful.comp (K.subtype_injective.comp e.symm.injective)
  obtain ⟨_, t, l, ht, _, hperiod, hdim, hne, hbasic, hnatural⟩ :=
    G2Recognition.Nonbinary.exists_basic_parameters_and_natural σ hn hF hfaith
  have hprod := (G2Recognition.basic_product_alternatives l hbasic).resolve_left hne
  obtain ⟨_, ht1, hp6, _⟩ := G2Recognition.small_orbit_parameters
    (by omega : 0 < n) ht hprod hperiod hdim hsmall
  obtain ⟨a, f, hf⟩ := hnatural ht1 hp6
  have htrans : ∀ x y : Atlas.G2.Natural.Space F, x ≠ 0 → y ≠ 0 →
      ∃ g, G2Recognition.naturalBinary F g x = y := by
    intro x y hx hy
    obtain ⟨g, hg⟩ := Atlas.G2.Natural.derivedAction_transitive F x y hx hy
    exact ⟨g.val, hg⟩
  apply h.not_nonzero_transitive_model K (G2Recognition.naturalBinary F)
    htrans ⟨e.trans a, f, ?_⟩
  intro g w
  simpa [σ] using hf (e g) w

attribute [local instance] G2Recognition.BinarySix.scalars

/-- The binary derived G₂ component has no source-compatible irreducible action. -/
theorem SourceData.not_g2_derived_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K)
    (hmodel : Nonempty (K ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := hmodel
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hr := h.setup.rank_le_automorphisms (L := K) (by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK.normal]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hb := hr.trans Atlas.G2.binary_derived_automorphism_two_rank_le_three
  have hsmall : Module.finrank (ZMod 2) W ≤ 8 := by
    have hd := h.dimension
    omega
  let σ := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  have hdegrees := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    G2DerivedPermutationFiltration.flagPerm G2DerivedPermutationFiltration.baseFlag
    G2DerivedPermutationFiltration.flagStabilizer
    G2DerivedPermutationFiltration.flagStabilizer_isPGroup
    G2DerivedPermutationFiltration.mem_flagStabilizer_iff
    G2DerivedPermutationFiltration.flagTransitive
    G2DerivedPermutationFiltration.flag_factorDegreeFiltration σ
  change Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 6 ∨
    8 < Module.finrank (ZMod 2) W at hdegrees
  have hsix : Module.finrank (ZMod 2) W = 6 := by
    have := h.six_le_degree
    omega
  obtain ⟨a, f, hf⟩ := G2Recognition.BinarySix.quasiequivalent_of_finrank_eq_six σ hsix
  apply h.not_nonzero_transitive_model K (G2Recognition.derivedNaturalBinary (ZMod 2))
    (Atlas.G2.Natural.derivedAction_transitive (ZMod 2)) ⟨e.trans a, f, ?_⟩
  intro g w
  simpa [σ] using hf (e g) w

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
