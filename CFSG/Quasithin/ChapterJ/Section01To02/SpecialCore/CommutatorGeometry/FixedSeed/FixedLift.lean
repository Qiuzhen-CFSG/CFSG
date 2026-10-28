module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.Propagation
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# The fixed lift and central absorption in J.2.3

The invariant nonzero subspace U/V contains a nonzero T-fixed vector.
For any such lift, centrality of V makes its commutator row T-invariant.
The two-group fixed-point theorem then puts Z=C_V(T), of order two,
in that nonzero row. The natural SL₂(4) calculation modulo Z is separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3, assertion (!), printed p.433 (PDF p.444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

/-- The chosen Sylow in L is literally T, under inclusion. -/
lemma sylow_map_eq : (d.sylowInL : Subgroup d.L).map d.L.subtype =
    (d.T : Subgroup G) := by
  rw [← d.intersection_eq, inf_eq_left.mpr d.T_le_L]

private def uSpace : Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
  AddSubgroup.toZModSubmodule 2
    ((d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map
      d.ru1.steinberg.coordinates).toAddSubgroup'

private lemma mem_uSpace (v : BinaryLinearThree.Steinberg) :
    v ∈ uSpace d ↔ ∃ u : d.toTypeRuSetup.S, (u : G) ∈ d.toTypeRuSetup.U ∧
      (d.ru1.steinberg.coordinates u).toAdd = v := Iff.rfl

/-- A nonzero fixed coset can be chosen in the literal U/V subspace. -/
theorem exists_fixed_lift_in_U :
    ∃ u : d.toTypeRuSetup.S, (u : G) ∈ d.toTypeRuSetup.U ∧ (u : G) ∉ d.V ∧
      ∀ g ∈ (d.sylowInL : Subgroup d.L),
        BinaryLinearThree.S (d.ru1.quotientMap g) (d.ru1.steinberg.coordinates u).toAdd =
          (d.ru1.steinberg.coordinates u).toAdd := by
  have hne : uSpace d ≠ ⊥ := by
    intro hbot
    have hUV : d.toTypeRuSetup.U ≤ d.V := by
      intro u hu
      have hm : (d.ru1.steinberg.coordinates ⟨u, d.U_le_S hu⟩).toAdd ∈ uSpace d :=
        (mem_uSpace d _).mpr ⟨⟨u, d.U_le_S hu⟩, hu, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      exact (d.ru1.steinberg.coordinates_eq_one_iff _).mp hm
    have hc := card_le_of_le hUV
    rw [d.ru2.card_U d.card_Z, d.ru1.card_V] at hc
    omega
  let A : Subrepresentation ((BinaryLinearThree.S.comp d.ru1.quotientMap).comp
      (d.sylowInL : Subgroup d.L).subtype) := {
    toSubmodule := uSpace d
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := (mem_uSpace d v).mp hv
      have hgT : ((g : d.L) : G) ∈ (d.T : Subgroup G) := by
        rw [← sylow_map_eq d]
        exact mem_map.mpr ⟨g, g.property, rfl⟩
      have hgH := d.toTypeRuSetup.T_le_H hgT
      exact (mem_uSpace d _).mpr ⟨⟨g * u * ((g : d.L) : G)⁻¹,
        (mem_normalizer_iff.mp (d.ru1.steinberg.normalized g.val.property) u).mp u.property⟩,
        (mem_normalizer_iff.mp (d.ru2.natural.normalized hgH) u).mp hu,
        d.ru1.steinberg.equivariant g u⟩ }
  let : Nontrivial A := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨v, hv, hf⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    A.toRepresentation d.sylowInL.isPGroup'
  obtain ⟨u, hu, he⟩ := (mem_uSpace d v).mp v.property
  refine ⟨u, hu, ?_, ?_⟩
  · intro huV
    apply hv
    apply Subtype.ext
    change (v : BinaryLinearThree.Steinberg) = 0
    rw [← he, (d.ru1.steinberg.coordinates_eq_one_iff u).mpr huV]
    rfl
  · intro g hg
    rw [he]
    exact congrArg Subtype.val (hf ⟨g, hg⟩)

/-- Fixing uV preserves the commutator row, since multiplying u by V
has no effect on that row. -/
theorem fixed_lift_normalizes_commutator (u : d.toTypeRuSetup.S)
    (hf : ∀ g ∈ (d.sylowInL : Subgroup d.L),
      BinaryLinearThree.S (d.ru1.quotientMap g) (d.ru1.steinberg.coordinates u).toAdd =
        (d.ru1.steinberg.coordinates u).toAdd) :
    (d.T : Subgroup G) ≤ normalizer (⁅zpowers (u : G), d.toTypeRuSetup.S⁆ : Subgroup G) := by
  intro g hg
  rw [← sylow_map_eq d] at hg
  obtain ⟨g, hg, rfl⟩ := hg
  let u' : d.toTypeRuSetup.S := ⟨g * u * (g : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized g.property) u).mp u.property⟩
  have he : d.ru1.steinberg.coordinates u' = d.ru1.steinberg.coordinates u :=
    Multiplicative.toAdd.injective ((d.ru1.steinberg.equivariant g u).trans (hf g hg))
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, MonoidHom.map_zpowers]
  change ⁅zpowers ((g : G) * (u : G) * (g : G)⁻¹),
    (d.L.pCoreIn 2).map (MulAut.conj (g : G)).toMonoidHom⁆ = _
  have hS : (d.L.pCoreIn 2).map (MulAut.conj (g : G)).toMonoidHom = d.L.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (d.ru1.steinberg.normalized g.property)
  rw [hS]
  exact commutator_eq_of_coordinates_eq d.ru1 u' u he

/-- Every nonzero T-invariant subgroup of V contains the source center Z. -/
theorem center_le_of_invariant (W : Subgroup G) (hWV : W ≤ d.V) (hne : W ≠ ⊥)
    (hn : (d.T : Subgroup G) ≤ normalizer W) : d.toTypeRuSetup.Z ≤ W := by
  have hWT := hWV.trans (d.ru1.V_le_S.trans d.S_le_T)
  have hpW : IsPGroup 2 W := d.T.isPGroup'.to_le hWT
  have hCne := inf_centralizer_ne_bot_of_pGroups (d.T : Subgroup G) W
    d.T.isPGroup' hpW hn hne
  have hCZ : W ⊓ centralizer ((d.T : Subgroup G) : Set G) ≤ d.toTypeRuSetup.Z := by
    rw [d.center_eq]
    exact inf_le_inf hWV le_rfl
  have he : W ⊓ centralizer ((d.T : Subgroup G) : Set G) = d.toTypeRuSetup.Z := by
    apply eq_of_le_of_card_ge hCZ
    rw [d.card_Z]
    exact (one_lt_card_iff_ne_bot _).mpr hCne
  exact he ▸ inf_le_left

/-- The T-fixed noncentral lift has a nonzero row, hence its row contains Z. -/
theorem center_le_fixed_commutator (u : d.toTypeRuSetup.S) (hu : (u : G) ∉ d.V)
    (hf : ∀ g ∈ (d.sylowInL : Subgroup d.L),
      BinaryLinearThree.S (d.ru1.quotientMap g) (d.ru1.steinberg.coordinates u).toAdd =
        (d.ru1.steinberg.coordinates u).toAdd) :
    d.toTypeRuSetup.Z ≤ ⁅zpowers (u : G), d.toTypeRuSetup.S⁆ := by
  apply center_le_of_invariant d _ (d.ru1.commutator_le_V u) _
    (fixed_lift_normalizes_commutator d u hf)
  intro hbot
  have hc := commutator_eq_bot_iff_le_centralizer.mp hbot (mem_zpowers (u : G))
  exact hu (d.ru1.centralizer_S ▸ hc)

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
