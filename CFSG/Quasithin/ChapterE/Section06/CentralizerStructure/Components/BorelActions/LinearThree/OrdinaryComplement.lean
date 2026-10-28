module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.Centers
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OrdinaryComplement
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The ordinary PSL₃ cyclic complement in E.6.11

Perfectness of SL₃ makes the actual PSL₃ model centerless, so the Borel
preimage in E.6.8 is the normalizer of the marked Sylow subgroup of L.
The displacement equals its Sylow center, and the fixed-factor decomposition
identifies its full L-centralizer with C_L(V). The intrinsic matrix complement
therefore maps to a cyclic complement to C_L(V) in L ∩ M.

All intersections and normalizers retain their relative ambient groups.
Neither maximality of U nor ambient normality of L is required. This module
supplies the ordinary complement; the parent combines it with the separately
proved Sylow-center clause to assemble the model witness.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and the ordinary PSL₃ case of E.6.11, printed pp.247–250 (PDF pp.258–261).
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem ordinary_center_eq_bot
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) : center L = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := iso
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hz : center PSL(3,F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  apply (center L).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have he : e x ∈ center PSL(3,F) := (centerCongr e ⟨x, hx⟩).property
  simpa only [hz, mem_bot] using he

/-- A cyclic subgroup of order 2ⁿ−1 complements the full centralizer C_L(V)
in the Borel L ∩ M of the actual ordinary PSL₃ model. -/
theorem exists_complement_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧
      Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M ∧
      (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥ := by
  have hz : IsPGroup 2 (center L) := by
    rw [ordinary_center_eq_bot iso]
    exact IsPGroup.of_bot
  have hB : (normalizer (S : Set L)).map L.subtype = L ⊓ M := by
    rw [← borel_eq_sylow_normalizer h b hQ S hS hz,
      map_subgroupOf_eq_of_le inf_le_left]
  let Z : Subgroup L := (center S).map (S : Subgroup L).subtype
  have hZ : Z.map L.subtype = ⁅V, L ⊓ M⁆ := by
    rw [map_subgroup_center_eq L.subtype L.subtype_injective, hS]
    exact center_eq_displacement_linear_three h hU hL b hn hVL hQ S hS iso
  have hC : (centralizer (Z : Set L)).map L.subtype =
      L ⊓ centralizer (V : Set G) := by
    rw [← displacement_centralizer b hn, ← hZ]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.property, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx z hz)
    · rintro x ⟨hxL, hxC⟩
      refine ⟨⟨x, hxL⟩, mem_centralizer_iff.mpr ?_, rfl⟩
      intro z hz
      apply Subtype.ext
      exact mem_centralizer_iff.mp hxC z (mem_map_of_mem L.subtype hz)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  obtain ⟨Y, hY, ⟨eY⟩, hsup, hinf⟩ :=
    Matrix.PSL3.LinearThree.exists_sylow_center_complement F (by omega) hF e S
  refine ⟨Y.map L.subtype, ?_, ?_, ?_, ?_⟩
  · exact hB ▸ map_mono hY
  · exact ⟨(Y.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eY⟩
  · rw [← hC, ← Subgroup.map_sup, hsup, hB]
  · rw [← hC, ← Subgroup.map_inf _ _ _ L.subtype_injective, hinf, Subgroup.map_bot]

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
