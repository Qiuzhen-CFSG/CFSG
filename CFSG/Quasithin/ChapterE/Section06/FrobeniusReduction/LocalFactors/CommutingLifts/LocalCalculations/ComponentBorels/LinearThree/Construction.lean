module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.LinearThree.Placement
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.LinearThree.Replacement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.Centers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary


/-!
# Constructing the compatible cyclic section in the ordinary PSL₃ case

Sylow conjugacy aligns the given component isomorphism with its specified
Sylow subgroup. The Borel and highest-root group then map to L ∩ M and
[V,L ∩ M]. The direct decomposition in the Borel alternative identifies
the root-group centralizer with C_L(V). Transporting the compatible root
torus therefore gives another complement to that centralizer. Its induced
action equals the original X-action, and faithful replacement transports
every cyclic-section clause.

Source: Aschbacher–Smith, E.6.11(2),(3b) and the factor-count paragraph
of E.6.25, printed pp.249–250,255. The earlier Sylow-center calculation
is reused; no new E.6.11 hypothesis or conclusion is assumed.
-/

public section

open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions.RootTorusControl
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components Components.BorelActions
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem linear_three_center_eq_bot {L : Subgroup G} {n : ℕ}
    (iso : ClassicalGroup.IsPSL L 3 (2^n)) : center L = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := iso
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hz : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  apply (center L).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have he : e x ∈ center PSL(3,F) := (centerCongr e ⟨x,hx⟩).property
  simpa only [hz,mem_bot] using he

/-- Construct the compatible torus while retaining all earlier cyclic-section clauses. -/
theorem exists_linear_three_torus_placement
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hX : RegularCyclicSection M V U X)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (t : TorusAction M V L X (subgroupCorank V U))
    (hn : 1 < subgroupCorank V U)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ subgroupCorank V U)) :
    ∃ Y : Subgroup G, Y ≤ L ∧ RegularCyclicSection M V U Y ∧
      inducedAutomizer V Y = inducedAutomizer V X ∧
      LinearThreeTorusPlacement M V L Y (subgroupCorank V U) := by
  have hz : IsPGroup 2 (center L) := by
    rw [linear_three_center_eq_bot iso]
    exact IsPGroup.of_bot
  have hB : (normalizer (S : Set L)).map L.subtype = L ⊓ M := by
    rw [← borel_eq_sylow_normalizer h b hQ S hS hz,
      map_subgroupOf_eq_of_le inf_le_left]
  have hcent := center_eq_displacement_linear_three h hU hL b hn hVL hQ S hS iso
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card,hF]
    simp [Nat.pow_mod,show subgroupCorank V U ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  let P := (unipotentSylow F (by omega : 0 < subgroupCorank V U) hF).mapSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L P S
  let j : PSL(3,F) ≃* L := e.symm.trans (MulAut.conj g)
  let f : PSL(3,F) →* G := L.subtype.comp j.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp j.injective
  have hjS : (unipotent F).map j.toMonoidHom = (S : Subgroup L) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh
  have hjB : (borel F).map f = L ⊓ M := by
    rw [show f = L.subtype.comp j.toMonoidHom from rfl,← Subgroup.map_map,
      ← normalizer_unipotent F (by omega) hF,map_equiv_normalizer_eq,hjS]
    exact hB
  have hjZ : (projectiveCenter F).map f = ⁅V,L ⊓ M⁆ := by
    rw [show f = L.subtype.comp j.toMonoidHom from rfl,← Subgroup.map_map,
      projectiveCenter_eq_mapped_center,map_subgroup_center_eq j.toMonoidHom j.injective,
      hjS,map_subgroup_center_eq L.subtype L.subtype_injective,hS,hcent]
  have hZV : (projectiveCenter F).map f ≤ V := by
    rw [hjZ]
    exact le_sup_left.trans (b.decomposition hn).1.le
  have hjC : (centralizer (projectiveCenter F : Set PSL(3,F))).map f =
      L ⊓ centralizer (V : Set G) := by
    rw [← displacement_centralizer b hn,← hjZ]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨(j x).property,mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨z,hz,rfl⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx z hz)
    · rintro x ⟨hxL,hxC⟩
      refine ⟨j.symm ⟨x,hxL⟩,mem_centralizer_iff.mpr ?_,?_⟩
      · intro z hz
        apply hf
        have he : f (j.symm ⟨x,hxL⟩) = x := by
          change (j (j.symm ⟨x,hxL⟩) : G) = x
          rw [j.apply_symm_apply]
        simpa only [map_mul,he] using mem_centralizer_iff.mp hxC
          (f z) (mem_map_of_mem f hz)
      · change (j (j.symm ⟨x,hxL⟩) : G) = x
        rw [j.apply_symm_apply]
  let Y : Subgroup G := (rootTorus F).range.map f
  have hYB : Y ≤ L ⊓ M := hjB ▸ map_mono (rootTorus_le_borel F)
  have hgen : (L ⊓ centralizer (V : Set G)) ⊔ Y = L ⊓ M := by
    rw [← hjC,← Subgroup.map_sup,rootTorus_complement,hjB]
  have hdisj : (L ⊓ centralizer (V : Set G)) ⊓ Y = ⊥ := by
    rw [← hjC,← Subgroup.map_inf _ _ _ hf,rootTorus_disjoint,Subgroup.map_bot]
  have hfaith : Y ⊓ centralizer (V : Set G) = ⊥ := by
    apply bot_unique
    rintro y ⟨hy,hc⟩
    exact hdisj ▸ (show y ∈ (L ⊓ centralizer (V : Set G)) ⊓ Y from
      ⟨⟨(hYB hy).1,hc⟩,hy⟩)
  have hBN : L ⊓ M ≤ normalizer (V : Set G) := component_intersection_normalizes h hU hL.1
  have hYloc : Y ≤ localNormalizer M V ⊓ centralizer (U : Set G) :=
    le_inf (le_inf (hYB.trans inf_le_right) (hYB.trans hBN))
      ((hYB.trans inf_le_left).trans hL.1)
  have hi := inducedAutomizer_eq_of_centralizing_complements
    (inf_le_right : L ⊓ centralizer (V : Set G) ≤ _) hBN t.complement hgen
  refine ⟨Y,hYB.trans inf_le_left,regularCyclicSection_of_same_image hX hYloc hfaith hi,
    hi,F,inferInstance,inferInstance,inferInstance,hF,j.symm,hjB,hZV,rfl⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
