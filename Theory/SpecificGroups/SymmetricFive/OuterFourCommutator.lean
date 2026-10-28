module
public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry

/-!
# An even Sylow element moving an outer four-group in S₅

Transport the actual Sylow and outer four-group to the existing common
marking. The even double transposition exchanges the two generating
transpositions, so their commutator is nontrivial. The resulting witnesses
retain the original Sylow and four-group.

Application: the residual involution in the nonsolvable branch of
Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.SymmetricFive.OuterFourCommutator
open OuterFourGeometry

theorem exists_even_commutator (P : Sylow 2 D) (B : Subgroup D)
    [IsElementaryAbelian 2 B] (hcard : Nat.card B=4) (hBP : B≤(P:Subgroup D))
    (hout : ¬ B≤alternatingGroup (Fin 5)) :
    ∃ a ∈ (P:Subgroup D), a ∈ alternatingGroup (Fin 5) ∧
      ∃ b ∈ B, ⁅a,b⁆ ≠ 1 := by
  obtain ⟨e,hP,hB⟩ := exists_marking P B hcard hBP hout
  have hA : (alternatingGroup (Fin 5)).map e.toMonoidHom = alternatingGroup (Fin 5) :=
    characteristic_iff_map_eq.mp inferInstance e
  have hcP : c ∈ (P:Subgroup D).map e.toMonoidHom := hP.symm ▸ (show c∈eight from ⟨4,rfl⟩)
  obtain ⟨a,ha,hac⟩ := hcP
  have haeven : a ∈ alternatingGroup (Fin 5) := by
    have hc : c ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
    rw [←hA] at hc
    obtain ⟨a',ha',he⟩ := hc
    exact (e.injective (he.trans hac.symm)) ▸ ha'
  have hbB : OuterFourGeometry.a ∈ B.map e.toMonoidHom := hB.symm ▸ (show OuterFourGeometry.a∈four from ⟨1,rfl⟩)
  obtain ⟨b,hb,hba⟩ := hbB
  change e a = c at hac
  change e b = OuterFourGeometry.a at hba
  refine ⟨a,ha,haeven,b,hb,?_⟩
  intro hz
  have hh := congrArg e hz
  simp only [map_commutatorElement,map_one,hac,hba] at hh
  exact (by decide +kernel : ⁅c,OuterFourGeometry.a⁆ ≠ 1) hh
end Theory.SpecificGroups.SymmetricFive.OuterFourCommutator
