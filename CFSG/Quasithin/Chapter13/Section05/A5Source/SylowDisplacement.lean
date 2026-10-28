module

public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import Theory.Representation.BinaryPermutation.FiveMovedHyperplanes

/-!
# Sylow displacement in the original alternating-five module

The image of the actual Sylow intersection in the marked A₅ action is a
Sylow four-group. Conjugating the regular four-group into that image puts
its moved hyperplane inside the actual commutator `[V,T ∩ L]`. The marked
embedding preserves its order eight.

This supplies the displacement obstruction for the original 5.2.3 cubic
source. It uses the chosen deleted-permutation module in the original
Context, without classifying arbitrary four-dimensional A₅ modules.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open BinaryPermutation BinaryPermutation.FiveMovedHyperplanes
open BinaryPermutation.CubicFixedSpace.Five
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The actual Sylow intersection moves at least eight points of the marked
module, measured in the literal ambient commutator subgroup. -/
theorem eight_le_card_sylow_commutator (d : Context T L V V₁ V₂ V₃) :
    8 ≤ Nat.card (⁅V, (T : Subgroup G) ⊓ L⁆ : Subgroup G) := by
  obtain ⟨S,hS⟩ := d.local_sylow
  let P := S.mapSurjective d.flag.module.onto
  obtain ⟨Q,hQ⟩ := klein_isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q P
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = P := by
    rw [←hg]
    rfl
  let i := d.flag.module.map.comp (coordinateAut g).toMonoidHom
  have hi : Function.Injective i := d.flag.module.injective.comp (coordinateAut g).injective
  have hV (x : Multiplicative (core (Fin 5))) : i x ∈ V :=
    d.flag.module.range_eq.le ⟨coordinateAut g x,rfl⟩
  have hle : moved.map i ≤ ⁅(T : Subgroup G) ⊓ L,V⁆ := by
    rw [map_le_iff_le_comap]
    apply moved_le_of_differences
    intro a ha x
    have hak : a ∈ klein := by
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact first_mem
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact second_mem
      have he : a = first * second := Set.mem_singleton_iff.mp ha
      exact he ▸ klein.mul_mem first_mem second_mem
    have hga : g * a * g⁻¹ ∈ (P : Subgroup _) := by
      rw [←hP]
      exact ⟨a,hQ hak,rfl⟩
    obtain ⟨l,hl,he⟩ := hga
    have hlT : (l : G) ∈ (T : Subgroup G) ⊓ L :=
      hS ▸ mem_map_of_mem L.subtype hl
    have hc : i (Multiplicative.ofAdd (act a x - x)) =
        ⁅(l : G),i (Multiplicative.ofAdd x)⁆ := by
      have heq := d.flag.module.equivariant l (act g x)
      rw [he] at heq
      change d.flag.module.map (Multiplicative.ofAdd (act g (act a x - x))) = _
      rw [map_sub,coordinateAut_conj,ofAdd_sub,map_div,div_eq_mul_inv,←heq]
      rfl
    change i (Multiplicative.ofAdd (act a x - x)) ∈
      (⁅(T : Subgroup G) ⊓ L,V⁆ : Subgroup G)
    rw [hc]
    exact commutator_mem_commutator hlT (hV _)
  have hcard := card_le_of_le hle
  rwa [card_map_of_injective hi,card_moved,commutator_comm] at hcard

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
