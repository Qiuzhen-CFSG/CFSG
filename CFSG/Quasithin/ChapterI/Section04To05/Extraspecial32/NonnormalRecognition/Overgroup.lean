module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.LocalStructure
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions

/-!
# The degree-nine endpoint of the nonnormal quaternion branch

An A₈ subgroup containing the full centralizer of the distinguished involution
has trivial ambient centralizer. If its index is nine, it cannot be normal:
otherwise conjugation embeds the ambient group in Aut(A₈) ≃ S₈, contradicting
the orders. Simplicity of A₈ then makes its normal core trivial. The literal
coset action has degree nine and image of index two in S₉, so gives an actual
equivalence with A₉. No simplicity assumption on the ambient group is used.

This supplies the final permutation-action step in Aschbacher,
“A 2-local characterization of M12”, Illinois J. Math. 47 (2003),
Proposition 3.3, p.38. The preceding fusion calculation establishing index nine
is a separate input. The source application is Aschbacher–Smith I.4.6, p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup
open Theory.SpecificGroups.SymmetricEight.Involutions

variable {G : Type*} [Group G] {z : G}

/-- Containing `C_G(z)` forces this A₈ subgroup to have trivial centralizer. -/
public theorem centralizer_eq_bot (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hC : Centralizer z ≤ L) :
    centralizer (L : Set G) = ⊥ := by
  have hzL : z ∈ L := hC (mem_centralizer_singleton_iff.mpr rfl)
  apply le_bot_iff.mp
  intro x hx
  have hxL : x ∈ L := hC (mem_centralizer_singleton_iff.mpr (hx z hzL).symm)
  let xL : L := ⟨x, hxL⟩
  have he : e xL ∈ center (alternatingGroup (Fin 8)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨y, rfl⟩ := e.surjective a
    simpa only [map_mul] using congrArg e (show y * xL = xL * y from
      Subtype.ext (hx y y.property))
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  have hx1 : xL = 1 := e.injective (he.trans e.map_one.symm)
  exact congrArg Subtype.val hx1

private theorem card_alternating_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- The source index-nine calculation determines the ambient order. -/
public theorem card_of_index_nine (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hi : L.index = 9) :
    Nat.card G = 181440 := by
  have hc : Nat.card L = 20160 := (Nat.card_congr e.toEquiv).trans card_alternating_eight
  have hm := L.card_mul_index
  rw [hc, hi] at hm
  exact hm.symm

/-- An index-nine A₈ containing the full involution centralizer is core-free. -/
public theorem normalCore_eq_bot_of_index_nine [Finite G] (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hC : Centralizer z ≤ L)
    (hi : L.index = 9) : L.normalCore = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := e.isSimpleGroup
  rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup L)).2
      L.normalCore L.normalCore_le (inferInstance) with hb | he
  · exact hb
  · have : L.Normal := he ▸ L.normalCore_normal
    have hinj := MulAut.conjNormal_injective_of_centralizer_eq_bot L
      (centralizer_eq_bot L e hC)
    have hbound := Nat.card_le_card_of_injective
      (MulAut.conjNormal : G →* MulAut L) hinj
    have haut : Nat.card (MulAut L) = 40320 := by
      rw [Nat.card_congr ((MulAut.congr e).trans permutationAutEquiv.symm).toEquiv,
        Nat.card_perm, Nat.card_fin]
      decide
    rw [card_of_index_nine L e hi, haut] at hbound
    omega

/-- The actual action on nine cosets identifies the ambient group with A₉. -/
public theorem alternating_nine_of_index_nine [Finite G] (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hC : Centralizer z ≤ L)
    (hi : L.index = 9) : Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  classical
  let : Fintype (G ⧸ L) := Fintype.ofFinite _
  let labels : (G ⧸ L) ≃ Fin 9 := Fintype.equivFinOfCardEq
    ((Nat.card_eq_fintype_card (α := G ⧸ L)).symm.trans hi)
  let action : G →* Equiv.Perm (Fin 9) :=
    labels.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ L))
  have hinj0 : Function.Injective (MulAction.toPermHom G (G ⧸ L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← L.normalCore_eq_ker]
    exact normalCore_eq_bot_of_index_nine L e hC hi
  have hinj : Function.Injective action := labels.permCongrHom.injective.comp hinj0
  have hr : Nat.card action.range = 181440 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
      (card_of_index_nine L e hi)
  have hperm : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have himage : action.range = alternatingGroup (Fin 9) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hm := action.range.card_mul_index
    rw [hr, hperm] at hm
    omega
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr himage)⟩

/-- The recognition endpoint, once the source's overgroup index is known. -/
public theorem alternating_eight_or_nine [Finite G] (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hC : Centralizer z ≤ L)
    (hi : L = ⊤ ∨ L.index = 9) :
    Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  rcases hi with rfl | hi
  · exact Or.inl ⟨(Subgroup.topEquiv.symm).trans e⟩
  · exact Or.inr (alternating_nine_of_index_nine L e hC hi)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
