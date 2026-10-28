module

public import Theory.GroupTheory.DihedralEightSections

/-!
# Sections retaining the whole Sylow order

If a quotient of a subgroup has the same Sylow order as the ambient group,
the inclusion and the quotient map between the lifted Sylow groups are
bijections. Thus the section has the actual ambient Sylow group. This
retains group structure, beyond numerical divisibility, in the component
sieves of Aschbacher--Smith F.6.18, printed p.310.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

theorem sylow_section_equiv_of_card_eq
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (hc : Nat.card P = Nat.card T) : Nonempty (P ≃* T) := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  let eQ : ((S : Subgroup K).map f) ≃* P :=
    MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hS)
  let q : S →* P := eQ.toMonoidHom.comp (f.subgroupMap (S : Subgroup K))
  have hq : Function.Surjective q :=
    eQ.surjective.comp (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U, hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  let i : S →* U := (Subgroup.inclusion hU).comp
    (K.subtype.subgroupMap (S : Subgroup K))
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) h
  have hUc : Nat.card U = Nat.card T := Nat.card_congr (U.equiv T).toEquiv
  have hSc : Nat.card S = Nat.card T := by
    apply le_antisymm
    · exact (Nat.card_le_card_of_injective i hi).trans_eq hUc
    · exact hc ▸ Nat.card_le_card_of_surjective q hq
  let eq : S ≃* P := MulEquiv.ofBijective q
    ((Nat.bijective_iff_surjective_and_card q).mpr ⟨hq, hSc.trans hc.symm⟩)
  let ei : S ≃* U := MulEquiv.ofBijective i
    ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi, hSc.trans hUc.symm⟩)
  exact ⟨(eq.symm.trans ei).trans (U.equiv T)⟩

end Theory.GroupTheory
