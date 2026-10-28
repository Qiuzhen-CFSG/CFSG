module

public import Theory.Representation.BinaryAlternatingSixSmallDegrees
public import Theory.Representation.NormalComponentConstituents
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry

/-!
# A normal ordinary A6 cannot act faithfully on an irreducible binary six-space

An actual normal A6 has an irreducible nontrivial constituent of dimension
four. Its distinct conjugates are disjoint and would have combined
dimension eight. Thus that constituent is invariant in the whole actor,
contrary to irreducibility in dimension six. The subgroup remains literal;
no ambient A6 model or assumption about its centralizer is introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace AlternatingSix.BinarySmallDegrees
variable {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem not_normal_six_space (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (H : Subgroup D) [H.Normal] (e : H≃*alternatingGroup (Fin 6)) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcard : Nat.card H=360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hH : H≠⊥ := by intro he; rw [he,card_bot] at hcard; omega
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf H hH
  let σ := (invariantSubspace ρ H I hI.choose).toRepresentation
  have hirr : Representation.IsIrreducible σ := hI.irreducible_of_normal_restriction ρ hi H
  let τ := σ.comp e.symm.toMonoidHom
  let : Representation.IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr hirr
  have hId : Module.finrank (ZMod 2) I≤6 := (Submodule.finrank_le I).trans hd.le
  have hfour : Module.finrank (ZMod 2) I=4 := by
    rcases finrank_eq_one_or_four τ hId with h1 | h4
    · apply (hI.not_le_fixedSpace ρ).elim
      intro v hv g
      have hg := representation_eq_one_of_isPerfect_of_finrank_le_two σ (by omega) g
      exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨v,hv⟩ : V)) hg
    · exact h4
  have stable (g : D) : I.map (ρ g)=I := by
    rcases hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H g with he | hdis
    · exact he
    · have hadd := (I.map (ρ g)).finrank_sup_add_finrank_inf_eq I
      have hbound := Submodule.finrank_le (I.map (ρ g) ⊔ I)
      rw [hdis.eq_bot,finrank_bot,add_zero,finrank_map_action,hfour] at hadd
      omega
  let B : Subrepresentation ρ := ⟨I,fun g v hv => stable g ▸
    (show ρ g v∈I.map (ρ g) from ⟨v,hv,rfl⟩)⟩
  rcases hi.eq_bot_or_eq_top B with hb | ht
  · have he : I=⊥ := congrArg Subrepresentation.toSubmodule hb
    exact hI.ne_bot ρ he
  · have he : I=⊤ := congrArg Subrepresentation.toSubmodule ht
    rw [he,finrank_top,hd] at hfour
    omega

end AlternatingSix.BinarySmallDegrees
