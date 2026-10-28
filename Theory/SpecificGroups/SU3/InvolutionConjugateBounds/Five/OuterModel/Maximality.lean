module
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Setup
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Maximality
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.GroupAction.AutomorphismOddOuter

/-!
# Relative maximality of the marked S₇ image

An injective S₇ image taking even permutations to inner automorphisms yields
an actual A₇ embedding in PSU₃(5). Inner conjugation is faithful: its kernel
is normal in the inherited simple group, and the nontrivial even image
excludes the whole kernel. The accepted A₇ maximality theorem applies after
transport from the antidiagonal form to the identity-Gram form.

For an overgroup inside the actor's extension, its inverse image under inner
conjugation is either this A₇ or all of PSU₃(5). The normality of the inner
automorphisms and the presence of the marked actor then force the overgroup
to be the S₇ image or the whole extension. The orders 126000 and 5040 rule
out equality of the original image with the extension. No maximal-subgroup
classification or full-automorphism maximality is assumed.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11. The A₇ maximality and group-order calculations are
reused from `Five.InnerModel.Maximality` without altering that module.
-/

public noncomputable section
open Subgroup Equiv
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The antidiagonal and identity-Gram projective matrix groups are isomorphic. -/
theorem exists_concrete_equiv_standard : Nonempty (ConcreteGroup ≃* StandardGroup) :=
  Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard 5 _ concreteForm
    (GaloisField.card 5 (2 * 1) (by decide)) concreteForm_conj

private theorem concrete_card : Nat.card ConcreteGroup = 126000 := by
  obtain ⟨e⟩ := exists_concrete_equiv_standard
  exact (Nat.card_congr e.toEquiv).trans standardGroup_card

private theorem concrete_alternating_maximal [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j) :
    IsCoatom j.range := by
  obtain ⟨e⟩ := exists_concrete_equiv_standard
  let : IsSimpleGroup StandardGroup := e.symm.isSimpleGroup
  have hh := alternatingSeven_range_isCoatom (e.toMonoidHom.comp j) (e.injective.comp hj)
  rw [MonoidHom.range_comp] at hh
  exact (e.mapSubgroup.isCoatom_iff j.range).mp hh

private theorem conj_injective_of_even [IsSimpleGroup ConcreteGroup]
    (f : Perm (Fin 7) →* MulAut ConcreteGroup) (hf : Function.Injective f)
    (heven : ∀ q : alternatingGroup (Fin 7),
      f (q : Perm (Fin 7)) ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).range) :
    Function.Injective (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).ker.Normal).eq_bot_or_eq_top
    with hh | hh
  · exact hh
  · let q : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 2, by
      rw [Perm.mem_alternatingGroup]; decide +kernel⟩
    obtain ⟨s, hs⟩ := heven q
    have hs1 : MulAut.conj s = 1 :=
      show s ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).ker from hh ▸ mem_top s
    have hq1 : (q : Perm (Fin 7)) = 1 := hf (by rw [← hs, hs1, map_one])
    exact False.elim ((by decide +kernel : (q : Perm (Fin 7)) ≠ 1) hq1)

/-- Maximality inside the marked involution's own extension follows from
maximality of the embedded alternating subgroup in the inner group. -/
theorem marked_range_covBy [IsSimpleGroup ConcreteGroup]
    (f : Perm (Fin 7) →* MulAut ConcreteGroup) (hf : Function.Injective f)
    (heven : ∀ q : alternatingGroup (Fin 7),
      f (q : Perm (Fin 7)) ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).range)
    (hmark : f tripleSwap = concreteActor) :
    f.range ⋖ MulAut.singleInnerExtension concreteActor := by
  let c : ConcreteGroup →* MulAut ConcreteGroup := MulAut.conj
  have hc : Function.Injective c := conj_injective_of_even f hf heven
  let e : ConcreteGroup ≃* c.range := MonoidHom.ofInjective hc
  let g : alternatingGroup (Fin 7) →* c.range :=
    (f.comp (alternatingGroup (Fin 7)).subtype).codRestrict _ heven
  let j : alternatingGroup (Fin 7) →* ConcreteGroup := e.symm.toMonoidHom.comp g
  have hjc (q : alternatingGroup (Fin 7)) : c (j q) = f (q : Perm (Fin 7)) := by
    exact congrArg Subtype.val (e.apply_symm_apply (g q))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply hf
    rw [← hjc, ← hjc, h]
  have hjmax := concrete_alternating_maximal j hj
  have hle := marked_range_le concreteActor f heven hmark
  have hproper : f.range ≠ MulAut.singleInnerExtension concreteActor := by
    intro heq
    have hin : c.range ≤ f.range := heq ▸ le_sup_left
    let k : ConcreteGroup →* f.range := c.codRestrict _ (fun s => hin ⟨s, rfl⟩)
    have hk : Function.Injective k := fun x y hh => hc (congrArg Subtype.val hh)
    let : Finite f.range := Finite.of_equiv _ (MonoidHom.ofInjective hf).toEquiv
    have hn := Nat.card_le_card_of_injective k hk
    have hr : Nat.card f.range = 5040 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [concrete_card, hr] at hn
    omega
  apply covBy_of_eq_or_eq (lt_of_le_of_ne hle hproper)
  intro K hK hKE
  have hjle : j.range ≤ K.comap c := by
    rintro _ ⟨q, rfl⟩
    change c (j q) ∈ K
    rw [hjc]
    exact hK ⟨q, rfl⟩
  by_cases htop : K.comap c = ⊤
  · right
    apply le_antisymm hKE
    apply sup_le
    · rintro _ ⟨s, rfl⟩
      exact (show s ∈ K.comap c from htop ▸ mem_top s)
    · apply (closure_le _).mpr
      intro x hx
      have hx' : x = concreteActor := Set.mem_singleton_iff.mp hx
      rw [hx', ← hmark]
      exact hK ⟨tripleSwap, rfl⟩
  · left
    have heq : K.comap c = j.range := hjmax.le_iff_eq htop |>.mp hjle
    apply le_antisymm ?_ hK
    intro x hx
    obtain ⟨y, ⟨s, rfl⟩, z, hz, rfl⟩ := mem_sup_of_normal_left.mp (hKE hx)
    have hza : closure {concreteActor} ≤ f.range := (closure_le _).mpr (by
      intro v hv
      rw [Set.mem_singleton_iff.mp hv, ← hmark]
      exact ⟨tripleSwap, rfl⟩)
    have hzK := hK (hza hz)
    have hsK : s ∈ K.comap c := by
      change c s ∈ K
      exact (mul_mem_cancel_right hzK).mp hx
    rw [heq] at hsK
    obtain ⟨q, hq⟩ := hsK
    have hcs : c s ∈ f.range := by
      rw [← hq, hjc]
      exact ⟨q, rfl⟩
    exact f.range.mul_mem hcs (hza hz)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
