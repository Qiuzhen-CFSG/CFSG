module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.ModuleCentralizer
public import Theory.Representation.BinaryPermutation.PairedResidual.PointFixer

/-!
# Full-cover centralizer of the paired A₄ in an ordinary A₇ block

An automorphism fixing the paired residual has at most two permutation
images. If that image is trivial, cohomology makes the automorphism inner
by a vector of U(L). The paired A₄ fixes only a line in that module, so
there are at most two such kernel automorphisms. Thus every subgroup
fixing the actual residual has order at most four.

The coordinates retain any specified isomorphism of L/O₂(L) with A₇.
The prime-five consumer in Chapter15 uses this bound to exclude a faithful
sixteen-element moving support. Source: Aschbacher--Smith C.1.13(c),
15.1.23 and the partition geometry of 15.1.25(5), pp.124,1100,1102.
The bound itself uses no later exchanged-component or index conclusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
open BinaryPermutation AlternatingSeven.ThreeResidualLocals
variable {L : Type*} [Group L] [Finite L]

private theorem card_le_two_of_values {A X : Type*} [Finite X]
    (f : A → X) (hf : Function.Injective f) (x y : X)
    (h : ∀ a, f a = x ∨ f a = y) : Nat.card A ≤ 2 := by
  classical
  let k : A → ({x,y} : Finset X) := fun a => ⟨f a, by simpa using h a⟩
  have hk : Function.Injective k := fun a b he => hf (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective k hk).trans (by rw [Nat.card_eq_finsetCard]; exact Finset.card_le_two)

private theorem seven_centralizer_card
    (h : IsAlternatingBlock L 7)
    (q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (E : blockU L ≃* Multiplicative (core (Fin 7)))
    (f : MulAut L →* Equiv.Perm (Fin 7))
    (hf : ∀ l : L, f (MulAut.conj l) = (q (QuotientGroup.mk' (pCore 2 L) l)).val)
    (hE : ∀ a u, (E (MulAut.characteristic (blockU L) a u)).toAdd =
      coreRepresentation (Fin 7) (f a) (E u).toAdd)
    (R : Subgroup L) (c : Perm7)
    (hi : pairedFour.map (MulAut.conj c).toMonoidHom ≤
      R.map ((alternatingGroup (Fin 7)).subtype.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (B : Subgroup (MulAut L))
    (hB : ∀ a ∈ B, ∀ r ∈ R, a r = r) : Nat.card B ≤ 4 := by
  classical
  let g := f.comp B.subtype
  have him (a : B) : f a ∈ centralizer
      (pairedFour.map (MulAut.conj c).toMonoidHom : Set Perm7) := by
    intro x hx
    have hx := hi hx
    obtain ⟨r,hr,rfl⟩ := hx
    have he : MulAut.conj r * a.val = a.val * MulAut.conj r := by
      ext t
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hB a a.property r hr]
    have hh := congrArg f he
    change (q (QuotientGroup.mk' (pCore 2 L) r)).val * f a =
      f a * (q (QuotientGroup.mk' (pCore 2 L) r)).val
    simpa only [map_mul,hf] using hh
  have himval (a : B) : f a = 1 ∨ f a = (MulAut.conj c) pairing := by
    let e := MulAut.conj c
    have hh : e.symm (f a) ∈ centralizer (pairedFour : Set Perm7) := by
      intro x hx
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using
        him a (e x) (mem_map_of_mem e.toMonoidHom hx)
    rcases (centralizer_pairedFour_iff _).mp hh with hh | hh
    · left
      exact e.symm.injective (hh.trans e.symm.map_one.symm)
    · right
      exact (e.apply_symm_apply (f a)).symm.trans (congrArg e hh)
  have hrange : Nat.card g.range ≤ 2 := by
    apply card_le_two_of_values g.range.subtype g.range.subtype_injective
      1 ((MulAut.conj c) pairing)
    rintro ⟨_,a,rfl⟩
    exact himval a
  let z : blockU L := E.symm (Multiplicative.ofAdd
    (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix))
  have hker : Nat.card g.ker ≤ 2 := by
    let j : g.ker → MulAut L := fun a => a.val.val
    have hj : Function.Injective j := fun a b he => Subtype.ext (Subtype.ext he)
    apply card_le_two_of_values j hj 1 (MulAut.conj (z : L)⁻¹)
    intro a
    have haf : f a.val.val = 1 := a.property
    have hfix (u : L) (hu : u ∈ blockU L) : a.val.val u = u := by
      have hh := hE a.val.val ⟨u,hu⟩
      rw [haf,map_one,Module.End.one_apply] at hh
      exact congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hh))
    obtain ⟨u,hu⟩ := h.seven_automorphism_inner_of_fixing_module a.val.val hfix
    have hufix : ∀ x ∈ pairedFour.map (MulAut.conj c).toMonoidHom,
        coreRepresentation (Fin 7) x (E u).toAdd = (E u).toAdd := by
      intro x hx
      have hx := hi hx
      obtain ⟨r,hr,rfl⟩ := hx
      have har := hB a.val.val a.val.property r hr
      have hur : (u : L) * r = r * u := by
        have hh := hu r
        rw [har] at hh
        calc
          (u : L) * r = u * ((u : L)⁻¹ * r * u) := congrArg (fun t : L => (u : L) * t) hh
          _ = r * u := by group
      have he : MulAut.characteristic (blockU L) (MulAut.conj r) u = u := by
        apply Subtype.ext
        change r * (u : L) * r⁻¹ = u
        rw [←hur,mul_inv_cancel_right]
      have hh := hE (MulAut.conj r) u
      rw [he,hf] at hh
      exact hh.symm
    rcases conjugate_pairedFour_fixed c (E u).toAdd hufix with he | he
    · have hu1 : u = 1 := E.injective (Multiplicative.toAdd.injective (he.trans (by simp)))
      left
      ext x
      change a.val.val x = x
      simpa only [hu1,coe_one,inv_one,one_mul,mul_one] using hu x
    · have huz : u = z := by
        apply E.injective
        rw [show E z = Multiplicative.ofAdd
          (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix) from E.apply_symm_apply _]
        exact Multiplicative.toAdd.injective he
      right
      ext x
      simpa only [huz,MulAut.conj_apply,inv_inv] using hu x
  have hc := g.ker.card_mul_index
  rw [index_ker] at hc
  calc
    Nat.card B = Nat.card g.ker * Nat.card g.range := hc.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange

omit [Finite L] in
private theorem seven_coordinates_at (h : IsAlternatingBlock L 7)
    (q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    ∃ E : blockU L ≃* Multiplicative (core (Fin 7)),
    ∃ f : MulAut L →* Equiv.Perm (Fin 7),
      (∀ l : L, f (MulAut.conj l) = (q (QuotientGroup.mk' (pCore 2 L) l)).val) ∧
      ∀ a u, (E (MulAut.characteristic (blockU L) a u)).toAdd =
        coreRepresentation (Fin 7) (f a) (E u).toAdd := by
  obtain ⟨q0,E0,f0,hq0,hE0⟩ := h.seven_automorphism_coordinates
  let a := q0.symm.trans q
  let c := SevenNormalizer.permutationOfAut a
  let e := MulAut.conj c
  let E := E0.trans (SevenMarkedAction.coreAction c)
  let f := e.toMonoidHom.comp f0
  have ha (x : alternatingGroup (Fin 7)) : (a x).val = e x.val := by
    exact (congrArg (fun b : MulAut (alternatingGroup (Fin 7)) => (b x).val)
      (SevenNormalizer.conjugation_permutationOfAut a)).symm
  refine ⟨E,f,?_,?_⟩
  · intro l
    change e (f0 (MulAut.conj l)) = _
    rw [hq0,←ha]
    simp only [a,MulEquiv.trans_apply,q0.symm_apply_apply]
  · intro b u
    change coreRepresentation (Fin 7) c
      (E0 (MulAut.characteristic (blockU L) b u)).toAdd =
      coreRepresentation (Fin 7) (c * f0 b * c⁻¹)
        (coreRepresentation (Fin 7) c (E0 u).toAdd)
    rw [hE0]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- Fixers of the actual paired A₄ residual have at most four automorphisms,
including the possible central attachment in the block cover. -/
theorem IsAlternatingBlock.seven_paired_residual_fixer_card_le_four (h : IsAlternatingBlock L 7)
    (q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (R : Subgroup L) (c : Perm7)
    (hi : pairedFour.map (MulAut.conj c).toMonoidHom ≤
      R.map ((alternatingGroup (Fin 7)).subtype.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (B : Subgroup (MulAut L))
    (hB : ∀ a ∈ B, ∀ r ∈ R, a r = r) : Nat.card B ≤ 4 := by
  obtain ⟨E,f,hf,hE⟩ := seven_coordinates_at h q
  exact seven_centralizer_card h q E f hf hE R c hi B hB

end CFSG.Quasithin.ChapterC
