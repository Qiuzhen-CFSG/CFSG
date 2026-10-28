module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.NonprimitiveRecognition.OrbitImages

/-!
# Passing from symmetric action images to alternating degree induction

A perfect subgroup has trivial sign. Its relative subnormality therefore
restricts to the even part of the actual permutation image, where the given
smaller-degree induction applies. Excluding degree seven before increasing
the ambient bound prevents propagation of the exceptional model.

Source: the alternating Sylow-overgroup argument in Aschbacher–Smith B.1.13,
printed p.74 (PDF p.85). Sylow containment of the even image is an explicit
geometric premise of this transfer lemma.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The even preimage after a specified relabelling of the permutation set. -/
@[expose] def alternatingEvenPreimage {Ω : Type*} {n : ℕ}
    (Y : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Fin n) :
    Subgroup (alternatingGroup (Fin n)) :=
  Y.comap ((Equiv.permCongrHom e.symm).toMonoidHom.comp
    (alternatingGroup (Fin n)).subtype)

/-- Smaller alternating classification applies to an actual symmetric image
once its even preimage contains an alternating Sylow subgroup. -/
theorem alternating_component_models_of_even_preimage
    {Ω : Type*} {m n : ℕ} (hsmall : AlternatingAllSylowComponentModels n)
    (hnm : n ≤ m) (hn7 : n ≠ 7)
    (Y : Subgroup (Equiv.Perm Ω)) (e : Ω ≃ Fin n)
    (S : Sylow 2 (alternatingGroup (Fin n)))
    (hS : (S : Subgroup _) ≤ alternatingEvenPreimage Y e)
    (D : Subgroup Y) (hD : IsComponent Y D) : AlternatingSubgroupModels m D := by
  let A := alternatingEvenPreimage Y e
  let j : A →* Y :=
    { toFun := fun a => ⟨Equiv.permCongr e.symm a.val.val, a.property⟩
      map_one' := by apply Subtype.ext; exact (Equiv.permCongrHom e.symm).map_one
      map_mul' := fun a b => by
        apply Subtype.ext
        exact (Equiv.permCongrHom e.symm).map_mul a.val.val b.val.val }
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (Equiv.permCongrHom e.symm).injective (congrArg Subtype.val hab)
  let := hD.2
  have hEven (d : D) : Equiv.Perm.sign (Equiv.permCongr e d.val.val) = 1 := by
    let f : D →* ℤˣ := Equiv.Perm.sign.comp
      ((Equiv.permCongrHom e).toMonoidHom.comp (Y.subtype.comp D.subtype))
    exact Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator
  have hmap : (D.comap j).map j = D := by
    apply le_antisymm (map_comap_le _ _)
    intro d hd
    let a : A := ⟨⟨Equiv.permCongr e d.val, hEven ⟨d, hd⟩⟩, by
      change Equiv.permCongr e.symm (Equiv.permCongr e d.val) ∈ Y
      change (Equiv.permCongrHom e).symm ((Equiv.permCongrHom e) d.val) ∈ Y
      rw [MulEquiv.symm_apply_apply]
      exact d.property⟩
    have ha : j a = d := by
      apply Subtype.ext
      exact (Equiv.permCongrHom e).symm_apply_apply d.val
    exact ⟨a, by change j a ∈ D; rw [ha]; exact hd, ha⟩
  let dEquiv : D.comap j ≃* D :=
    (equivMapOfInjective (D.comap j) j hj).trans (MulEquiv.subgroupCongr hmap)
  have hcomp : IsComponent A (D.comap j) :=
    ⟨hD.1.comap j, IsQuasisimple.of_mulEquiv dEquiv.symm⟩
  have hmodels : AlternatingSubgroupModels n D :=
    (hsmall S A hS _ hcomp).of_mulEquiv dEquiv.symm
  rcases hmodels with ⟨k, hk, hkn, he⟩ | ⟨hn, _⟩
  · exact Or.inl ⟨k, hk, hkn.trans hnm, he⟩
  · exact (hn7 hn).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
