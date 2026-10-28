module

public import Theory.Alternating.OddCentralCovers

/-!
# Triple-cover comparison over the prescribed A₆ projection

This retains the projection equation in Schur's uniqueness theorem when
comparing an arbitrary central triple cover with the even hexacode group.
The finite-universe transport is the one already used by
`OddCentralCovers.triple_cover_equiv`; the quotient marking is retained here.

Source: GLS, volume 3, Theorem 5.2.3; Aschbacher--Smith, A.3.5 and K.1.3.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Atlas.Codes
open GLS3.Chapter5.SchurPresentation

namespace Representation.Hexacode.CoverComparison

/-- The unique triple-cover comparison can be chosen over the literal
alternating-coordinate projection, in every source universe. -/
theorem exists_even_equiv_over_coordinate
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L (alternatingGroup (Fin 6)))
    (hk : Nat.card f.toMonoidHom.ker = 3) :
    ∃ e : L ≃* HexEvenAutomorphisms,
      hexEvenCoordinate.comp e.toMonoidHom = f.toMonoidHom := by
  let _ : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let fhex : Covering HexEvenAutomorphisms (alternatingGroup (Fin 6)) := {
    toMonoidHom := hexEvenCoordinate
    surjective := hexEvenCoordinate_surjective }
  obtain ⟨S, iS, finS, ⟨s⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} L
  let _ := iS
  let _ := finS
  let _ : IsQuasisimple S := IsQuasisimple.of_mulEquiv s
  let fS := f.comp (Covering.ofMulEquiv s.symm)
  have hkS : Nat.card fS.toMonoidHom.ker = 3 := by
    rw [← hk]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨s.symm x, x.property⟩
      invFun := fun x => ⟨s x, by
        change f (s.symm (s x)) = 1
        rw [s.symm_apply_apply]
        exact x.property⟩
      left_inv := fun x => Subtype.ext (s.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (s.symm_apply_apply x) }
  obtain ⟨U, iU, finU, qU, fu, hu, hcyc, hcard⟩ :=
    theorem_5_2_3_c_multiplier_a6
  let _ := iU
  let _ := finU
  let _ := qU
  obtain ⟨e, he, _⟩ :=
    coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      fu hu hcyc hcard fS fhex hkS hexEven_kernel_card
  refine ⟨s.trans e, ?_⟩
  apply MonoidHom.ext
  intro x
  have hx := congrArg
    (fun p : Covering S (alternatingGroup (Fin 6)) => p (s x)) he
  change hexEvenCoordinate (e (s x)) = f (s.symm (s x)) at hx
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    Covering.toMonoidHom_apply]
  simpa only [s.symm_apply_apply] using hx

end Representation.Hexacode.CoverComparison
