module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.Alternating.theorem_5_2_3
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Mathlib.Algebra.Group.Shrink

/-!
# Recognition of the marked hexacode triple cover

The universal A₆ cover has cyclic kernel of order six. Any two triple
covers are quotients by the same subgroup of order two, and hence are
uniquely isomorphic over A₆. Apply that
comparison to an arbitrary perfect central triple cover and the actual
even hexacode coordinate map. Shrinking the finite input handles arbitrary
universes without changing either the quotient map or the resulting marking.

Source: GLS3, Theorem 5.2.3(c), and the convention for Â₆ in
Aschbacher–Smith, A.3.5, printed p.43 (PDF p.54).
-/

public section
open Subgroup Theory.GroupTheory Atlas.Codes
namespace Representation.Hexacode
noncomputable section

/-- Every perfect central triple cover of A₆ is the concrete even hexacode
group, by an equivalence commuting with the given quotient map. -/
theorem triple_cover_equiv {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center E) (hcard : Nat.card f.ker = 3) :
    ∃ e : E ≃* HexEvenAutomorphisms,
      hexEvenCoordinate.comp e.toMonoidHom = f := by
  let s : Shrink.{0} E ≃* E := Shrink.mulEquiv
  let : Finite (Shrink.{0} E) := Finite.of_equiv E s.symm.toEquiv
  let g := f.comp s.toMonoidHom
  let : Group.IsPerfect (Shrink.{0} E) :=
    Group.IsPerfect.ofSurjective (f := s.symm.toMonoidHom) s.symm.surjective
  have hgc : g.ker ≤ center (Shrink.{0} E) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply s.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using mem_center_iff.mp (hcentral hx) (s y)
  have hgcard : Nat.card g.ker = 3 := by
    have hker : g.ker = f.ker.map s.symm.toMonoidHom :=
      MonoidHom.ker_comp_mulEquiv f s
    rw [hker, card_map_of_injective s.symm.injective, hcard]
  let gc : PerfectCentralCovering.Cover (Shrink.{0} E) (alternatingGroup (Fin 6)) :=
    { toMonoidHom := g, surjective := hf.comp s.surjective,
      isPerfect := inferInstance, ker_le_center := hgc }
  let : IsQuasisimple (Shrink.{0} E) := gc.isQuasisimple
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let hc : Covering HexEvenAutomorphisms (alternatingGroup (Fin 6)) :=
    { toMonoidHom := hexEvenCoordinate, surjective := hexEvenCoordinate_surjective }
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, hcyc, horder⟩ :=
    GLS3.Chapter5.SchurPresentation.theorem_5_2_3_c_multiplier_a6
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨e, he, _⟩ :=
    GLS3.Chapter5.SchurPresentation.coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      f₀ hf₀ hcyc horder gc.toCovering hc hgcard hexEven_kernel_card
  refine ⟨s.symm.trans e, ?_⟩
  apply MonoidHom.ext
  intro x
  have h := DFunLike.congr_fun he (s.symm x)
  change hexEvenCoordinate (e (s.symm x)) = f (s (s.symm x)) at h
  simpa only [MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using h
end
end Representation.Hexacode
