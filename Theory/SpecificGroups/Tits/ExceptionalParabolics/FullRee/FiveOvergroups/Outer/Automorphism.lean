module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Core
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms

/-! The checked Parrott assignment gives a genuine Tits automorphism. Its
square and the two original max4 images are retained; an explicit core
involution satisfies the order-sixteen semidihedral relation. -/

@[expose] public section
open Subgroup
noncomputable section
namespace Tits.Max4Outer
open MinimumIndexCandidates
open ExceptionalParabolics.FullRee

theorem satisfies : SatisfiesParrottRelations assignment := by
  intro r
  rw [← parrottRelatorWord_eq,lift_word]
  exact relation r

def hom : Atlas1600Group →* Atlas1600Group :=
  (parrottLift assignment satisfies).comp parrottFiniteImageEquiv.symm.toMonoidHom

theorem hom_generator (i : ParrottGenerator) : hom (atlas1600ParrottAssignment i)=assignment i := by
  rw [← parrottFiniteImageEquiv_generator]
  change parrottLift assignment satisfies (parrottFiniteImageEquiv.symm (parrottFiniteImageEquiv _))=_
  rw [MulEquiv.symm_apply_apply,parrottLift_generator]

theorem hom_square (x : Atlas1600Group) : hom (hom x)=squareElement*x*squareElement⁻¹ := by
  have h : (hom.comp hom).comp parrottFiniteImageEquiv.toMonoidHom =
      (MulAut.conj squareElement).toMonoidHom.comp parrottFiniteImageEquiv.toMonoidHom := by
    apply PresentedGroup.ext
    intro i
    change hom (hom (parrottFiniteImageEquiv (parrottGenerator i)))=
      squareElement*parrottFiniteImageEquiv (parrottGenerator i)*squareElement⁻¹
    rw [parrottFiniteImageEquiv_generator,hom_generator,assignment,map_eval]
    simp only [hom_generator]
    exact square_certificate i
  obtain ⟨y,rfl⟩ := parrottFiniteImageEquiv.surjective x
  exact congrArg (fun f : ParrottGroup →* Atlas1600Group => f y) h

theorem hom_injective : Function.Injective hom := by
  intro x y he
  apply (MulAut.conj squareElement).injective
  exact (hom_square x).symm.trans ((congrArg hom he).trans (hom_square y))

def automorphism : MulAut Atlas1600Group :=
  MulEquiv.ofBijective hom ⟨hom_injective,Finite.surjective_of_injective hom_injective⟩

@[simp] theorem automorphism_apply (x : Atlas1600Group) : automorphism x=hom x := rfl

theorem automorphism_square : automorphism^2=MulAut.conj squareElement := by
  ext x
  exact hom_square x

theorem hom_coreGen (i : Fin 2) : hom (coreGen i)=eval coreGen (actionWord i) := by
  rw [← coreWord_eq,map_eval]
  simp only [hom_generator]
  exact action_certificate i

theorem coreGen_mem (i : Fin 2) : coreGen i∈max4 := by
  fin_cases i
  · exact Max4Projective.sourceGen_mem 0
  · exact Max4Projective.sourceGen_mem 1

theorem eval_core_mem (w : List (Fin 2 × Bool)) : eval coreGen w∈max4 := by
  induction w with
  | nil => exact max4.one_mem
  | cons a w ih =>
    rcases a with ⟨i,b⟩
    cases b
    · exact max4.mul_mem (max4.inv_mem (coreGen_mem i)) ih
    · exact max4.mul_mem (coreGen_mem i) ih

theorem automorphism_preserves : max4.map automorphism.toMonoidHom=max4 := by
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap,max4]
    apply (closure_le _).mpr
    rintro x (hx|hx)
    · subst x
      change hom (coreGen 0)∈max4
      rw [hom_coreGen]
      exact eval_core_mem _
    · have he : x=max4Generators.2 := hx
      subst x
      change hom (coreGen 1)∈max4
      rw [hom_coreGen]
      exact eval_core_mem _
  · rw [card_map_of_injective (f := automorphism.toMonoidHom) automorphism.injective]

theorem conj_injective : Function.Injective (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group) := by
  intro x y he
  apply atlasEmbedding_injective
  apply atlasAutEquiv.injective
  simpa only [atlasAutEquiv_embedding] using he

theorem automorphism_order : orderOf automorphism=8 := by
  have hp : automorphism^8=1 := by
    rw [show 8=2*4 from rfl,pow_mul,automorphism_square,← map_pow,square_four,map_one]
  have hn : automorphism^4≠1 := by
    intro he
    have he' : MulAut.conj (squareElement^2)=MulAut.conj (1 : Atlas1600Group) := by
      rw [map_pow,← automorphism_square,← pow_mul]
      simpa using he
    exact square_sq_ne (conj_injective he')
  exact orderOf_eq_prime_pow (p := 2) (n := 2) hn hp

theorem reflection_order : orderOf reflection=2 :=
  (orderOf_eq_prime_iff).mpr ⟨reflection_square,reflection_ne⟩

theorem hom_reflection : hom reflection=reflection*squareElement := by
  change hom (eval coreGen reflectionWord)=_
  rw [map_eval]
  simp only [hom_coreGen]
  exact reflection_image_certificate

theorem semidihedral_relation :
    MulAut.conj reflection*automorphism*(MulAut.conj reflection)⁻¹=automorphism^3 := by
  have hr : reflection⁻¹=reflection := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using reflection_square)
  have hmul : reflection*hom reflection=squareElement := by
    rw [hom_reflection,← mul_assoc,← pow_two,reflection_square,one_mul]
  ext x
  change reflection*hom (reflection⁻¹*x*reflection)*reflection⁻¹=
    hom (hom (hom x))
  have hi : (hom reflection)⁻¹=hom reflection := by rw [← map_inv,hr]
  rw [map_mul,map_mul,map_inv,hom_square,← hmul]
  simp only [mul_inv_rev,hi,hr]
  group

end Tits.Max4Outer
