module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterGenerators
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.FirstImageCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.SecondImageCertificate

/-!
# Exhausting the automorphisms of the actual second Tits core

The Frattini restrictions and fourth-power relations place the image of s3
among 384 checked words. After undoing that word, the remaining automorphism
fixes s3; its s7 image is one of 64 checked words. Two-generator
extensionality identifies the automorphism, and injectivity of the certified
indices gives the exact order 24576. The carrier throughout is the literal
normal two-core of the second parabolic. `OuterQuotient` consumes this count
and exhaustion to construct its quotient by actual inner automorphisms.

Source and marking: Parrott (1972), §5, p.683; see `CoreGenerators`.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.SecondCoreAction
namespace AutomorphismExhaustion
open CoreGenerators OuterGenerators

/-- A sixth, identity letter pads the certified words. -/
def letterAut (i : Fin 6) : MulAut Core :=
  if h : i.val < 5 then candidateAut ⟨i.val,h⟩ else 1

def step (i : Fin 6) (n : Fin 1024) : Fin 1024 :=
  if h : i.val < 5 then CoreAutomorphismCertificate.image ⟨i.val,h⟩ n else n

theorem letterAut_normalForm (i : Fin 6) (n : Fin 1024) :
    letterAut i (coreNormalForm n) = coreNormalForm (step i n) := by
  unfold letterAut step
  split
  · exact candidateAut_normalForm _ _
  · rfl

def wordAut : List (Fin 6) → MulAut Core
  | [] => 1
  | i :: w => wordAut w * letterAut i

def wordIndex (w : List (Fin 6)) (n : Fin 1024) : Fin 1024 :=
  w.foldl (fun x i => step i x) n

theorem wordAut_normalForm (w : List (Fin 6)) (n : Fin 1024) :
    wordAut w (coreNormalForm n) = coreNormalForm (wordIndex w n) := by
  induction w generalizing n with
  | nil => rfl
  | cons i w ih =>
    change wordAut w (letterAut i (coreNormalForm n)) = _
    rw [letterAut_normalForm,ih]
    rfl

def firstRep (j : Fin 384) : MulAut Core :=
  wordAut ((List.finRange 12).map (FirstImageCertificate.letter j))

def secondRep (j : Fin 64) : MulAut Core :=
  wordAut ((List.finRange 12).map (SecondImageCertificate.letter j))

theorem firstRep_first (j : Fin 384) :
    firstRep j (generator 2) = coreNormalForm (FirstImageCertificate.indices j) := by
  change wordAut _ (coreNormalForm 4) = _
  rw [wordAut_normalForm]
  have h := FirstImageCertificate.word_images j
  simpa only [wordIndex,List.foldl_map,FirstImageCertificate.evaluate,
    FirstImageCertificate.step,step] using congrArg coreNormalForm h

theorem secondRep_first (j : Fin 64) : secondRep j (generator 2) = generator 2 := by
  change wordAut _ (coreNormalForm 4) = coreNormalForm 4
  rw [wordAut_normalForm]
  have h := (SecondImageCertificate.word_images j).1
  simpa only [wordIndex,List.foldl_map,SecondImageCertificate.evaluate,
    SecondImageCertificate.step,step] using congrArg coreNormalForm h

theorem secondRep_second (j : Fin 64) :
    secondRep j (generator 6) = coreNormalForm (SecondImageCertificate.indices j) := by
  change wordAut _ (coreNormalForm 256) = _
  rw [wordAut_normalForm]
  have h := (SecondImageCertificate.word_images j).2
  simpa only [wordIndex,List.foldl_map,SecondImageCertificate.evaluate,
    SecondImageCertificate.step,step] using congrArg coreNormalForm h

private theorem perm_normalForm (n : Fin 1024) :
    perm (coreNormalForm n) = CoreAutomorphismCertificate.form n := by
  change AmalgamRigidity.SecondExtension.perm (coreNormalForm n : second) = _
  rw [coreNormalForm_val,AmalgamRigidity.SecondExtension.map_word]
  unfold CoreAutomorphismCertificate.form
  congr 1
  exact funext AmalgamRigidity.SecondExtension.perm_gen

private theorem perm_first : perm (generator 2) = AmalgamRigidity.SecondExtension.packedGen 3 :=
  perm_generator 2
private theorem perm_second : perm (generator 6) = AmalgamRigidity.SecondExtension.packedGen 7 :=
  perm_generator 6

private theorem relations : (generator 2)^4=1 ∧ (generator 6)^4=1 ∧
    (generator 2 * generator 6)^4=1 ∧
    generator 2 * generatorWord (generator 2) (generator 6) 0 =
      generatorWord (generator 2) (generator 6) 0 * generator 2 := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply eq_of_points
    all_goals
      simp only [map_mul,map_pow,map_one,map_generatorWord,perm_generator]
      decide +kernel

/-- Every actual first image occurs among the certified 384 representatives. -/
theorem first_image (a : MulAut Core) :
    ∃ j : Fin 384, a (generator 2) = firstRep j (generator 2) := by
  obtain ⟨n,hn⟩ := coreNormalForm_bijective.2 (a (generator 2))
  have hp : (CoreAutomorphismCertificate.form n ^ 4) 0 = 0 := by
    have h : coreNormalForm n ^ 4 = 1 := by
      rw [hn,← map_pow,relations.1,map_one]
    have h' := congrArg (fun x : Core => perm x 0) h
    simpa only [map_pow,map_one,Equiv.Perm.one_apply,perm_normalForm] using h'
  have hpar := first_image_parity a n hn.symm
  rcases FirstImageCertificate.first_candidates n with h | h | h
  · exact (h hp).elim
  · exact (hpar.elim (fun k => k h.1) (fun k => k h.2)).elim
  · exact ⟨FirstImageCertificate.decode n,by rw [firstRep_first,h,hn]⟩

/-- An actual automorphism fixing the first generator is one of 64 words. -/
theorem stabilizer_exhaustion (a : MulAut Core) (ha : a (generator 2) = generator 2) :
    ∃ j : Fin 64, a = secondRep j := by
  obtain ⟨n,hn⟩ := coreNormalForm_bijective.2 (a (generator 6))
  have hy : (CoreAutomorphismCertificate.form n ^ 4) 0 = 0 := by
    have h : coreNormalForm n ^ 4 = 1 := by
      rw [hn,← map_pow,relations.2.1,map_one]
    simpa only [map_pow,map_one,Equiv.Perm.one_apply,perm_normalForm] using
      congrArg (fun x : Core => perm x 0) h
  have hxy : ((AmalgamRigidity.SecondExtension.packedGen 3 *
      CoreAutomorphismCertificate.form n)^4) 0 = 0 := by
    have h : (generator 2 * coreNormalForm n)^4=1 := by
      rw [hn,← ha,← map_mul,← map_pow,relations.2.2.1,map_one]
    simpa only [map_pow,map_one,Equiv.Perm.one_apply,map_mul,perm_normalForm,perm_first,perm_second] using
      congrArg (fun x : Core => perm x 0) h
  have hcomm :
      (AmalgamRigidity.SecondExtension.packedGen 3 *
        generatorWord (AmalgamRigidity.SecondExtension.packedGen 3)
          (CoreAutomorphismCertificate.form n) 0) 0 =
      (generatorWord (AmalgamRigidity.SecondExtension.packedGen 3)
        (CoreAutomorphismCertificate.form n) 0 *
          AmalgamRigidity.SecondExtension.packedGen 3) 0 := by
    have h := congrArg a.toMonoidHom relations.2.2.2
    simp only [map_mul,map_generatorWord] at h
    have h : generator 2 * generatorWord (generator 2) (coreNormalForm n) 0 =
        generatorWord (generator 2) (coreNormalForm n) 0 * generator 2 := by
      simpa only [MulEquiv.coe_toMonoidHom,ha,← hn] using h
    simpa only [map_mul,map_generatorWord,perm_normalForm,perm_first,perm_second] using
      congrArg (fun x : Core => perm x 0) h
  have hpar := second_image_parity a ha n hn.symm
  rcases SecondImageCertificate.second_candidates n with h | h | h | h | h
  · exact (hpar h).elim
  · exact (h hy).elim
  · exact (h hxy).elim
  · exact (h hcomm).elim
  · refine ⟨SecondImageCertificate.decode n,aut_ext a _ ?_ ?_⟩
    · rw [ha,secondRep_first]
    · rw [secondRep_second,h,hn]

/-- A concrete 384-by-64 family exhausts the actual automorphism group. -/
theorem exhaustion (a : MulAut Core) :
    ∃ (i : Fin 384) (j : Fin 64), a = firstRep i * secondRep j := by
  obtain ⟨i,hi⟩ := first_image a
  have hfix : ((firstRep i)⁻¹ * a) (generator 2) = generator 2 := by
    change (firstRep i).symm (a (generator 2)) = generator 2
    rw [hi,MulEquiv.symm_apply_apply]
  obtain ⟨j,hj⟩ := stabilizer_exhaustion ((firstRep i)⁻¹ * a) hfix
  exact ⟨i,j,by rw [← hj,mul_inv_cancel_left]⟩


private theorem first_decode : ∀ j : Fin 384,
    FirstImageCertificate.decode (FirstImageCertificate.indices j) = j := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem second_decode : ∀ j : Fin 64,
    SecondImageCertificate.decode (SecondImageCertificate.indices j) = j := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

def enumerate (ij : Fin 384 × Fin 64) : MulAut Core := firstRep ij.1 * secondRep ij.2

theorem enumerate_bijective : Function.Bijective enumerate := by
  constructor
  · rintro ⟨i,j⟩ ⟨k,l⟩ he
    have hx := congrArg (fun a : MulAut Core => a (generator 2)) he
    change firstRep i (secondRep j (generator 2)) = firstRep k (secondRep l (generator 2)) at hx
    rw [secondRep_first,secondRep_first,firstRep_first,firstRep_first] at hx
    have hik := (Function.LeftInverse.injective first_decode) (coreNormalForm_bijective.1 hx)
    subst k
    have hjl : secondRep j = secondRep l := mul_left_cancel he
    have hy := congrArg (fun a : MulAut Core => a (generator 6)) hjl
    rw [secondRep_second,secondRep_second] at hy
    have hjl := (Function.LeftInverse.injective second_decode) (coreNormalForm_bijective.1 hy)
    subst l
    rfl
  · intro a
    obtain ⟨i,j,h⟩ := exhaustion a
    exact ⟨(i,j),h.symm⟩

/-- Exact size of the automorphism group on the literal core. -/
theorem automorphism_card : Nat.card (MulAut Core) = 24576 := by
  have h := (Nat.card_congr (Equiv.ofBijective enumerate enumerate_bijective)).symm
  simpa using h

end AutomorphismExhaustion
end Tits.ExceptionalParabolics.SecondCoreAction

