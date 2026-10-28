module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Odd.Representatives

/-!
# Exact parameters of the odd short family

Specializing the triality multiplication law at the central all-ones Parker
loop element removes both the associator and half-overlap corrections. Thus
`r(x,d Omega) = r(x,d)` in the actual extraspecial group. The Parker sign gives
the other central lift. Conversely, the minimal Leech class recovers the unique
coordinate of magnitude three and the normalized Golay word. The two possible
codewords and two loop signs then give exactly these parameter identifications;
the nontrivial central involution distinguishes the signs.

Together with the re-exported `odd_iff`, `rOdd_tensor`, and `rOdd_correction`,
this constructs and exhausts the source family with its specified representative.
Equality of group lifts is proved from triality identities, not inferred from
equality of lattice classes.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8(3), printed p. 150
(PDF page 81, left), and the triality multiplication formula of Lemma 14.2(7).
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

private theorem odd_psiAut_one : psiAut1N 1 = 1 := by
  apply Subtype.ext
  change psiAut1 (1 : ParkerStandardGroup).val = 1
  simp only [psiAut1, Subgroup.coe_one, Equiv.Perm.one_apply, ↓reduceIte]
  ext ⟨a,b,c⟩ : 1
  cases a <;> cases b <;> cases c <;> rfl

private theorem odd_psi3_one : psi3N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi3 loopOne (a,b,c) = (a,b,c)
  simp

/-- Specializing the actual triality multiplication law at the central loop word. -/
theorem loopImage_mul_omega (d : ParkerLoop) :
    loopImage (parkerLoopMultiply d parkerOmega) = loopImage d * loopImage parkerOmega := by
  have ha : associatorAutomorphism d.1 golayOne = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rw [associatorAutomorphism_apply]
    have ht : parkerTripleIntersection d.1 golayOne a.1 = 0 := by
      rw [parkerTripleIntersection_cycle,parkerTripleIntersection_cycle,parkerTripleIntersection_one]
    simp [ht]
  have hh := psi1N_mul_collection parkerOmega d
  change psi1N d * psi1N parkerOmega = psiAut1N (associatorAutomorphism d.1 golayOne) *
    psi3N (0,golayHalfOverlap d.1 golayOne) * psi1N (parkerLoopMultiply parkerOmega d) at hh
  rw [ha,odd_psiAut_one,golayHalfOverlap_symmetric,golayHalfOverlap_one] at hh
  change _ = 1 * psi3N loopOne * _ at hh
  rw [odd_psi3_one,one_mul,one_mul,parkerOmega_commutes] at hh
  apply Subtype.ext
  simp only [Subgroup.coe_mul,loopImage_val,← map_mul,hh]

theorem loopImage_omega_sq : loopImage parkerOmega ^ 2 = 1 := by
  rw [pow_two,← loopImage_mul_omega,parkerOmega_square]
  apply Subtype.ext
  rw [loopImage_val]
  change nQuotientMap (psi1N loopOne) = 1
  rw [TrialityGeneratorCalculation.psi1_one,map_one]

@[simp] theorem oddCode_mul_omega (x : Omega) (d : ParkerLoop) :
    oddCode x (parkerLoopMultiply d parkerOmega) = oddCode x d := by
  apply Subtype.ext
  funext i
  change (d.1 + golayOne).val i + (d.1 + golayOne).val x * golayOne.val i = _
  simp only [oddCode,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,golayOne,allOnes,mul_one]
  change d.1.val i + 1 + (d.1.val x + 1) = d.1.val i + d.1.val x
  ring_nf
  simp

@[simp] theorem oddRepresentative_mul_omega (x : Omega) (d : ParkerLoop) :
    oddRepresentative x (parkerLoopMultiply d parkerOmega) = oddRepresentative x d := by
  simp only [oddRepresentative,oddCode_mul_omega]

/-- Multiplication by the all-ones loop element leaves the actual source word fixed. -/
theorem rOddElement_mul_omega (x : Omega) (d : ParkerLoop) :
    rOddElement x (parkerLoopMultiply d parkerOmega) = rOddElement x d := by
  simp only [rOddElement,loopImage_mul_omega]
  have he : (parkerLoopMultiply d parkerOmega).1.val x = d.1.val x + 1 := rfl
  rw [he]
  rcases bit_cases (d.1.val x) with h | h
  · rw [h,zero_add]
    change (loopImage d * loopImage parkerOmega) * loopImage parkerOmega ^ 1 * _ =
      loopImage d * loopImage parkerOmega ^ 0 * _
    rw [pow_one,pow_zero,mul_one,mul_assoc (loopImage d),← pow_two,loopImage_omega_sq,mul_one]
  · rw [h,CharTwo.add_self_eq_zero]
    change (loopImage d * loopImage parkerOmega) * loopImage parkerOmega ^ 0 * _ =
      loopImage d * loopImage parkerOmega ^ 1 * _
    rw [pow_one,pow_zero,mul_one]

theorem rOdd_mul_omega (x : Omega) (d : ParkerLoop) :
    rOdd x (parkerLoopMultiply d parkerOmega) = rOdd x d :=
  Subtype.ext (rOddElement_mul_omega x d)

private theorem odd_three_support_neg (a : IntegerCoordinates) :
    oddThreeSupport (-a) = oddThreeSupport a := by
  ext i
  simp [oddThreeSupport]

theorem odd_three_support (x : Omega) (d : ParkerLoop) :
    oddThreeSupport (oddRepresentative x d).val = {x} := by
  rw [oddRepresentative_profile]
  rw [odd_three_support_neg,signedOddProfile_three_support _ _ (by simp)]

/-- Minimal reduction recovers the point and the normalized Golay word. -/
theorem rOdd_class_eq_iff (x y : Omega) (d e : ParkerLoop) :
    shortLiftClass sourceLatticeComparison (rOdd x d) =
      shortLiftClass sourceLatticeComparison (rOdd y e) ↔ x = y ∧ oddCode x d = oddCode y e := by
  rw [rOdd_class,rOdd_class,shortReduction_eq_iff]
  constructor
  · intro h
    have hs : oddThreeSupport (oddRepresentative x d).val =
        oddThreeSupport (oddRepresentative y e).val := by
      rcases h with h | h
      · exact congrArg (fun a : leech => oddThreeSupport a.val) h
      · have hh := congrArg (fun a : leech => oddThreeSupport a.val) h
        change oddThreeSupport (oddRepresentative x d).val =
          oddThreeSupport (-(oddRepresentative y e).val) at hh
        rw [odd_three_support_neg] at hh
        exact hh
    rw [odd_three_support,odd_three_support,Finset.singleton_inj] at hs
    subst y
    refine ⟨rfl,?_⟩
    rcases h with h | h
    · have he := congrArg Subtype.val h
      change (oddRepresentative x d).val = (oddRepresentative x e).val at he
      rw [oddRepresentative_profile,oddRepresentative_profile,neg_inj] at he
      exact signedOddProfile_code_injective {x} ∅ he
    · have he := congrArg (fun a : leech => a.val x) h
      change (oddRepresentative x d).val x = -(oddRepresentative x e).val x at he
      simp only [oddRepresentative_at] at he
      omega
  · rintro ⟨rfl,h⟩
    exact Or.inl (by change oddRepresentative x d = oddRepresentative x e; simp [oddRepresentative,h])

private theorem odd_code_eq_iff (x : Omega) (d e : ParkerLoop) :
    oddCode x d = oddCode x e ↔ d.1 = e.1 ∨ d.1 = e.1 + golayOne := by
  constructor
  · intro h
    rcases bit_cases (d.1.val x) with hd | hd <;>
      rcases bit_cases (e.1.val x) with he | he
    · exact Or.inl (by simpa [oddCode,hd,he] using h)
    · exact Or.inr (by simpa [oddCode,hd,he] using h)
    · apply Or.inr
      have hh : d.1 + golayOne = e.1 := by simpa [oddCode,hd,he] using h
      rw [← hh,add_assoc]
      have hz : golayOne + golayOne = 0 := by ext i; simp
      rw [hz,add_zero]
    · exact Or.inl (by simpa [oddCode,hd,he] using h)
  · rintro (h | h)
    · simp [oddCode,h]
    · have hm : (parkerLoopMultiply e parkerOmega).1 = d.1 := h.symm
      have : oddCode x d = oddCode x (parkerLoopMultiply e parkerOmega) := by
        simp only [oddCode,hm]
      exact this.trans (oddCode_mul_omega x e)

private theorem odd_loop_code_eq (d e : ParkerLoop) (h : d.1 = e.1) :
    d = e ∨ d = parkerSign 1 e := by
  rcases bit_cases d.2 with hd | hd <;> rcases bit_cases e.2 with he | he
  · exact Or.inl (Prod.ext h (hd.trans he.symm))
  · exact Or.inr (Prod.ext h (by simp [parkerSign,hd,he]))
  · exact Or.inr (Prod.ext h (by simp [parkerSign,hd,he]))
  · exact Or.inl (Prod.ext h (hd.trans he.symm))

/-- The only repetition is multiplication of the Parker parameter by `Omega`. -/
theorem rOdd_eq_iff (x y : Omega) (d e : ParkerLoop) :
    rOdd x d = rOdd y e ↔ x = y ∧ (d = e ∨ d = parkerLoopMultiply e parkerOmega) := by
  constructor
  · intro h
    have hc := (rOdd_class_eq_iff x y d e).mp
      (congrArg (shortLiftClass sourceLatticeComparison) h)
    obtain ⟨rfl,hc⟩ := hc
    refine ⟨rfl,?_⟩
    rcases (odd_code_eq_iff x d e).mp hc with hc | hc
    · rcases odd_loop_code_eq d e hc with he | he
      · exact Or.inl he
      · subst d
        rw [rOdd_sign] at h
        exact False.elim ((shortLiftSigns sourceLatticeComparison).fixedPointFree _ h)
    · have hc' : d.1 = (parkerLoopMultiply e parkerOmega).1 := hc
      rcases odd_loop_code_eq d (parkerLoopMultiply e parkerOmega) hc' with he | he
      · exact Or.inr he
      · subst d
        rw [rOdd_sign,rOdd_mul_omega] at h
        exact False.elim ((shortLiftSigns sourceLatticeComparison).fixedPointFree _ h)
  · rintro ⟨rfl,h | h⟩
    · rw [h]
    · rw [h,rOdd_mul_omega]

/-- The opposite central lift has exactly the two negated Parker parameters. -/
theorem rOdd_eq_flip_iff (x y : Omega) (d e : ParkerLoop) :
    rOdd x d = (shortLiftSigns sourceLatticeComparison).flip (rOdd y e) ↔
      x = y ∧ (d = parkerSign 1 e ∨ d = parkerSign 1 (parkerLoopMultiply e parkerOmega)) := by
  rw [← rOdd_sign,rOdd_eq_iff,parkerLoopMultiply_sign_left]

@[simp] theorem oddRepresentative_sign (x : Omega) (s : ParkerBit) (d : ParkerLoop) :
    oddRepresentative x (parkerSign s d) = oddRepresentative x d := rfl

end Sporadic.Monster.Construction.LocalC.ShortFamilies
