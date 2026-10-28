module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.AutomizerData
public import Theory.ElementaryAbelian.Basic

/-!
# The elementary normal subgroup in Case IV

F = C_T(d) is elementary of order sixteen, normal and self-centralizing in T.
The quotient T/F is elementary of order eight. The basis z₁,z₃,a,d identifies
F with binary four-space; literal right conjugation by z₂,z₄,b gives precisely
the three generators in `AutomizerData`. Thus the finite normalizer problem
uses the actual local action, with the original source conventions.

Source: Janko, A characterization of the Mathieu simple groups, I,
J. Algebra 9 (1968), Section 1, printed p.3.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
open Subgroup
open scoped IsMulCommutative

private theorem elementary_of_square {A : Type*} [Group A]
    (h : ∀ x : A, x ^ 2 = 1) : IsElementaryAbelian 2 A where
  is_comm.comm x y := (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (h x)) x y).eq
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h

public theorem F_elementary : IsElementaryAbelian 2 F := by
  apply elementary_of_square
  have h : ∀ x : F, (x : Model)^2=1 := by decide +kernel
  exact fun x => Subtype.ext (h x)

public theorem F_generators : z 0 ∈ F ∧ z 2 ∈ F ∧ a ∈ F ∧ d ∈ F := by decide +kernel

public theorem F_centralizer : centralizer (F : Set Model) = F := by
  apply le_antisymm
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx d F_generators.2.2.2).symm
  · let := F_elementary
    exact le_centralizer F

public instance F_normal : F.Normal where
  conj_mem n hn g := by
    let := F_elementary
    have hgd : g⁻¹*d*g ∈ F := by
      have h : ∀ x : Model, x⁻¹*d*x ∈ F := by decide +kernel
      exact h g
    have hc : Commute n (g⁻¹*d*g) := setLike_mul_comm hn hgd
    apply mem_centralizer_singleton_iff.mpr
    simpa [MulAut.conj_apply, mul_assoc] using
      (hc.map (MulAut.conj g)).eq

@[expose] public def fWord (v : BinaryFour) : Model :=
  z 0 ^ (v.toAdd 0).val * z 2 ^ (v.toAdd 1).val *
    a ^ (v.toAdd 2).val * d ^ (v.toAdd 3).val

private theorem fWord_mem : ∀ v, fWord v ∈ F := by decide +kernel

private def fHom : BinaryFour →* F where
  toFun v := ⟨fWord v, fWord_mem v⟩
  map_one' := by apply Subtype.ext; decide +kernel
  map_mul' := by
    have h : ∀ v w, fWord (v*w) = fWord v * fWord w := by decide +kernel
    exact fun v w => Subtype.ext (h v w)

public noncomputable def fBasis : BinaryFour ≃* F :=
  MulEquiv.ofBijective fHom
    ⟨by
      intro v w h
      have hh : Function.Injective fWord := by decide +kernel
      exact hh (congrArg Subtype.val h), by
      intro x
      have hh : ∀ x : F, ∃ v, fWord v = (x : Model) := by decide +kernel
      obtain ⟨v,hv⟩ := hh x
      exact ⟨v,Subtype.ext hv⟩⟩

public theorem fBasis_apply (v : BinaryFour) : (fBasis v : Model) = fWord v := by rfl

public theorem fBasis_point : (fBasis automizerPoint : Model) = z 0 := by
  change fWord automizerPoint = z 0
  decide +kernel

@[expose] public def fConjugator (i : Fin 3) : Model := ![z 1, z 3, b] i

-- Literal right conjugation in the source convention.
public theorem f_conjugation : ∀ i v,
    (fConjugator i)⁻¹ * fWord v * fConjugator i =
      fWord (automizerGenerator i v) := by decide +kernel

public theorem quotient_elementary : IsElementaryAbelian 2 (Model ⧸ F) := by
  apply elementary_of_square
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change (QuotientGroup.mk' F) x ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have h : ∀ x : Model, x^2 ∈ F := by decide +kernel
    exact h x

public theorem quotient_card : Nat.card (Model ⧸ F) = 8 := by
  change F.index = 8
  have h := F.index_mul_card
  rw [F_card, model_card] at h
  omega

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
