module
public import Theory.Representation.PSL3Two.WholeMovedBound
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.OtherFactor

/-!
# A sharp natural tensor exhausts the whole moved module

The two natural markings give a chief section of dimension nine. The
original four-group actor contains an involution with displacement at most
three. The three-involution bound limits the whole K-moved module to nine
dimensions. Because the chief section is supported inside that module,
its denominator is zero and its upper subspace is the whole moved module.
The original quotient projection is an intertwining isomorphism; composing
it with the existing coordinates retains the same natural tensor marking.

Source: Aschbacher--Smith 13.1.9, printed p.871, the deduction [D,K̂] = W.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace Representation.CommonChief
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {S K A : Subgroup Q}
  {support : Submodule (ZMod 2) V} {c : Data ρ S K A support}
  {hc : ⁅S,K ⊔ A⁆ = ⊥} {t : c.NaturalTensor hc}

/-- The literal common chief section has dimension nine under the two
natural markings. -/
theorem Data.NaturalTensor.OtherNatural.section_finrank (o : t.OtherNatural) :
    Module.finrank (ZMod 2) (c.upper.toSubmodule ⧸
      (sectionLower (ρ.comp (actorGroup S K A).subtype) c.lower c.upper).toSubmodule) = 9 := by
  have hi : Module.finrank (ZMod 2) t.tensor.constituent.toSubmodule = 3 :=
    o.coordinates.finrank_eq.trans (by simp)
  have he := t.tensor.coordinates.toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct,hi] at he
  simpa only [Module.finrank_fin_fun,Module.finrank_self,mul_one] using he

/-- A sharp actor exhausts the entire moved module. The three-involution
bound leaves no room for a denominator below its nine-dimensional tensor. -/
theorem Data.NaturalTensor.OtherNatural.whole_moved (o : t.OtherNatural)
    (hAK : A ≤ K) (he : IsElementaryAbelian 2 A) (hne : A ≠ ⊥)
    (hcod : fixedCodim ρ A ≤ 3)
    (hsupport : support ≤ subspaceCommutator ρ ⊤ K) :
    c.lower = ⊥ ∧ c.upper.toSubmodule = subspaceCommutator ρ ⊤ K ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) = 9 := by
  let := he
  obtain ⟨a,hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let aK : K := ⟨a,hAK a.property⟩
  have ha2 : aK ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : Q) a.property)
  have haneK : aK ≠ 1 := fun hz => hane (Subtype.ext (congrArg (fun x : K => (x : Q)) hz))
  have hb := BinaryLinearThree.moved_finrank_le_three_mul_fixedCodim ρ K o.second aK ha2 haneK
  have hcod' : fixedCodim ρ (zpowers (a : Q)) ≤ 3 :=
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr a.property)).trans hcod
  have hbound : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) ≤ 9 :=
    hb.trans (by change 3 * fixedCodim ρ (zpowers (a : Q)) ≤ 9; omega)
  have hU : c.upper.toSubmodule ≤ subspaceCommutator ρ ⊤ K := c.upper_le_support.trans hsupport
  have hdimU := Submodule.finrank_mono hU
  have hdim := (sectionLower (ρ.comp (actorGroup S K A).subtype) c.lower c.upper).toSubmodule.finrank_quotient_add_finrank
  have heq := (sectionLowerEquiv (ρ.comp (actorGroup S K A).subtype) c.lower_le_upper).finrank_eq
  rw [o.section_finrank,heq] at hdim
  have hzero : Module.finrank (ZMod 2) c.lower.toSubmodule = 0 := by
    omega
  refine ⟨?_,Submodule.eq_of_le_of_finrank_eq hU (by omega),by omega⟩
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.finrank_eq_zero.mp hzero

/-- The original quotient projection is an equivariant isomorphism once
the sharp dimension argument has killed its denominator. -/
@[expose] def Data.wholeSectionEquiv (hz : c.lower = ⊥) :
    c.upper.toRepresentation.Equiv
      (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper) := by
  let U := (sectionLower (ρ.comp (actorGroup S K A).subtype) c.lower c.upper).toSubmodule
  let p : c.upper.toRepresentation.IntertwiningMap
      (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper) :=
    .mk U.mkQ (by intro g; ext v; rfl)
  apply p.ofBijective
  refine ⟨?_,U.mkQ_surjective⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Subtype.ext
  have hvlow : (v : V) ∈ c.lower.toSubmodule := (Submodule.Quotient.mk_eq_zero U).mp hv
  rw [hz] at hvlow
  exact hvlow

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem Data.wholeSectionEquiv_apply (hz : c.lower = ⊥) (v : c.upper.toSubmodule) :
    c.wholeSectionEquiv hz v =
      (sectionLower (ρ.comp (actorGroup S K A).subtype) c.lower c.upper).toSubmodule.mkQ v := rfl


open QuadraticFourGroup.TensorClassification
/-- The same tensor coordinates now act on the whole upper module, through
the original quotient projection and the original commuting-product map. -/
def Data.NaturalTensor.wholeTensorEquiv (t : c.NaturalTensor hc) (hz : c.lower = ⊥) :
    Representation.Equiv (c.upper.toRepresentation.comp (commutingProduct S (K ⊔ A) hc))
      (externalTensor t.tensor.constituent.toRepresentation t.tensor.multiplicity) := by
  let p : Representation.Equiv (c.upper.toRepresentation.comp (commutingProduct S (K ⊔ A) hc))
      (c.productRepresentation hc) :=
    .mk (c.wholeSectionEquiv hz).toLinearEquiv (by
      intro g
      exact (c.wholeSectionEquiv hz).isIntertwining' (commutingProduct S (K ⊔ A) hc g))
  exact p.trans t.tensor.coordinates

omit [FiniteDimensional (ZMod 2) V] in
/-- Zero denominator promotes the chief section's irreducibility to the
whole upper module with its unchanged actor-group action. -/
theorem Data.whole_irreducible (hz : c.lower = ⊥) : IsIrreducible c.upper.toRepresentation :=
  (RepEquiv.irreducible_euqiv
    ({ toLinearEquiv := (c.wholeSectionEquiv hz).toLinearEquiv
       isIntertwining' := (c.wholeSectionEquiv hz).isIntertwining' } :
      RepEquiv c.upper.toRepresentation
        (sectionRepresentation (ρ.comp (actorGroup S K A).subtype) c.lower c.upper))).mpr c.irreducible

end Representation.CommonChief
