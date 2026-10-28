module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PrefixChecks

/-!
# Kernel-checked homomorphisms from the common presentation

Check every adjacent matrix-prefix multiplication and each endpoint. The
unitary relators evaluate to identity; the symplectic relators evaluate to
identity or negative identity, hence vanish in the literal center quotient.
The universal property of a presented group therefore supplies two actual
homomorphisms, with their prescribed values on both generators.

This is a construction step toward PSU₄(2) ≅ PSp₄(3), the comparison used in
Aschbacher–Smith I.1.4(1), printed p.408, and GLS3 §2.2/§2.7. The finite
presentation bound and the matrix-group generation/counting arguments are
separate obligations; relations alone do not establish the comparison.
-/

@[expose] public section
open Matrix Atlas.Algebra
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

theorem unitary_relator (r : Fin 11) :
    FreeGroup.lift unitaryGenerator (relator r) = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h := congrArg unitaryValue (wordValue_eq_range unitaryGenerator (relatorWord r))
  rw [map_list_prod, List.map_map] at h
  change unitaryValue (FreeGroup.lift unitaryGenerator (relator r)) =
    ((List.range (relatorWord r).length).map (unitaryLetter r)).prod at h
  rw [prefixProduct (unitaryLetter r) (unitaryPrefix r) _
    (unitaryPrefix_zero r) (fun k hk => unitaryPrefix_step r
      ⟨k, lt_of_lt_of_le hk (relatorWord_length_le r)⟩), unitaryPrefix_end] at h
  exact h

theorem symplectic_relator_central (r : Fin 11) :
    FreeGroup.lift symplecticGenerator (relator r) ∈ Subgroup.center (Sp (ZMod 3)) := by
  have h := congrArg symplecticValue (wordValue_eq_range symplecticGenerator (relatorWord r))
  rw [map_list_prod, List.map_map] at h
  change symplecticValue (FreeGroup.lift symplecticGenerator (relator r)) =
    ((List.range (relatorWord r).length).map (symplecticLetter r)).prod at h
  rw [prefixProduct (symplecticLetter r) (symplecticPrefix r) _
    (symplecticPrefix_zero r) (fun k hk => symplecticPrefix_step r
      ⟨k, lt_of_lt_of_le hk (relatorWord_length_le r)⟩)] at h
  rw [mem_center_iff]
  rcases symplecticPrefix_end r with he | he
  · exact Or.inl (Subtype.ext (h.trans he))
  · right
    apply Matrix.PSp4Three.ext_action
    intro x
    change symplecticValue (FreeGroup.lift symplecticGenerator (relator r)) *ᵥ x = _
    rw [h, he, Matrix.neg_mulVec, Matrix.one_mulVec, negIdentity_smul]

def projectiveGenerator (i : Fin 2) : PSp (ZMod 3) :=
  QuotientGroup.mk' _ (symplecticGenerator i)

theorem projective_relator (r : Fin 11) :
    FreeGroup.lift projectiveGenerator (relator r) = 1 := by
  have h : FreeGroup.lift projectiveGenerator =
      (QuotientGroup.mk' (Subgroup.center (Sp (ZMod 3)))).comp
        (FreeGroup.lift symplecticGenerator) := by
    apply FreeGroup.ext_hom
    intro i
    simp [projectiveGenerator]
  rw [h, MonoidHom.comp_apply]
  exact (QuotientGroup.eq_one_iff _).mpr (symplectic_relator_central r)

/-- The homomorphism sending the two presented generators to the checked
special unitary matrices. Its bijectivity is not assumed. -/
def toSpecial : Presentation →* StandardSU :=
  PresentedGroup.toGroup (f := unitaryGenerator) (by rintro _ ⟨r, rfl⟩; exact unitary_relator r)

/-- The homomorphism to the literal symplectic center quotient. -/
def toProjectiveSymplectic : Presentation →* PSp (ZMod 3) :=
  PresentedGroup.toGroup (f := projectiveGenerator) (by rintro _ ⟨r, rfl⟩; exact projective_relator r)

@[simp] theorem toSpecial_generator (i : Fin 2) :
    toSpecial (PresentedGroup.of i) = unitaryGenerator i := PresentedGroup.toGroup.of _

@[simp] theorem toProjectiveSymplectic_generator (i : Fin 2) :
    toProjectiveSymplectic (PresentedGroup.of i) = projectiveGenerator i :=
  PresentedGroup.toGroup.of _

theorem toSpecial_generator_zero_ne_one : toSpecial (PresentedGroup.of 0) ≠ 1 := by
  rw [toSpecial_generator]
  intro h
  have he := congrArg (fun g : StandardSU => g.val.val 0 0) h
  exact (by decide +kernel : omega ≠ 1) he

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
