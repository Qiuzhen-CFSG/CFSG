module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.KernelComparison
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.DerivedInvolution
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Canonical comparisons for the E.2.2 models

For odd f, 2^f is two modulo three, so the scalar center of SL₃(2^f)
is trivial. Its actual projective projection is therefore an isomorphism.
For f > 1, the simple characteristic-two symplectic group contains an
explicit nonidentity commutator, so its derived subgroup is the whole group;
the resulting comparison is the subgroup inclusion. Both maps preserve
every specified subgroup image, in particular the Borel used in E.2.2.

Central quotient transport also connects the actual faithful action image
to a specified component model. This uses the parent's central-kernel
theorem and never asserts that a representation's kernel is trivial.

Source: Aschbacher--Smith, E.2.2, printed pp.215--216, and the odd-exponent
specialization in the proof of 15.3.65, printed p.1152.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

open Subgroup Matrix
open scoped MatrixGroups

variable {D E : Type*} [Group D] [Group E]

/-- A specified model isomorphism induces its canonical central-quotient map. -/
def centralQuotientCongr (e : D ≃* E) : D ⧸ center D ≃* E ⧸ center E :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

@[simp] theorem centralQuotientCongr_mk (e : D ≃* E) (g : D) :
    centralQuotientCongr e (QuotientGroup.mk g) = QuotientGroup.mk (e g) := rfl

/-- Restrict the same map to the actual commutator subgroups. -/
def derivedCongr (e : D ≃* E) : commutator D ≃* commutator E :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl))

@[simp] theorem derivedCongr_apply (e : D ≃* E) (g : commutator D) :
    (derivedCongr e g : E) = e g := rfl

/-- The central quotient of the actual nontrivial action image is the model's
central quotient, even for an action with nontrivial central kernel. -/
def actionImageModelCentralQuotientEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (e : D ≃* E) :
    Representation.BinaryOffender.actionImage ρ ⧸
        center (Representation.BinaryOffender.actionImage ρ) ≃* E ⧸ center E :=
  (actionImageCentralQuotientEquiv ρ hn).symm.trans (centralQuotientCongr e)

/-- Catalogue comparisons of section images reduce to the specified model,
without making a stronger kernel assertion. -/
theorem componentModel_actionImage_iff
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (e : D ≃* E) (family : Family) (q : ℕ) :
    ComponentModel (Representation.BinaryOffender.actionImage ρ ⧸
      center (Representation.BinaryOffender.actionImage ρ)) family q ↔
        ComponentModel (E ⧸ center E) family q := by
  let a := actionImageModelCentralQuotientEquiv ρ hn e
  exact ⟨fun h => h.transport a.symm, fun h => h.transport a⟩

/-- A genuine perfect central covering preserves the catalogue comparison.
The input supplies the map, its surjectivity and its central kernel. -/
theorem componentModel_centralCover_iff (π : PerfectCentralCovering.Cover D E)
    (family : Family) (q : ℕ) :
    ComponentModel (D ⧸ center D) family q ↔ ComponentModel (E ⧸ center E) family q :=
  ⟨fun h => h.transport π.quotientCenterEquiv.symm,
    fun h => h.transport π.quotientCenterEquiv⟩

/-- In particular the exceptional central cover of A₆ contributes the
alternating-six entry through its actual covering map. -/
theorem alternatingSixCover_componentModel
    (π : PerfectCentralCovering.Cover D (alternatingGroup (Fin 6))) :
    ComponentModel (D ⧸ center D) .alternatingSix 0 := by
  let a : (alternatingGroup (Fin 6) ⧸ center (alternatingGroup (Fin 6))) ≃*
      alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)))).trans
        QuotientGroup.quotientBot
  exact .alternatingSix (π.quotientCenterEquiv.trans a)

variable {F : Type*} [Field F] [Finite F] {f : ℕ}

/-- The odd field exponent eliminates the degree-three scalar center. -/
theorem slThree_center_eq_bot (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    center SL(3, F) = ⊥ := by
  apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr
  rw [hF]
  obtain ⟨k, rfl⟩ := hf
  have hfour : 4 ^ k % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ k) 1
    simpa only [one_pow] using (show Nat.ModEq 3 4 1 by decide).pow k
  rw [pow_succ, pow_mul, Nat.mul_mod]
  norm_num only [Nat.reducePow] at *
  rw [hfour]
  decide

/-- The SL₃/PSL₃ comparison at odd exponent is the actual projection. -/
def slThreeEquivProjective (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    SL(3, F) ≃* PSL(3, F) :=
  Matrix.SL3.equivProjectiveOfCenterEqBot F (slThree_center_eq_bot hF hf)

@[simp] theorem slThreeEquivProjective_apply
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) (g : SL(3, F)) :
    slThreeEquivProjective hF hf g = Matrix.PSL3.projection F g :=
  Matrix.SL3.equivProjectiveOfCenterEqBot_apply F (slThree_center_eq_bot hF hf) g

/-- The marked Borel, or any other marked subgroup, keeps the same projection. -/
theorem slThreeEquivProjective_subgroup
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) (A : Subgroup SL(3, F)) :
    A.map (slThreeEquivProjective hF hf).toMonoidHom = A.map (Matrix.PSL3.projection F) := by
  congr 1
  exact MonoidHom.ext (slThreeEquivProjective_apply hF hf)

/-- Above the binary endpoint, the derived symplectic subgroup is the whole
group. Simplicity is used only for this actual matrix carrier. -/
theorem spFour_derived_eq_top (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    commutator (Theory.SpecificGroups.SymplecticFour.Sp F) = ⊤ := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let : IsSimpleGroup (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F)) :=
    Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup_of_card_eq_two_pow hf hF
  let : IsSimpleGroup (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  rcases (inferInstance : (commutator (Theory.SpecificGroups.SymplecticFour.Sp F)).Normal).eq_bot_or_eq_top
      with h | h
  · obtain ⟨x, hx, _⟩ :=
      Theory.SpecificGroups.SymplecticFour.exists_involution_derived_of_char_two (F := F)
    exact (hx (Subtype.ext (by simpa [h] using x.property))).elim
  · exact h

/-- E.2.2's literal derived carrier maps to Sp₄ by subgroup inclusion. -/
def spFourDerivedEquiv (hF : Nat.card F = 2 ^ f) (hf : 1 < f) :
    BorelReduction.SourceCases.Sp4Derived F ≃* Theory.SpecificGroups.SymplecticFour.Sp F :=
  (MulEquiv.subgroupCongr (spFour_derived_eq_top hF hf)).trans Subgroup.topEquiv

@[simp] theorem spFourDerivedEquiv_apply
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (g : BorelReduction.SourceCases.Sp4Derived F) :
    spFourDerivedEquiv hF hf g = g.val := rfl

/-- Every subgroup of the derived model uses the same inclusion. -/
theorem spFourDerivedEquiv_subgroup
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (A : Subgroup (BorelReduction.SourceCases.Sp4Derived F)) :
    A.map (spFourDerivedEquiv hF hf).toMonoidHom =
      A.map (BorelReduction.SourceCases.Sp4Derived F).subtype := rfl

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
