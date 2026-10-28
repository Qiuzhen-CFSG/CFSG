module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives
public import Theory.Representation.TripleSixFixedSpace

/-!
# Excluding the genuine triple-six moved section

The source's binary coordinates and scalar-linearity define a faithful
three-dimensional F₄ action of L. Its actual map onto L/Z(L) ≃ A₆ has
kernel of order three. The intrinsic order-four and orbit calculation
constructs a cubic element fixing a Sylow fixed space on this action.
The projective-line contract retains the two-dimensional offender plane;
no identification with a different representation is needed.

`NativeSections.movedSection_enlargement` lifts the cubic witness through
both genuine module extensions and then into an arbitrary ambient actor.
The literal offender action is excluded by its seed centralizer. The final
consumer sends `SectionAlternatives` to the binary G₂ branch, which has its
own fixed-space exclusion. The recognition owner assembles these calculations
with the separately proved source-row extraction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2(8), printed p.86; B.5.1, p.99; K.1.3, p.453; 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
namespace ExceptionalFixedSpace.TripleSix
open ClassificationComparison ClassificationComparison.FFAlternatives

universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

omit [Finite D] in
private noncomputable def fieldAction (a : ProjectiveLine.TripleSixAction ρ L) :
    Representation BinaryField.four.Carrier L (Fin 3 → BinaryField.four.Carrier) where
  toFun g :=
    { toFun := fun w => a.coordinates (ρ g (a.coordinates.symm w))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro c w
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          a.scalar_linear g c (a.coordinates.symm w) }
  map_one' := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ (1 : D) (a.coordinates.symm w)) = w
    rw [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ ((g * h : L) : D) (a.coordinates.symm w)) =
      a.coordinates (ρ g (a.coordinates.symm
        (a.coordinates (ρ h (a.coordinates.symm w)))))
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LinearEquiv.symm_apply_apply]

omit [Finite D] in
private theorem fieldAction_faithful (hρ : Function.Injective ρ)
    (a : ProjectiveLine.TripleSixAction ρ L) : Function.Injective (fieldAction a) := by
  intro g h he
  apply Subtype.ext
  apply hρ
  ext v
  apply a.coordinates.injective
  have hh := LinearMap.congr_fun he (a.coordinates v)
  change a.coordinates (ρ g (a.coordinates.symm (a.coordinates v))) =
    a.coordinates (ρ h (a.coordinates.symm (a.coordinates v))) at hh
  simpa only [LinearEquiv.symm_apply_apply] using hh

/-- Every Sylow subgroup of L has a cubic fixer on the literal natural section. -/
theorem natural_enlargement (hρ : Function.Injective ρ)
    (a : ProjectiveLine.TripleSixAction ρ L) (S : Sylow 2 L) :
    ∃ d : L, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (ρ.comp L.subtype) (S : Subgroup L), ρ d v = v := by
  let q := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q :=
    a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.card q.ker = 3 := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective,
      QuotientGroup.ker_mk', Nat.card_congr a.centerEquiv.toEquiv]
    change Nat.card (ZMod 3) = 3
    exact Nat.card_zmod 3
  obtain ⟨T, d, hd3, hdne, hfix⟩ := Representation.TripleSixFixedSpace.exists_cubic_fixer
    q hq hk (fieldAction a) (fieldAction_faithful hρ a)
    (show Nat.card BinaryField.four.Carrier = 4 from BinaryField.four.card_eq)
    (by simp : Module.finrank BinaryField.four.Carrier
      (Fin 3 → BinaryField.four.Carrier) = 3)
  apply sylow_fixedSpace_enlargement_of_cubic (ρ.comp L.subtype)
    (T : Subgroup L) T.isPGroup' d hd3 hdne _ S
  intro v hv
  apply a.coordinates.injective
  have hh := hfix (a.coordinates v) (by
    intro t
    change a.coordinates (ρ t.val (a.coordinates.symm (a.coordinates v))) = a.coordinates v
    rw [LinearEquiv.symm_apply_apply]
    exact congrArg a.coordinates (hv t))
  change a.coordinates (ρ d (a.coordinates.symm (a.coordinates v))) = a.coordinates v at hh
  change a.coordinates (ρ d v) = a.coordinates v
  simpa only [LinearEquiv.symm_apply_apply] using hh

/-- Lift through the central section and trivial quotient, retaining the ambient actor. -/
theorem movedSection_enlargement (s : MovedSection ρ L)
    (hf : Function.Injective s.action)
    (a : ProjectiveLine.TripleSixAction s.action L) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let T : Sylow 2 L := Classical.choice inferInstance
  exact NativeSections.movedSection_enlargement s T (natural_enlargement hf a T) S

/-- The exact section stored by the full B.5.1 conclusion supplies the outside-Sylow fixer. -/
theorem source_enlargement (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hf : Function.Injective c.sectionData.action)
    (a : ProjectiveLine.TripleSixAction c.sectionData.action L) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v :=
  movedSection_enlargement c.sectionData hf a S

end ExceptionalFixedSpace.TripleSix

open ClassificationComparison ClassificationComparison.FFAlternatives
variable {H : Type*} [Group H] [Finite H]
  (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- The seed centralizer excludes triple-six on the actual offender subgroup. -/
theorem offenderAction_not_tripleSix
    (L : Subgroup (offenderGroup P Z hC)) (s : MovedSection (offenderAction P Z hC) L)
    (hf : Function.Injective s.action) : ¬ Nonempty (ProjectiveLine.TripleSixAction s.action L) := by
  rintro ⟨a⟩
  obtain ⟨S, hS⟩ := exists_offenderSylow P Z hC
  obtain ⟨d, hd, _, hv⟩ := ExceptionalFixedSpace.TripleSix.movedSection_enlargement s hf a S
  exact offenderAction_no_fixedSpace_enlargement P Z hC (S : Subgroup _) hS d hd hv

/-- Apply the exclusion to the unaltered action stored by the exhaustive comparison. -/
theorem comparedBranch_not_tripleSix
    (b : QuasisimpleComparison.ComparedBranch (quotientAction P Z hC))
    (hf : Function.Injective b.source.sectionData.action) :
    ¬ Nonempty (ProjectiveLine.TripleSixAction b.source.sectionData.action
      (generalizedFitting (offenderGroup P Z hC))) :=
  offenderAction_not_tripleSix P Z hC _ b.source.sectionData hf

/-- Once the source module disjunction is supplied, only binary G₂ survives. -/
theorem offenderAction_binaryG2_of_models
    (L : Subgroup (offenderGroup P Z hC)) (s : MovedSection (offenderAction P Z hC) L)
    (h : SectionAlternatives s) :
    Function.Injective s.action ∧ Nonempty
      (MarkedActionEquiv s.action (offenderSubgroup s.action) L
        (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2)))) := by
  cases offenderAction_exceptionalSection_of_models P Z hC L s h with
  | binaryG2 hf a => exact ⟨hf, ⟨a⟩⟩
  | tripleSix hf a => exact (offenderAction_not_tripleSix P Z hC L s hf ⟨a⟩).elim

/-- The remaining action is marked on the comparison branch's literal offender group. -/
theorem comparedBranch_binaryG2_of_models
    (b : QuasisimpleComparison.ComparedBranch (quotientAction P Z hC))
    (h : SectionAlternatives b.source.sectionData) :
    Function.Injective b.source.sectionData.action ∧ Nonempty
      (MarkedActionEquiv b.source.sectionData.action
        (offenderSubgroup b.source.sectionData.action)
        (generalizedFitting (offenderGroup P Z hC))
        (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2)))) :=
  offenderAction_binaryG2_of_models P Z hC _ b.source.sectionData h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
