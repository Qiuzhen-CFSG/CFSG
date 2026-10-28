module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction.FrattiniSection
public import Theory.GroupTheory.SolvableRadical.AutomorphismAction
public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions
public import CFSG.Quasithin.Chapter1.Section03.FrattiniShape

/-!
# The original nonquasisimple component's four-group obstruction

The complete A.3.6 theorem supplies a characteristic odd omega--Frattini
plane, on which the inner-action kernel is exactly the Fitting subgroup.
A four-group acting faithfully on the radical quotient would consequently
act faithfully on this plane. Its scalar involution then acts trivially on
the radical quotient, a contradiction.

Both nonquasisimple A.3.6 alternatives are included, with every homocyclic
exponent and every Fitting prime retained. The original component and its
literal quotient by O₂ are connected by equivariant solvable-kernel descent.
Thus the two final contradictions on printed p.876 require only construction
of the geometric four-group, with no additional extension or characteristic
subgroup marking. This proves that obstruction, not the preceding geometry
or the full Theorem13.1.7.

Source: Aschbacher--Smith,13.1.14 and the end of13.1.7, printed p.876,
using A.3.6 and the strengthened original radical action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual nonquasisimple A.3.6 component has no four-group action
faithful on its own solvable-radical quotient. -/
theorem a36_four_group_action_not_injective
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    {C : Subgroup G} (hC : C.IsCComponent) (hc : A36Conclusion C)
    (hn : ¬ IsQuasisimple C)
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (ρ : E →* MulAut C) :
    ¬ Function.Injective ((quotientAut (solvableRadical C)).comp ρ) := by
  have hne : Nat.card (fittingSubgroup C) ≠ 1 := by
    intro he
    have hb : fittingSubgroup C = ⊥ := (card_le_one_iff_eq_bot _).mp he.le
    let := hc.2.2.1
    exact hn (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot))
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hne
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3,hk,_⟩ :=
    ((CenterFrattiniSource.strengthened_omega_actions hG hO hC hc).2 hn).2.2 p hd
  have hshape : XiOddQuotient p (omegaCore p C) :=
    ((RadicalStructure.core_omega (RadicalStructure.nonsimple_radical hc hn) hd).2).of_mulEquiv
      ((omega (pCore p C) (p := p) 1).equivMapOfInjective
        (pCore p C).subtype (pCore p C).subtype_injective)
  let : Fact (IsPGroup p (omegaCore p C)) := ⟨hshape.isPGroup⟩
  let : IsElementaryAbelian p (omegaCore p C ⧸ frattini (omegaCore p C)) :=
    isElementaryAbelian_quotient_frattini (p := p)
  have he : frattiniConjugation (omegaCore p C) = omegaFrattiniAction p C := by
    apply MonoidHom.ext
    intro c
    change quotientAut (frattini (omegaCore p C)) (MulAut.conjNormal c) =
      quotientAut (frattini (omegaCore p C))
        (MulAut.characteristic (omegaCore p C) (MulAut.conj c))
    rw [characteristic_conj_eq_conjNormal]
  apply four_group_quotient_action_not_injective_of_frattini_plane hE (by omega)
    (omegaCore p C) (solvableRadical C) hshape.frattini_card ?_ ρ
  rw [he,hk]
  exact le_solvableRadical _ inferInstance inferInstance

/-- The obstruction on the literal L/O∞(L), with the complete original
A.3.6 hypotheses discharged from the source local component. -/
theorem local_four_group_action_not_injective
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (ρ : E →* MulAut L) :
    ¬ Function.Injective ((quotientAut (solvableRadical L)).comp ρ) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hQ := uniqueness_local_quotient_sqtk hG hL.2.2
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hL.1
  let C := radicalLocalImage T L
  let e : (L ⧸ pCore 2 L) ≃* C := radicalLocalQuotientEquiv hL
  let q := QuotientGroup.mk' (pCore 2 L)
  let f : L →* C := e.toMonoidHom.comp q
  let σ : E →* MulAut C := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp ρ)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsSolvable f.ker := by
    rw [hker]
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    infer_instance
  have hcompat (a : E) (x : L) : σ a (f x) = f (ρ a x) := by
    change e (quotientAut (pCore 2 L) (ρ a) (e.symm (e (q x)))) = e (q (ρ a x))
    rw [e.symm_apply_apply]
    exact congrArg e (quotientAut_apply_mk (pCore 2 L) (ρ a) x)
  let : Group.IsNilpotent (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :=
    pCore_isPGroup.isNilpotent
  intro hi
  apply a36_four_group_action_not_injective hQ (pCore_quotient_pCore_eq_bot 2)
    (hL.1.map_quotient _) hc (fun h => hn (h.of_mulEquiv e.symm)) hE σ
  exact radical_quotient_action_injective_of_solvable_kernel f hf ρ σ hcompat hi

/-- The geometric four-group required by the two terminal source
contradictions cannot normalize the original nonquasisimple component and
act faithfully on L/O∞(L). The action is literal ambient conjugation. -/
theorem normalizer_four_group_action_not_injective
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L A : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hAL : A ≤ normalizer (L : Set G)) :
    ¬ Function.Injective ((quotientAut (solvableRadical L)).comp
      (L.normalizerMonoidHom.comp (inclusion hAL))) :=
  local_four_group_action_not_injective hG T hL hn hA _

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
