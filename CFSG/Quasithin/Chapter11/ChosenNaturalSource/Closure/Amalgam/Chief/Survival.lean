module
public import Theory.GroupTheory.GeneralizedFitting.CoreImageDetection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.KernelBound

/-!
# A genuine chief section detecting the generalized-Fitting lift

The literal conjugation action has precisely the original relative
centralizer as its kernel on K. The two-center bound therefore prevents
the generalized-Fitting lift from disappearing into the two-core of the
faithful action image. The chief-flag detection theorem then constructs
an actual (KT)^g-chief section of U^g on which that lift survives.

No faithful-action or trivial-two-core assumption is imposed on the full
module. The local quotient marking and relative-component status are the
earlier inputs from qt-d-1222-natural-flag-cartan and
qt-d-1222-natural-relative-components. Proving that a seed element moves
an F*-detecting section remains with qt-d-1222-amalgam-chief-section.
Source: Aschbacher--Smith, last paragraph of 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)
variable [IsElementaryAbelian 2 (localClosure E)]

private theorem componentAction_kernel :
    (Models.componentAction E g (action E g)).ker =
      (centralizer (localClosure E : Set G)).subgroupOf E.K := by
  ext k
  have hrep : k ∈ (Models.componentAction E g (action E g)).ker ↔
      Models.componentEmbedding E g k ∈ (action E g).ker := by
    change actionHom (action E g) (Models.componentEmbedding E g k) = 1 ↔ _
    rw [actionHom_eq_one_iff]
    exact ⟨fun hw => LinearMap.ext hw, fun he w => LinearMap.congr_fun he w⟩
  rw [hrep, action_kernel]
  change (MulAut.conj g) (k : G) ∈ centralizer
      ((localClosure E).map (MulAut.conj g).toMonoidHom : Set G) ↔
    (k : G) ∈ centralizer (localClosure E : Set G)
  rw [show ((localClosure E).map (MulAut.conj g).toMonoidHom : Set G) =
      (MulAut.conj g) '' (localClosure E : Set G) from rfl,
    ← map_centralizer_equiv (localClosure E : Set G) (MulAut.conj g), mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]

/-- The actual generalized-Fitting lift survives outside the action-image core. -/
theorem fitting_image_not_le_twoCore (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    [IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁)] :
    ¬ markedFitting E g ≤
      (pCore 2 (actionImage (action E g))).comap (actionHom (action E g)) := by
  let f := Models.componentAction E g (action E g)
  have hk : f.ker ≤ (center (E.K ⧸ pCore 2 E.K)).comap (QuotientGroup.mk' (pCore 2 E.K)) := by
    intro k hker
    rw [componentAction_kernel] at hker
    obtain ⟨y,hy,he⟩ := K_centralizer_le_two_center E h hK hlt ⟨k.property,hker⟩
    have he' : y = k := Subtype.ext he
    exact he' ▸ hy
  have hc := Models.component_top E hK
  let : Group.IsPerfect (⊤ : Subgroup E.K) := hc.perfect
  let : Group.IsPerfect E.K := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup E.K) ≃* E.K).toMonoidHom) topEquiv.surjective
  have hq := Models.quotient_component_top E hK
  let : Nontrivial (⊤ : Subgroup (E.K ⧸ pCore 2 E.K)) := (nontrivial_iff_ne_bot _).mpr hq.ne_bot
  let : Nontrivial (E.K ⧸ pCore 2 E.K) := topEquiv.injective.nontrivial
  have hfit := fitting_preimage_not_le_core_comap f.rangeRestrict f.rangeRestrict_surjective
    (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  intro hbad
  apply hfit
  intro k hkF
  have hm : Models.componentEmbedding E g k ∈ markedFitting E g :=
    mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_map_of_mem E.K.subtype hkF)
  have hfcore : f k ∈ pCore 2 (actionImage (action E g)) := hbad hm
  have hrestrict : (pCore 2 (actionImage (action E g))).comap f.range.subtype ≤
      pCore 2 f.range := le_sSup ⟨inferInstance,
        pCore_isPGroup.comap_of_injective f.range.subtype f.range.subtype_injective⟩
  exact hrestrict hfcore

/-- A literal chief section detecting the conjugated lift, with no survival premise. -/
theorem exists_fitting_chief_section_of_local_quotient (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    [IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁)] :
    ∃ A B : Subrepresentation (action E g), A ⋖ B ∧
      ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker :=
  exists_fitting_chief_section E g (fitting_image_not_le_twoCore E g h hK hlt)

/-- The actual source flag marking gives an F*-detecting section. Seed movement
on that same section is the remaining joint-detection obligation. -/
theorem exists_fitting_chief_section_of_rank_one (h : LocalInputs E)
    (hK : Source.NormalComponentIn E.G₁ E.K) (hlt : E.L₁ < E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree)) :
    ∃ A B : Subrepresentation (action E g), A ⋖ B ∧
      ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := hlocal
  have hlarge : 4 ≤ Nat.card F := by
    rw [hcard]
    change (2 : ℕ)^2 ≤ 2 ^ E.input.field.degree
    exact Nat.pow_le_pow_right (by decide) (by have := E.input.nonbinary; omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := e.isSimpleGroup
  exact exists_fitting_chief_section_of_local_quotient E g h hK hlt

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
