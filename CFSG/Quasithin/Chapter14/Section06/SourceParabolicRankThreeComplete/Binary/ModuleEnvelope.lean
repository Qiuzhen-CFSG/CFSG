module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The binary module envelopes in original 14.6.10(5)

A moved subgroup of the omega-center of the actual component-radical core
lies in the center of the MS commutator core. The first four C.1.34 rows
therefore put it inside a natural module or a doubled natural module. In the
layered rows we use the central natural section. The final row is excluded
by an explicit noncentral omega-center hypothesis, supplied by the original
source Sylow intersection in Binary.Source.

The plane configuration records the Sylow invariance and genuine first-residual
movement needed for the remaining projective-line calculation. Neither that
calculation nor its rank-three conclusion is assumed in the definition.
Source: Aschbacher--Smith C.1.34 and original14.6.10(5), pp.136--137,1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06.Binary
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G]

/-- The literal geometric input of the projective-line argument: a moving
four-group, normalized by a Sylow subgroup of the component. -/
structure PlaneConfiguration (C V : Subgroup G) : Prop where
  perfect : Group.IsPerfect C
  elementary : IsElementaryAbelian 2 (conjugateSpanBy V C)
  card : Nat.card V = 4
  sylow : ∃ P : Sylow 2 C,
    (P : Subgroup C).map C.subtype ≤ normalizer (V : Set G)
  moved : ∃ A : Subgroup G, A ≤ C ∧ IsPPerfect 2 A ∧
    A ≤ normalizer (V : Set G) ∧ ⁅V,A⁆ = V

/-- Natural coordinates on a containing module, after excluding the central
omega-center row. The contained subgroup is not identified with the MS core. -/
def ModuleEnvelope (C U : Subgroup G) : Prop :=
  ∃ (E : Subgroup G)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)),
    U ≤ E ∧
    (HasSectionModel C E ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
    HasSectionModel C E ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural 3)))

/-- A moved omega-center subgroup lies in the center of the literal MS core. -/
theorem moved_omega_le_center_msQ (C R U : Subgroup G)
    (hU : U ≤ omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2))
    (hm : ⁅U,C⁆ = U) : U ≤ FullSieve.SourceInterface.centerIn (msQ C R) := by
  let J := C ⊔ R
  have hUQ : U ≤ J.pCoreIn 2 := fun x hx =>
    ((mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)).1
  have hCQ : C ≤ normalizer (J.pCoreIn 2 : Set G) :=
    (show C ≤ J from le_sup_left).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hQ : msQ C R ≤ J.pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp hCQ
  have hUm : U ≤ msQ C R := hm ▸ commutator_mono hUQ le_rfl
  intro x hx
  refine ⟨⟨x,hUm hx⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  apply Subtype.ext
  exact ((mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)).2.2 q (hQ q.property)

/-- The complete C.1.34 alternatives supply natural coordinates around the
actual moved subgroup when their central omega-center row is impossible. -/
theorem envelope_of_module_alternatives (C R S U : Subgroup G)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : MSModuleAlternatives C R S 1 (ZMod 2) e)
    (hU : U ≤ omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2))
    (hm : ⁅U,C⁆ = U)
    (hnc : ¬ FullSieve.SourceInterface.omegaCenterIn S ≤
      FullSieve.SourceInterface.centerIn (C ⊔ R)) : ModuleEnvelope C U := by
  have hZ := moved_omega_le_center_msQ C R U hU hm
  have hQ : U ≤ msQ C R := hZ.trans (map_subtype_le _)
  rcases hc with hc | hc | hc | hc | hc
  · exact ⟨msQ C R,e,hQ,Or.inl hc.2.2⟩
  · exact ⟨msQ C R,e,hQ,Or.inr hc.1⟩
  · exact ⟨FullSieve.SourceInterface.centerIn (msQ C R),e,hZ,Or.inl hc.1⟩
  · exact ⟨⁅FullSieve.SourceInterface.centerIn (msQ C R),C⁆,e,hm ▸ commutator_mono hZ le_rfl,
      Or.inl hc.2.2.2.2.2.1⟩
  · exact (hnc hc.2.2.2.1).elim

end CFSG.Quasithin.Chapter14.Section06.Binary
