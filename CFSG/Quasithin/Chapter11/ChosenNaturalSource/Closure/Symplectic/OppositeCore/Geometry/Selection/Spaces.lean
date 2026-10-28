module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Denominator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.Transport

/-!
# The actual complementary spaces for a marked opposite lift

The standard perpendicular hyperplane complements the opposite point.
The same symplectic marking and the original quotient action transport
this complement to the chosen central quotient. Their ambient preimages
join to V and intersect in C_V(L), retaining the common central kernel.
Every lift of the marked opposition has these properties.

Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry

private theorem standard_complement {F : Type*} [Field F] [Finite F] [CharP F 2] :
    IsCompl (LocalGeometry.Sp4.ModelFlag.hyperplane (F := F))
      ((point F).map (toLinear TwoConjugate.opposition).toLinearMap) := by
  let v : Vector F := Pi.single (.inr 0) 1
  have he : toLinear (TwoConjugate.opposition (F := F)) (e 0) = v := by
    change (TwoConjugate.opposition (F := F)) • e (F := F) 0 = v
    rw [TwoConjugate.opposition_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Theory.SpecificGroups.SymplecticFour.e, v]
  have hp : (point F).map (toLinear TwoConjugate.opposition).toLinearMap = F ∙ v := by
    rw [point, Submodule.map_span, Set.image_singleton]
    change F ∙ (toLinear (TwoConjugate.opposition (F := F)) (e 0)) = F ∙ v
    rw [he]
  rw [hp]
  constructor
  · rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx.2
    have ha : a = 0 := by
      simpa [v] using (LocalGeometry.Sp4.ModelFlag.mem_hyperplane _).mp hx.1
    simp [ha]
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x - x (.inr 0) • v, ?_, x (.inr 0) • v, ?_, sub_add_cancel _ _⟩
    · apply (LocalGeometry.Sp4.ModelFlag.mem_hyperplane _).mpr
      simp [v]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))

private theorem map_complement {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (a : M ≃ₗ[F] M) {U W : Submodule F M} (h : IsCompl U W) :
    IsCompl (U.map a.toLinearMap) (W.map a.toLinearMap) := by
  constructor
  · rw [disjoint_iff, ← Submodule.map_inf _ a.injective, h.inf_eq_bot, Submodule.map_bot]
  · rw [codisjoint_iff, ← Submodule.map_sup, h.sup_eq_top]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr a.surjective

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The same marked action takes the point to a complement of the original
three-space. This is a statement in the field model of the chosen quotient. -/
theorem opposite_field_spaces_complementary (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    IsCompl (m.flag.space 2)
      ((m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap) := by
  have he : ((m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap) =
      ((point E.input.field.Carrier).map (toLinear TwoConjugate.opposition).toLinearMap).map
        (toLinear g).toLinearMap := by
    rw [hflag 0, hy]
    change ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map _ = _
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro v
    change (g * TwoConjugate.opposition * g⁻¹) • (g • v) =
      g • ((TwoConjugate.opposition (F := E.input.field.Carrier)) • v)
    simp only [mul_smul, inv_smul_smul]
  rw [he, hflag 2]
  exact map_complement (toLinear g) standard_complement

private theorem binary_complement {F : BinaryField} (c : LocalGeometry.Coordinates D F)
    {U W : Submodule F.Carrier c.Space} (h : IsCompl U W) :
    IsCompl (c.binarySubspace U) (c.binarySubspace W) := by
  constructor
  · rw [disjoint_iff]
    apply le_bot_iff.mp
    intro v hv
    change v = 0
    apply c.linearEquiv.injective
    exact (show c.linearEquiv v = 0 from h.disjoint.le_bot hv).trans c.linearEquiv.map_zero.symm
  · rw [codisjoint_iff]
    apply top_unique
    intro v _
    have hv : c.linearEquiv v ∈ U ⊔ W := by rw [h.sup_eq_top]; trivial
    obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hv
    apply Submodule.mem_sup.mpr
    refine ⟨c.linearEquiv.symm u, ?_, c.linearEquiv.symm w, ?_, ?_⟩
    · change c.linearEquiv (c.linearEquiv.symm u) ∈ U
      simpa only [c.linearEquiv.apply_symm_apply] using hu
    · change c.linearEquiv (c.linearEquiv.symm w) ∈ W
      simpa only [c.linearEquiv.apply_symm_apply] using hw
    · apply c.linearEquiv.injective
      simpa only [map_add, c.linearEquiv.apply_symm_apply] using he

private theorem binary_map_action {F : BinaryField} (c : LocalGeometry.Coordinates D F)
    (U : Submodule F.Carrier c.Space) (y : L) :
    c.binarySubspace (U.map (c.modelAction (c.quotientMap y))) =
      (c.binarySubspace U).map (D.chosenCentralAction y) := by
  have hi (v : D.chosenCentralQuotient) :
      c.linearEquiv (D.chosenCentralAction y v) =
        c.modelAction (c.quotientMap y) (c.linearEquiv v) :=
    c.intertwines (QuotientGroup.mk' (pCore 2 L) y) v
  ext v
  constructor
  · intro hv
    change c.linearEquiv v ∈ U.map (c.modelAction (c.quotientMap y)) at hv
    obtain ⟨u,hu,he⟩ := Submodule.mem_map.mp hv
    refine ⟨c.linearEquiv.symm u, ?_, ?_⟩
    · change c.linearEquiv (c.linearEquiv.symm u) ∈ U
      simpa only [c.linearEquiv.apply_symm_apply] using hu
    · apply c.linearEquiv.injective
      rw [hi, c.linearEquiv.apply_symm_apply]
      exact he
  · rintro ⟨w,hw,rfl⟩
    exact ⟨c.linearEquiv w,hw,(hi w).symm⟩

/-- Complementarity holds for the literal chosen central quotient and its
original L-action, before taking any ambient preimages. -/
theorem opposite_quotient_spaces_complementary (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    IsCompl E.threeSpace (E.point.map (D.chosenCentralAction y)) := by
  have h := binary_complement (LocalGeometry.Coordinates.sp4 m.action)
    (opposite_field_spaces_complementary E m g hflag y hy)
  rw [m.threeSpace_eq, m.point_eq]
  exact (binary_map_action (LocalGeometry.Coordinates.sp4 m.action) (m.flag.space 0) y) ▸ h

/-- The lifted preimages sum to V and meet in the full original central
kernel. They need not be disjoint as ambient subgroups. -/
theorem opposite_preimages (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    E.V₃ ⊔ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ∧
      E.V₃ ⊓ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ⊓ centralizer (L : Set G) := by
  let c := LocalGeometry.Coordinates.sp4 m.action
  have h := opposite_field_spaces_complementary E m g hflag y hy
  have he : E.V₁.map (MulAut.conj (y : G)).toMonoidHom =
      c.preimage ((m.flag.space 0).map (c.modelAction (c.quotientMap y))) := by
    rw [c.preimage_map_action, m.point_preimage]
    rfl
  rw [he, m.threeSpace_preimage]
  change c.preimage (m.flag.space 2) ⊔ c.preimage _ = V ∧
    c.preimage (m.flag.space 2) ⊓ c.preimage _ = V ⊓ centralizer (L : Set G)
  rw [← c.preimage_sup, ← c.preimage_inf]
  change c.preimage (_ ⊔ (m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap) = V ∧
    c.preimage (_ ⊓ (m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap) = _
  rw [h.sup_eq_top, h.inf_eq_bot, c.preimage_top, c.preimage_bot]
  exact ⟨rfl,rfl⟩

/-- The actual denominator construction now receives its geometric sum
premise from the marked opposition, retaining the original quotient groups. -/
theorem opposition_denominator_le_corePair (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    pairDenominator E (y : G) ≤ corePair (auxiliaryW E) (y : G) :=
  NaturalQuotient.denominator_le_corePair E m y.property hW hPhi
    (opposite_preimages E m g hflag y hy).1.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
