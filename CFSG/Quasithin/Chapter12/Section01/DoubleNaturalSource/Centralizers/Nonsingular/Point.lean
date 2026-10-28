module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The actual residual and fixed vectors at a doubled-module point

The point residual is O²(C_L(w)), embedded back in G. Its image in the
normalizer action quotient is exactly the H.9 residual. Fixed vectors of
an image subgroup are precisely vectors centralized by its original actors.
Thus a residual element moving a fixed vector in the quotient lifts to an
element of the actual point residual, with the same movement in G.

Source: Aschbacher--Smith, 12.1.1, printed pp.788--789. These transport
identities prepare the ambient argument; they do not assert its conclusion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- The full ambient point centralizer G_w. -/
def pointCentralizer (_B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) : Subgroup G :=
  centralizer ({(w : G)} : Set G)

/-- The original normalizer point centralizer M_w. -/
def localPointCentralizer (w : componentOrbit V (T : Subgroup G)) : Subgroup G :=
  normalizer (L : Set G) ⊓ B.pointCentralizer w

/-- The intersection with the original Sylow, before any Sylow assertion. -/
def pointSylow (w : componentOrbit V (T : Subgroup G)) : Subgroup G :=
  (T : Subgroup G) ⊓ B.pointCentralizer w

/-- The two-residual inside the original component. -/
def pointResidualInComponent (w : componentOrbit V (T : Subgroup G)) : Subgroup L :=
  (pResidual 2 ((B.pointCentralizer w).subgroupOf L)).map
    ((B.pointCentralizer w).subgroupOf L).subtype

/-- The source L_w = O²(C_L(w)), embedded in the original ambient group. -/
def pointResidual (w : componentOrbit V (T : Subgroup G)) : Subgroup G :=
  (B.pointResidualInComponent w).map L.subtype

/-- The original T-fixed subgroup of the doubled orbit. -/
def fixedLine (_B : DoubledBranch T L V n) : Subgroup G :=
  componentOrbit V (T : Subgroup G) ⊓ centralizer (T : Set G)

theorem pointResidual_le (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w ≤ L ⊓ B.pointCentralizer w := by
  rintro _ ⟨l, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨a.val.property, a.property⟩

theorem pointResidual_le_normalizer (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w ≤ normalizer (L : Set G) :=
  (B.pointResidual_le w).trans (inf_le_left.trans L.le_normalizer)

theorem pointResidual_eq [Finite G] (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w = (pResidual 2 (L ⊓ B.pointCentralizer w : Subgroup G)).map
      (L ⊓ B.pointCentralizer w).subtype := by
  rw [pointResidual, pointResidualInComponent, map_embedded_pResidual,
    subgroupOf_map_subtype, inf_comm]

/-- Normality is relative to M_w, with the ambient residual embedding. -/
theorem localPointCentralizer_normalizes_residual [Finite G]
    (w : componentOrbit V (T : Subgroup G)) :
    B.localPointCentralizer w ≤ normalizer (B.pointResidual w : Set G) := by
  rw [B.pointResidual_eq]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ B.pointCentralizer w) (pResidual 2 _))
  exact (inf_le_inf le_rfl (B.pointCentralizer w).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

variable [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
namespace SourceModel
variable {B} (S : B.SourceModel)

/-- The component point-centralizer image uses the same quotient as H.9. -/
theorem component_point_image (w : componentOrbit V (T : Subgroup G)) :
    ((B.pointCentralizer w).subgroupOf L).map B.componentToActionQuotient =
      S.setup.innerStabilizer (Additive.ofMul w) := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨S.component_layer ▸ ⟨l, rfl⟩, ?_⟩
    have hh : inclusion L.le_normalizer l ∈
        (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := by
      rw [S.stabilizer_comap]
      exact hl
    exact hh
  · rintro ⟨ha, hw⟩
    rw [← S.component_layer] at ha
    obtain ⟨l, rfl⟩ := ha
    refine ⟨l, ?_, rfl⟩
    have hh : inclusion L.le_normalizer l ∈
        (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := hw
    rw [S.stabilizer_comap] at hh
    exact hh

/-- Images commute with the literal embedded residual, without a kernel premise. -/
theorem pointResidual_image [Finite G] (w : componentOrbit V (T : Subgroup G)) :
    (B.pointResidualInComponent w).map B.componentToActionQuotient =
      S.setup.residual (Additive.ofMul w) := by
  rw [pointResidualInComponent, map_embedded_pResidual, S.component_point_image]
  rfl

/-- Fixed spaces of an actual normalizer subgroup, with its literal image map. -/
theorem mem_fixed_image_iff (A : Subgroup (normalizer (L : Set G)))
    (z : componentOrbit V (T : Subgroup G)) :
    Additive.ofMul z ∈ S.setup.fixed (A.map B.actionProjection) ↔
      (z : G) ∈ centralizer (A.map (normalizer (L : Set G)).subtype : Set G) := by
  constructor
  · intro hz a ha
    obtain ⟨m, hm, rfl⟩ := ha
    have he := hz ⟨B.actionProjection m, mem_map_of_mem _ hm⟩
    rw [S.representation_eq] at he
    have he' := congrArg (fun u : Additive (componentOrbit V (T : Subgroup G)) =>
      (u.toMul : G)) he
    change (m : G) * (z : G) * (m : G)⁻¹ = (z : G) at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro hz a
    obtain ⟨m, hm, he⟩ := a.property
    change S.setup.representation (a : B.ActionQuotient) (Additive.ofMul z) = _
    rw [← he, S.representation_eq]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (m : G) * (z : G) * (m : G)⁻¹ = (z : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hz (m : G) (mem_map_of_mem _ hm))

/-- Residual movement in H.9 lifts to movement by the original O²(C_L(w)). -/
theorem exists_pointResidual_mover [Finite G]
    (w z : componentOrbit V (T : Subgroup G))
    (hm : ∃ a ∈ S.setup.residual (Additive.ofMul w),
      S.setup.representation a (Additive.ofMul z) ≠ Additive.ofMul z) :
    ∃ l ∈ B.pointResidual w, l * (z : G) * l⁻¹ ≠ (z : G) := by
  obtain ⟨a, ha, hm⟩ := hm
  rw [← S.pointResidual_image w] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  refine ⟨l, mem_map_of_mem _ hl, ?_⟩
  intro he
  apply hm
  rw [S.representation_eq]
  apply Additive.toMul.injective
  exact Subtype.ext he

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
