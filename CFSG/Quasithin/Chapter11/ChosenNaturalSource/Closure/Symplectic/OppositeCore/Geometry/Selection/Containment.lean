module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Kernel
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection.Cartan
public import Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan

/-!
# The original Cartan kernel belongs to the selected opposite pair

The source kernel centralizes L₁/O₂(L₁). Its image therefore centralizes
the literal point-local quotient. Preservation of the original point and
the selected opposite point puts that image in the marked SL₂ pair.
The odd Cartan kernel lifts into I because the two-group action kernel
normalizes I. The final selection theorem discharges this containment
for the constructed y, together with all preceding opposite geometry.

The natural action on Q/N and the full opposite-stabilizer Cartan
conjugacy remain with the opposite-core assembly; no bound Q≤O₂(G₁)
is assumed or asserted here. Source: Aschbacher--Smith 11.5.7, p.783.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Oddness and normalization by the actual two-group action kernel lift
Cartan containment from the full V-action to the original opposite join. -/
theorem cartanKernel_le_pair_of_actionImage (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (hi : actionImage (V := V) (cartanKernel E) ≤
      actionImage (V := V) (oppositeJoin (auxiliaryW E) y)) :
    cartanKernel E ≤ oppositeJoin (auxiliaryW E) y := by
  let J := L ⊔ (T : Subgroup G)
  let X := (cartanKernel E).subgroupOf J
  let I := (oppositeJoin (auxiliaryW E) y).subgroupOf J
  have hXJ : cartanKernel E ≤ J :=
    inf_le_left.trans ((hX.1.trans inf_le_left).trans le_sup_left)
  have hIJ : oppositeJoin (auxiliaryW E) y ≤ J := oppositeJoin_le_large E m hW hy
  have ho : Odd (Nat.card X) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXJ).toEquiv]
    exact hX.odd.of_dvd_nat (card_dvd_of_le (show cartanKernel E ≤ E.X from inf_le_left))
  have hp : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      (ho.coprime_two_left.of_dvd_right (_root_.orderOf_dvd_natCard x))
  have hn := large_core_normalizes_pair E m hy
  have hnI : J.pCoreIn 2 ≤ normalizer (oppositeJoin (auxiliaryW E) y : Set G) :=
    (le_inf hn.1 hn.2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hk : (largeAction E).ker ≤ (J.pCoreIn 2).subgroupOf J := by
    intro k hk
    rw [largeAction_ker] at hk
    exact (large_centralizer_eq_core E).le ⟨k.property,hk⟩
  have hkn : (largeAction E).ker ≤ normalizer (I : Set J) :=
    (hk.trans (comap_mono hnI)).trans
      ((oppositeJoin (auxiliaryW E) y).le_normalizer_comap J.subtype)
  have him : X.map (largeAction E) ≤ I.map (largeAction E) := by
    rw [largeAction_image E _ hXJ,largeAction_image E _ hIJ]
    exact hi
  have hle := isPPerfect_le_of_map_le_of_kernel_normalizes
    (largeAction E) X I hp (largeAction_kernel_isPGroup E) hkn him
  intro x hx
  exact hle (show (⟨x,hXJ hx⟩ : J) ∈ X from hx)

private theorem model_stabilizer_of_normalizes (m : MarkedFlag E)
    (U : Submodule E.input.field.Carrier (Vector E.input.field.Carrier)) (x : L)
    (hn : (x : G) ∈ normalizer ((LocalGeometry.Coordinates.sp4 m.action).preimage U : Set G)) :
    PointModel.quotientMap m x ∈ stabilizer U := by
  apply (mem_stabilizer_iff _ _).mpr
  intro v hv
  exact (((LocalGeometry.Coordinates.sp4 m.action).mem_normalizer_preimage_iff U x).mp hn v).mpr hv

/-- The literal opposite point preimage in the selected symplectic frame. -/
theorem opposition_point_preimage (m : MarkedFlag E) (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹) :
    E.V₁.map (MulAut.conj (y : G)).toMonoidHom =
      (LocalGeometry.Coordinates.sp4 m.action).preimage
        ((E.input.field.Carrier ∙ (Pi.single (.inr 0) 1 : Vector E.input.field.Carrier)).map
          (toLinear g).toLinearMap) := by
  let c := LocalGeometry.Coordinates.sp4 m.action
  rw [m.point_preimage]
  change (c.preimage (m.flag.space 0)).map _ = _
  rw [← c.preimage_map_action]
  congr 1
  change (m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap = _
  rw [hpoint,hy,← OppositeLongRootPair.opposition_point_image]
  change ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map _ = _
  rw [← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  change (g * TwoConjugate.opposition * g⁻¹) • (g • v) =
    g • ((TwoConjugate.opposition (F := E.input.field.Carrier)) • v)
  simp only [mul_smul,inv_smul_smul]

/-- Centralizing the original local quotient, together with preservation
of the two selected points, puts the Cartan kernel in the marked pair image. -/
theorem cartanKernel_image_le_pair (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y : G)).toMonoidHom : Set G)) :
    PointModel.image m (cartanKernel E) ≤
      OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom := by
  have hlocal := PointModel.local_identification m g hpoint
  rintro a ⟨x,hx,rfl⟩
  apply OppositeLongRootPair.mem_conjugate_pair_of_local_quotient_centralizing
    E.input.field.card_eq E.input.nonbinary g
  · have hh := cartan_normalizes_marked_flag E m hX 0 hx.1
    have hs := model_stabilizer_of_normalizes E m (m.flag.space 0) x hh
    rw [hpoint] at hs
    exact hs
  · apply model_stabilizer_of_normalizes E m _ x
    rw [← opposition_point_preimage E m g hpoint y hy]
    exact hXpoint hx.1
  · intro l hl
    rw [← hlocal] at hl
    obtain ⟨k,hk,rfl⟩ := hl
    have hcomm := coreQuotientCentralizer_commutator hx.2 hk
    have hh : PointModel.quotientMap m ⁅x,k⁆ ∈ PointModel.image m (E.L₁.pCoreIn 2) :=
      mem_map_of_mem _ hcomm
    rw [map_commutatorElement,PointModel.image_core m E.L₁ E.L₁_le,hlocal] at hh
    exact hh

/-- The actual odd Cartan kernel lies in the original opposite join.
The source action image is used only for the marked pair identification;
normalization by the two-group action kernel supplies the genuine lift. -/
theorem cartanKernel_le_oppositeJoin (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y : G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
        (FullAction.modelHom m)) :
    cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y : G) := by
  apply cartanKernel_le_pair_of_actionImage E m hX hW y.property
  rw [hi,← FullAction.image_eq m (cartanKernel E)
    (inf_le_left.trans (hX.1.trans inf_le_left))]
  exact map_mono (cartanKernel_image_le_pair E m hX g hpoint y hy hXpoint)

/-- The Cartan-compatible source choice includes X₁≤I, as well as the
literal opposite action, quotient spaces, and three local conjugators. -/
theorem exists_cartan_opposite_with_kernel (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
          (FullAction.modelHom m) ∧
      cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y : G) ∧
      E.X ≤ normalizer (E.V₁.map (MulAut.conj (y : G)).toMonoidHom : Set G) ∧
      E.X ≤ normalizer (corePair (auxiliaryW E) (y : G) : Set G) ∧
      IsCompl E.threeSpace (E.point.map (D.chosenCentralAction y)) ∧
      E.V₃ ⊔ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ∧
      E.V₃ ⊓ E.V₁.map (MulAut.conj (y : G)).toMonoidHom = V ⊓ centralizer (L : Set G) ∧
      (oppositeJoin (auxiliaryW E) (y : G)).pCoreIn 2 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      pairDenominator E (y : G) ≤ corePair (auxiliaryW E) (y : G) ∧
      ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
        L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) (y : G)).map
          (MulAut.conj (l i)).toMonoidHom) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨g,y,hflag,hlocal,hy,hi,hXp,hXQ,hs,hjoin,hmeet,hcore,hN,hgen⟩ :=
    exists_cartan_opposite_pair_geometry E m hX hW hroot hPhi
  exact ⟨g,y,hflag,hlocal,hy,hi,
    cartanKernel_le_oppositeJoin E m hX hW g (hflag 0) y hy hXp hi,
    hXp,hXQ,hs,hjoin,hmeet,hcore,hN,hgen⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
