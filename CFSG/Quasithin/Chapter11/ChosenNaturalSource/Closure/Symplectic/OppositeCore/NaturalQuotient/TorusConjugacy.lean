module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.TorusConjugacy.Diagonal
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Conjugating the original Cartan kernel under the opposite stabilizer

Every member of the full S=N_M₁(V₁ʸ) preserves L, L₁, the two points,
and I. The literal quotient comparison puts X₁ˢ inside O₂(I)X₁.
This product is solvable, with X₁ an odd Hall subgroup. Hall conjugacy
and the product decomposition therefore give a conjugator in O₂(I).
No restriction of S to L and no normalization of [Q,X₁] is assumed.
The core-transfer assembly applies this to the original commutator.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

open Subgroup Matrix Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups Pointwise commutatorElement
set_option backward.isDefEq.respectTransparency false
public noncomputable section

private theorem odd_conjugate_in_two_product {A : Type*} [Group A] [Finite A]
    (R X : Subgroup A) (hR : IsPGroup 2 R) (hX : Group.IsSolvable X)
    (ho : Odd (Nat.card X)) (hn : X ≤ normalizer (R : Set A))
    (s : A) (hs : X.map (MulAut.conj s).toMonoidHom ≤ R ⊔ X) :
    ∃ r ∈ R, X.map (MulAut.conj s).toMonoidHom = X.map (MulAut.conj r).toMonoidHom := by
  let B := R ⊔ X
  let Xs := X.map (MulAut.conj s).toMonoidHom
  let : Group.IsNilpotent R := hR.isNilpotent
  let : Group.IsSolvable X := hX
  have hB : Group.IsSolvable B := Group.isSolvable_sup_of_normalizes R X hn
  have hhall : IsHallSubgroup OddHall.oddPrimes (X.subgroupOf B) :=
    OddHall.oddHall_of_normalized_sup hR ho.coprime_two_left hn rfl
  have hcard : Nat.card Xs = Nat.card X := Nat.card_congr ((MulAut.conj s).subgroupMap X).symm.toEquiv
  obtain ⟨Y,hXY,hYB,hY⟩ := OddHall.exists_hall_containing_odd B Xs hB hs (hcard ▸ ho)
  have hYX : Nat.card Y = Nat.card X := by
    have hc := hY.card_eq hhall
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hYB).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (show X ≤ B from le_sup_right)).toEquiv] using hc
  have hYe : Xs = Y := eq_of_le_of_card_ge hXY (by omega)
  rw [← hYe] at hY
  obtain ⟨b,hb⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hB hhall hY
  have hb' : Xs = X.map (MulAut.conj (b:A)).toMonoidHom := by
    have he := congrArg (fun Z : Subgroup B => Z.map B.subtype) hb
    rw [map_subgroupOf_eq_of_le hs,Subgroup.map_map] at he
    rw [← map_subgroupOf_eq_of_le (show X ≤ B from le_sup_right),Subgroup.map_map]
    exact he
  have hp : (b:A) ∈ (R:Set A) * (X:Set A) := by
    rw [← coe_mul_of_right_le_normalizer_left R X hn]
    exact b.property
  obtain ⟨r,hr,x,hx,he⟩ := hp
  refine ⟨r,hr,?_⟩
  change Xs = _
  rw [hb',← he]
  have hc : (MulAut.conj (r*x)).toMonoidHom =
      (MulAut.conj r).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply,mul_assoc]
  rw [hc,← Subgroup.map_map]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer hx)

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- A scalar actor of the literal pair differs from a source Cartan lift by O₂(I). -/
theorem scalar_actor_le_core_sup_cartan (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G))
    (x : L) (hx : (x:G) ∈ oppositeJoin (auxiliaryW E) (y:G))
    (s : E.input.field.Carrierˣ)
    (hs : PointModel.quotientMap m x = g * diagonalTorus s 1 * g⁻¹) :
    (x:G) ∈ (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ⊔ cartanKernel E := by
  obtain ⟨z,hz⟩ := exists_cartan_scalar_lift E m hX g hflag y hy hXpoint s
  have hzX := scalar_lift_mem_cartanKernel E m hX g
    (PointModel.local_identification m g (hflag 0)) z s hz
  let I := oppositeJoin (auxiliaryW E) (y:G)
  let xI : I := ⟨x,hx⟩
  let zI : I := ⟨z,hXI hzX⟩
  let zL : L := inclusion (hX.1.trans inf_le_left) z
  let f := pairAction E m hW g y hi
  have he : f xI = f zI := by
    apply OppositeLongRootPair.embedding_injective
    apply (MulAut.conj g).injective
    exact (pairAction_component E m hW g y hi x hx).trans
      (hs.trans (hz.symm.trans (pairAction_component E m hW g y hi zL (hXI hzX)).symm))
  have hk : xI * zI⁻¹ ∈ pCore 2 I := by
    rw [← pairAction_ker_eq_core E m hW g y hi]
    change f (xI*zI⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (I.pCoreIn 2 ⊔ cartanKernel E).mul_mem
    (mem_sup_left (mem_map_of_mem I.subtype hk)) (mem_sup_right hzX)
  change ((x:G)*(z:G)⁻¹)*(z:G) ∈ I.pCoreIn 2 ⊔ cartanKernel E at hm
  simpa only [inv_mul_cancel_right] using hm

/-- The full opposite-point stabilizer takes X₁ into O₂(I)X₁. -/
theorem stabilizer_conjugate_cartan_le_core_sup (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G))
    (s : G) (hs : s ∈ oppositePointStabilizer E (y:G)) :
    (cartanKernel E).map (MulAut.conj s).toMonoidHom ≤
      (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ⊔ cartanKernel E := by
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact cartan_normalizes_marked_flag E m hX 0
  have hnL : s ∈ normalizer (E.L₁ : Set G) := by
    apply normalizer_le_normalizer_characteristic_image
      (L ⊓ E.G₁) (solvableResidual (L ⊓ E.G₁ : Subgroup G))
    exact inf_normalizer_le_normalizer_inf ⟨hs.1.1,E.G₁.le_normalizer hs.1.2⟩
  rintro a ⟨x,hx,rfl⟩
  have hxL : x ∈ L := (hX.1.trans inf_le_left) hx.1
  have haL : (MulAut.conj s) x ∈ L := (mem_normalizer_iff.mp hs.1.1 x).mp hxL
  have haI := (mem_normalizer_iff.mp (opposite_stabilizer_normalizes_join E (y:G) hs) x).mp (hXI hx)
  have haG : (MulAut.conj s) x ∈ E.G₁ := E.G₁.mul_mem
    (E.G₁.mul_mem hs.1.2 (hXG hx.1)) (E.G₁.inv_mem hs.1.2)
  have hap : (MulAut.conj s) x ∈ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G) :=
    mul_mem (mul_mem hs.2 (hXpoint hx.1)) (inv_mem hs.2)
  have hac : (MulAut.conj s) x ∈ coreQuotientCentralizer E.L₁ :=
    (mem_normalizer_iff.mp (normalizer_normalizes_coreQuotientCentralizer E.L₁ hnL) x).mp hx.2
  obtain ⟨t,ht⟩ := scalar_image_of_point_pair_centralizer E m g (hflag 0) y hy ⟨_,haL⟩ haG hap hac
  exact scalar_actor_le_core_sup_cartan E m hX hW g hflag y hy hXpoint hi hXI ⟨_,haL⟩ haI t ht

/-- Conjugacy under the actual O₂(I), for every member of the full source stabilizer. -/
theorem opposite_stabilizer_cartan_conjugacy (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (g : Sp E.input.field.Carrier)
    (hflag : ∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G))
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G)) :
    ∀ s ∈ oppositePointStabilizer E (y:G),
      ∃ r ∈ (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2,
        (cartanKernel E).map (MulAut.conj s).toMonoidHom =
          (cartanKernel E).map (MulAut.conj r).toMonoidHom := by
  have hXX : cartanKernel E ≤ E.X := inf_le_left
  have he := (LocalGeometry.Coordinates.sp4 m.action).cartanTorusEquiv hX
  let : Group.IsSolvable E.X := Group.isSolvable_of_isSolvable_injective (f := he.toMonoidHom) he.injective
  have hsolv : Group.IsSolvable (cartanKernel E) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hXX) (inclusion_injective hXX)
  have ho := hX.odd.of_dvd_nat (card_dvd_of_le hXX)
  have hn : cartanKernel E ≤ normalizer
      ((oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 : Set G) :=
    hXI.trans ((oppositeJoin (auxiliaryW E) (y:G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  intro s hs
  exact odd_conjugate_in_two_product _ _ (isPGroup_pCoreIn 2 _) hsolv ho hn s
    (stabilizer_conjugate_cartan_le_core_sup E m hX hW g hflag y hy hXpoint hi hXI s hs)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
