module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LiftedAction.Normalizer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Pairing
/-!
# Realization of the actual lifted tensor action

Split C_P(D)V by ambient multiplication and project C_P(D) through the
literal quotient P/V. An element normalizing D preserves that centralizer,
so its action in these coordinates is the prescribed pair of linear factors.
The actual tensor commutator pairing identifies conjugation by p in P with
the outer-product translation specified by p's opposite quotient summand.
The cubic-normalizer Frattini factorization proves the forward formula;
normalizer surjectivity and quotient surjectivity realize every parameter.
For the second summand both actor factors and tensor coordinates are swapped.

`blockCoordinates` discharges the pairing hypothesis from the earlier common
layer actions and the relative equality V = Z(P). It uses the same concrete
`blockEquiv` constructed in Splitting, preserving determinant markings.
No tensor orbit census or moving block normalizer is used.

Source: Aschbacher–Smith, 15.3.53–55 and 15.3.61(2), pp.1146–1151.
-/

public section
open Subgroup Matrix
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
private def selectedPlane (i : Fin 2) (w : SumVector) : Plane :=
  if i = 0 then w.1 else w.2
private def otherPlane (i : Fin 2) (w : SumVector) : Plane :=
  if i = 0 then w.2 else w.1
private def orientedActor (i : Fin 2) (a : Actor) : Actor :=
  if i = 0 then a else a.swap

private theorem selected_sumAction (i : Fin 2) (a : Actor) (w : SumVector) :
    (selectedPlane i (sumAction a w)).toAdd =
      (orientedActor i a).1.val *ᵥ (selectedPlane i w).toAdd := by
  fin_cases i <;> rfl

private theorem oriented_tensorAction (i : Fin 2) (a : Actor) (w : TensorVector) :
    orientTensor i (tensorAction a w) = tensorAction (orientedActor i a) (orientTensor i w) := by
  fin_cases i
  · rfl
  · change Multiplicative.ofAdd (a.1.val * w.toAdd * a.2.val.transpose).transpose =
      Multiplicative.ofAdd (a.2.val * w.toAdd.transpose * a.1.val.transpose)
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

private theorem append_linear (a : Actor) (u : Plane) (w : TensorVector) :
    appendColumns (Multiplicative.ofAdd (a.1.val *ᵥ u.toAdd), tensorAction a w) =
      transform a.1 a.2 0 (appendColumns (u,w)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · change (a.1.val * w.toAdd * a.2.val.transpose) i k =
      (a.1.val * w.toAdd * a.2.val.transpose) i k +
        (a.1.val *ᵥ u.toAdd) i * (0 : BinaryPlane) k
    simp only [Pi.zero_apply, mul_zero, add_zero]

private theorem append_translate (t : BinaryPlane) (u : Plane) (w : TensorVector) :
    appendColumns (u, Multiplicative.ofAdd (Matrix.vecMulVec u.toAdd t) * w) =
      transform (1 : PlaneActor) (1 : PlaneActor) t (appendColumns (u,w)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · change u.toAdd i = ((1 : BinaryMatrix) *ᵥ u.toAdd) i
    rw [Matrix.one_mulVec]
  · change u.toAdd i * t k + w.toAdd i k =
      ((1 : BinaryMatrix) * w.toAdd * (1 : BinaryMatrix).transpose) i k +
        ((1 : BinaryMatrix) *ᵥ u.toAdd) i * t k
    simp [add_comm]

private theorem translate_linear (l r : Frame) (t : BinaryPlane) (x : BlockModel) :
    transform (1 : PlaneActor) (1 : PlaneActor) t (transform l r 0 x) =
      transform l r t x := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · change ((1 : BinaryMatrix) *ᵥ (l.val *ᵥ first x)) i = _
    rw [Matrix.one_mulVec]
    rfl
  · change ((1 : BinaryMatrix) * (Matrix.of fun m n => (l.val * matrix x * r.val.transpose) m n +
        (l.val *ᵥ first x) m * (0 : BinaryPlane) n) * (1 : BinaryMatrix).transpose) i k +
        ((1 : BinaryMatrix) *ᵥ (l.val *ᵥ first x)) i * t k = _
    simp only [Pi.zero_apply, mul_zero, add_zero, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mulVec]
    rfl

private theorem oriented_pairing (i : Fin 2) (w u : SumVector)
    (hu : u ∈ naturalSummand i) :
    orientTensor i (Multiplicative.ofAdd
      (Matrix.vecMulVec w.1.toAdd u.2.toAdd + Matrix.vecMulVec u.1.toAdd w.2.toAdd)) =
      Multiplicative.ofAdd (Matrix.vecMulVec (selectedPlane i u).toAdd (otherPlane i w).toAdd) := by
  fin_cases i
  · have h : u.2 = 1 := hu
    rw [h]
    funext m n
    change w.1.toAdd m * (0 : BinaryPlane) n + u.1.toAdd m * w.2.toAdd n =
      u.1.toAdd m * w.2.toAdd n
    simp
  · have h : u.1 = 1 := hu
    rw [h]
    funext m n
    change w.1.toAdd n * u.2.toAdd m + (0 : BinaryPlane) n * w.2.toAdd m =
      u.2.toAdd m * w.1.toAdd n
    simp [mul_comm]

variable {G : Type*} [Group G] [Finite G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]
variable (d : LayerActions I Y P V hIP hIV) (hVP : V ≤ P)
  (hcentral : V ≤ centralizer (P : Set G)) (i : Fin 2) (D : Subgroup G)
  (hDI : D ≤ I) (hD : Nat.card D = 3)
  (himage : (D.subgroupOf I).map d.actor = complementaryCubic i)
local notation "C" => (P ⊓ centralizer (D : Set G) : Subgroup G)
local notation "B" => fusionBlock P V D
local notation "eB" => blockEquiv d hVP hcentral i D hDI hD himage

private theorem blockEquiv_product (c : C) (v : V) :
    eB ⟨(c : G) * v, (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) c.property) ((show V ≤ B from le_sup_right) v.property)⟩ =
      appendColumns (selectedPlane i (upperMap d ⟨c, c.property.1⟩),
        orientTensor i (d.lowerCoordinates v)) := by
  let s := splitBlock d hcentral i D himage
  have hs : s ⟨(c : G) * v, (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) c.property) ((show V ≤ B from le_sup_right) v.property)⟩ =
      (c,v) := by
    apply s.symm.injective
    rw [s.symm_apply_apply]
    apply Subtype.ext
    rfl
  change appendColumns (_, _) = _
  change appendColumns
    (((centralizerEquiv d hVP hcentral i D hDI hD himage).trans (naturalSummandEquiv i))
      (s ⟨_, _⟩).1, (d.lowerCoordinates.trans (orientTensor i)) (s ⟨_, _⟩).2) = _
  rw [hs]
  rfl

omit [Finite G] in
include d hcentral himage in
private theorem block_decomposition (x : B) :
    ∃ c : C, ∃ v : V, (x : G) = (c : G) * v := by
  let s := splitBlock d hcentral i D himage
  exact ⟨(s x).1, (s x).2, (congrArg Subtype.val (s.symm_apply_apply x)).symm⟩

private theorem normalizer_conjugation (n : I) (hn : (n : G) ∈ normalizer (D : Set G))
    (x : B) :
    MulAut.conj (n : G) (x : G) =
      ((eB).symm (transform (orientedActor i (d.actor n)).1
        (orientedActor i (d.actor n)).2 0 (eB x)) : G) := by
  obtain ⟨c, v, hx⟩ := block_decomposition d hcentral i D himage x
  have hCn : (n : G) ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hIP n.property,
      (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (D : Set G))) hn⟩
  let cn : C := ⟨MulAut.conj (n : G) (c : G),
    (mem_normalizer_iff.mp hCn c).mp c.property⟩
  let vn : V := lowerAction I V hIV n v
  let y : B := ⟨(cn : G) * vn,
    (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) cn.property) ((show V ≤ B from le_sup_right) vn.property)⟩
  have hex : eB x = appendColumns
      (selectedPlane i (upperMap d ⟨c, c.property.1⟩), orientTensor i (d.lowerCoordinates v)) := by
    have he : x = ⟨(c : G) * v,
        (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) c.property) ((show V ≤ B from le_sup_right) v.property)⟩ :=
      Subtype.ext hx
    rw [he, blockEquiv_product]
  have hey : eB y = transform (orientedActor i (d.actor n)).1
      (orientedActor i (d.actor n)).2 0 (eB x) := by
    rw [hex, ← append_linear]
    change eB ⟨(cn : G) * vn, _⟩ = _
    rw [blockEquiv_product]
    have hc : upperMap d ⟨cn, cn.property.1⟩ =
        sumAction (d.actor n) (upperMap d ⟨c, c.property.1⟩) :=
      upperMap_conj d n ⟨c, c.property.1⟩
    rw [hc]
    change appendColumns (_, orientTensor i (d.lowerCoordinates (lowerAction I V hIV n v))) = _
    rw [d.lower_compatible, oriented_tensorAction]
    congr 1
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd (selected_sumAction i (d.actor n) _)
    · rfl
  rw [← hey, (eB).symm_apply_apply]
  change MulAut.conj (n : G) (x : G) = (cn : G) * vn
  rw [hx, map_mul]
  rfl

private theorem inner_conjugation (hf : PairingFormula d) (p : P) (x : B) :
    MulAut.conj (p : G) (x : G) =
      ((eB).symm (transform (1 : PlaneActor) (1 : PlaneActor)
        (otherPlane i (upperMap d p)).toAdd (eB x)) : G) := by
  obtain ⟨c, v, hx⟩ := block_decomposition d hcentral i D himage x
  obtain ⟨hk, he⟩ := hf.commutator p ⟨c, c.property.1⟩
  let k : V := ⟨(p : G) * c * (p : G)⁻¹ * (c : G)⁻¹, hk⟩
  let y : B := ⟨(c : G) * (k * v : V),
    (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) c.property)
      ((show V ≤ B from le_sup_right) (k * v).property)⟩
  have hex : eB x = appendColumns
      (selectedPlane i (upperMap d ⟨c, c.property.1⟩), orientTensor i (d.lowerCoordinates v)) := by
    have hx' : x = ⟨(c : G) * v,
        (fusionBlock P V D).mul_mem ((show C ≤ B from le_sup_left) c.property)
          ((show V ≤ B from le_sup_right) v.property)⟩ := Subtype.ext hx
    rw [hx', blockEquiv_product]
  have hcq : upperMap d ⟨c, c.property.1⟩ ∈ naturalSummand i :=
    (centralizerProjection d hVP i D hDI hD himage c).property
  have hey : eB y = transform (1 : PlaneActor) (1 : PlaneActor)
      (otherPlane i (upperMap d p)).toAdd (eB x) := by
    rw [hex, ← append_translate]
    change eB ⟨(c : G) * (k * v : V), _⟩ = _
    rw [blockEquiv_product, map_mul, map_mul]
    change appendColumns (_, orientTensor i (d.lowerCoordinates ⟨_, hk⟩) * _) = _
    rw [he, oriented_pairing i _ _ hcq]
  rw [← hey, (eB).symm_apply_apply]
  have hpv : MulAut.conj (p : G) (v : G) = v := by
    change (p : G) * v * (p : G)⁻¹ = v
    rw [hcentral v.property p p.property, mul_inv_cancel_right]
  change MulAut.conj (p : G) (x : G) = (c : G) * ((k : G) * v)
  rw [hx, map_mul, hpv, ← mul_assoc, hcentral k.property c c.property.1]
  change (p : G) * c * (p : G)⁻¹ * v =
    ((p : G) * c * (p : G)⁻¹ * (c : G)⁻¹) * c * v
  group

private theorem product_conjugation (hf : PairingFormula d) (p : P) (n : I)
    (hn : (n : G) ∈ normalizer (D : Set G)) (x : B) :
    MulAut.conj ((p : G) * n) (x : G) =
      ((eB).symm (transform (orientedActor i (d.actor n)).1
        (orientedActor i (d.actor n)).2 (otherPlane i (upperMap d p)).toAdd (eB x)) : G) := by
  have hmul : MulAut.conj ((p : G) * n) (x : G) =
      MulAut.conj (p : G) (MulAut.conj (n : G) (x : G)) := by
    change ((p : G) * n) * x * ((p : G) * n)⁻¹ = _
    simp only [MulAut.conj_apply, _root_.mul_inv_rev]
    group
  rw [hmul, normalizer_conjugation d hVP hcentral i D hDI hD himage n hn,
    inner_conjugation d hVP hcentral i D hDI hD himage hf,
    (eB).apply_symm_apply]
  exact congrArg (fun z => ((eB).symm z : G))
    (translate_linear (orientedActor i (d.actor n)).1
      (orientedActor i (d.actor n)).2 (otherPlane i (upperMap d p)).toAdd (eB x))

private noncomputable def coordinatesOfPairing (hPI : P ≤ I) (hf : PairingFormula d) :
    BlockCoordinates I P V D where
  equiv := eB
  distinguished := blockEquiv_distinguished d hVP hcentral i D hDI hD himage
  forward := by
    intro g hg
    obtain ⟨p, n, hn, hpn⟩ := factor_through_cubic_normalizer d hPI hVP i D hDI hD himage ⟨g,hg⟩
    refine ⟨(orientedActor i (d.actor n)).1, (orientedActor i (d.actor n)).2,
      (otherPlane i (upperMap d p)).toAdd, ?_⟩
    intro x
    change g = (p : G) * n at hpn
    subst g
    exact product_conjugation d hVP hcentral i D hDI hD himage hf p n hn x
  realize := by
    intro l r t
    let a : Actor := orientedActor i (l,r)
    obtain ⟨n, hn, he⟩ := exists_normalizer_actor d hPI hVP i D hDI hD himage a
    have ha : orientedActor i (d.actor n) = (l,r) := by
      rw [he]
      fin_cases i <;> rfl
    let w : SumVector := if i = 0 then (1, Multiplicative.ofAdd t) else (Multiplicative.ofAdd t,1)
    have hup : Function.Surjective (upperMap d) :=
      d.upperCoordinates.surjective.comp (QuotientGroup.mk'_surjective (V.subgroupOf P))
    obtain ⟨p, hp⟩ := hup w
    have ht : (otherPlane i (upperMap d p)).toAdd = t := by
      rw [hp]
      fin_cases i <;> rfl
    refine ⟨(p : G) * n, I.mul_mem (hPI p.property) n.property, fun x => ?_⟩
    have h := product_conjugation d hVP hcentral i D hDI hD himage hf p n hn x
    rw [ha, ht] at h
    exact h

/-- Construct the actual six-dimensional block action from the earlier layer
representations and the relative center. The tensor commutator formula is proved,
not an additional premise. The normalizer realizes the linear factors, and the
opposite quotient summand realizes every inner translation. -/
noncomputable def blockCoordinates (hPI : P ≤ I)
    (hcenter : V = (center P).map P.subtype) : BlockCoordinates I P V D := by
  have hc : V ≤ centralizer (P : Set G) := by
    rw [hcenter]
    rintro v ⟨vP, hvP, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp hvP ⟨x,hx⟩)
  exact coordinatesOfPairing d hVP hc i D hDI hD himage hPI
    (pairingFormula_of_layerActions d hVP hcenter)

/-- The action realization retains precisely the equivalence constructed from
ambient multiplication and the literal quotient projection. -/
theorem blockCoordinates_equiv (hPI : P ≤ I)
    (hcenter : V = (center P).map P.subtype) :
    (blockCoordinates d hVP i D hDI hD himage hPI hcenter).equiv = eB := by
  rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
