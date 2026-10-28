module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalCrossing

/-!
# The noncentral coordinate of the entire crossed unitary root

The second natural coordinate on the crossed unitary root has exactly the
Frattini kernel of the unitary radical. To see this, a vector with second
coordinate zero lies on the crossed-linear line. Lift that vector through
the faithful linear-root chart; disjointness of the middle roots makes the
lift trivial. The source special-radical identity identifies the resulting
kernel with the full intrinsic center of the crossed unitary root.

Its orders q³ and q then prove surjectivity onto the quadratic field.
This retains all central elements, including the q = 2 quaternion center.
Source: Fong--Seitz II (8.14)--(8.16), printed pp.203--204.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open scoped Pointwise IsMulCommutative commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (J : HermitianForm 3 E) {n : ℕ}
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (hroot : ((rankOne Q split j).subtype.comp
    (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j)
  (hc : ∀ a v, c (Representation.elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (hphi : (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype ≤
    rootAt Q split j (Q.simple i))
  (hcard : Nat.card (simpleRoot Q split i) = Nat.card E)

include hm hij hE hfixed hVi hroot hc hphi hcard in
/-- The middle natural coordinate on the whole crossed unitary root has
exactly the actual Frattini kernel. -/
theorem crossed_unitary_coordinate_zero_iff (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (naturalSectionMap Q split j c v).toAdd 1 = 0 ↔ v ∈ frattini (simpleRemainder Q split j) := by
  constructor
  · intro hzero
    let e := naturalCrossEquiv Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi hcard
    let x := e.symm (.ofAdd ((naturalSectionMap Q split j c v).toAdd 0))
    let w : simpleRemainder Q split j :=
      ⟨x,(opposite_roots_le_remainder Q split i j hij).2 x.property⟩
    have h0 : (naturalSectionMap Q split j c w).toAdd 0 = (naturalSectionMap Q split j c v).toAdd 0 :=
      congrArg Multiplicative.toAdd (e.apply_symm_apply _)
    obtain ⟨h1,h2⟩ := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
      hm i hij hVi w x.property
    have hv2 := crossed_unitary_natural_plane Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc v hv
    have hq : QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w =
        QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v := by
      apply Additive.ofMul.injective
      apply c.injective
      ext k
      fin_cases k
      · exact h0
      · exact h1.trans hzero.symm
      · exact h2.trans hv2.symm
    have hdiff := hphi (mem_map_of_mem (simpleRemainder Q split j).subtype (QuotientGroup.eq.mp hq))
    have hxD : (x : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) := by
      have hh := (rootAt Q split j (Q.simple i)).mul_mem hv
        ((rootAt Q split j (Q.simple i)).inv_mem hdiff)
      change (v : X ⧸ Q.D) * ((x : X ⧸ Q.D)⁻¹ * v)⁻¹ ∈ _ at hh
      simpa only [mul_inv_rev,inv_inv,mul_inv_cancel_left] using hh
    have hx1 : (x : X ⧸ Q.D) = 1 :=
      (disjoint_iff.mp (crossed_roots_disjoint Q split hm i j hij)).le ⟨x.property,hxD⟩
    have hw : w = 1 := Subtype.ext hx1
    rw [hw,map_one] at hq
    exact (QuotientGroup.eq_one_iff v).mp hq.symm
  · intro hv
    have he : QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr hv
    change c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v)) 1 = 0
    rw [he]
    exact congrFun c.map_zero 1


/-- The first noncentral coordinate on the entire crossed unitary root,
measured in the same natural module as the crossed-linear coordinate. -/
def naturalUnitaryCoordinate : rootAt Q split j (Q.simple i) →* Multiplicative E where
  toFun v := .ofAdd ((naturalSectionMap Q split j c
    ⟨v,cross_root_le_own_remainder Q split hm j i hij.symm v.property⟩).toAdd 1)
  map_one' := by
    change Multiplicative.ofAdd ((naturalSectionMap Q split j c 1).toAdd 1) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((naturalSectionMap Q split j c
      (⟨x,cross_root_le_own_remainder Q split hm j i hij.symm x.property⟩ *
        ⟨y,cross_root_le_own_remainder Q split hm j i hij.symm y.property⟩)).toAdd 1) = _
    rw [map_mul]
    rfl

include hE hfixed hVi hroot hc hcard in
/-- The full intrinsic center, with no discarded scalar parameters, is the
kernel of the noncentral coordinate. -/
theorem naturalUnitaryCoordinate_ker
    (hcenter : (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype) :
    (naturalUnitaryCoordinate Q split hm i j hij c).ker = center (rootAt Q split j (Q.simple i)) := by
  ext x
  let v : simpleRemainder Q split j :=
    ⟨x,cross_root_le_own_remainder Q split hm j i hij.symm x.property⟩
  have he := crossed_unitary_coordinate_zero_iff Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc
    (hcenter.le.trans (map_subtype_le _)) hcard v x.property
  change Multiplicative.ofAdd ((naturalSectionMap Q split j c v).toAdd 1) = 1 ↔ x ∈ _
  rw [show Multiplicative.ofAdd ((naturalSectionMap Q split j c v).toAdd 1) = 1 ↔
    (naturalSectionMap Q split j c v).toAdd 1 = 0 from Multiplicative.ofAdd.injective.eq_iff]
  rw [he]
  constructor
  · intro hx
    have hh := hcenter ▸ mem_map_of_mem (simpleRemainder Q split j).subtype hx
    obtain ⟨y,hy,hxy⟩ := hh
    exact (Subtype.val_injective hxy : y = x) ▸ hy
  · intro hx
    have hh : (x : X ⧸ Q.D) ∈ (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
      rw [hcenter]
      exact ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hh
    exact (Subtype.val_injective hxy : y = v) ▸ hy

include hE hfixed hVi hroot hc hcard in
/-- The noncentral coordinate covers the whole quadratic field. -/
theorem naturalUnitaryCoordinate_surjective
    (hcenter : (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype)
    (hD : Nat.card (rootAt Q split j (Q.simple i)) = (2^n)^3)
    (hZ : Nat.card (center (rootAt Q split j (Q.simple i))) = 2^n) :
    Function.Surjective (naturalUnitaryCoordinate Q split hm i j hij c) := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [naturalUnitaryCoordinate_ker Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hcard hcenter,hZ,hD]
  change 2^n ≤ (2^n)^3 / Nat.card E
  rw [hE]
  apply (Nat.le_div_iff_mul_le (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) n) 2)).mpr
  exact le_of_eq (by ring)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
