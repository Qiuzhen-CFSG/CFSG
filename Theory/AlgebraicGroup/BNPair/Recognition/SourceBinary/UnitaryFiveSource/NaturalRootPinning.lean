module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RootCharts
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions

/-!
# Full SU₃ root pinning and its natural section

Conjugate a Sylow subgroup of the actual SU₃ actor to the actual source
unitary root. Change the natural basis by that same explicit inner conjugator,
so every original actor element remains tracked. The entire nonabelian root,
including its center, then acts by its Hermitian upper triangular matrix.
Its fixed vectors are exactly the first coordinate line, also for q = 2.
The actual crossed linear root lies on this line by source commutation.

Source: Fong--Seitz II (8C), (8.14)--(8.16), printed pp.203--204.
This pins the unitary actor and natural coordinates together; comparison
with the independently constructed SL₂ Hermitian coordinates is still needed.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [Finite E] [CharP E 2] in
private theorem specialRoot_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) he)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) he)

private def specialSylowCoordinates (T : Sylow 2 J.specialSubgroup) :
    T ≃* hermitianUnipotentCoord J := by
  letI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact (SylowOmega.specialSylowEquivProjective J T).trans
    (((T.mapSurjective J.specialToProjective_surjective).equiv
      (EvenTwoRank.rootSylow J hJ hn hE hfixed)).trans
        (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).symm)

include hn hE hfixed in
private theorem exists_specialRootSylow :
    ∃ T : Sylow 2 J.specialSubgroup,
      (T : Subgroup _) = (hermitianUnipotentSU J hJ).range := by
  let e := MonoidHom.ofInjective (specialRoot_injective J hJ)
  have hp : IsPGroup 2 (hermitianUnipotentSU J hJ).range :=
    (BinaryRootFrattini.isTwoGroup J).of_equiv e
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  have hc : Nat.card T = Nat.card (hermitianUnipotentSU J hJ).range :=
    Nat.card_congr ((specialSylowCoordinates J hn hE hfixed hJ T).trans e).toEquiv
  exact ⟨T,(eq_of_le_of_card_ge hT hc.le).symm⟩

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (κ : rankOne Q split j ≃* J.specialSubgroup)

include hn hE hfixed hVj ν in
/-- An inner change of basis pins the full SU3 root to the actual source root.
The supplied SU3 marking is retained in the elementwise equation. -/
theorem exists_unitary_root_pinning :
    ∃ (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j),
      ((rankOne Q split j).subtype.comp
        (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j ∧
      ∀ a, κ (θ a) = g * a * g⁻¹ := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨T,hT⟩ := hA.exists_le_sylow
  let T' := T.mapSurjective (f := κ.toMonoidHom) κ.surjective
  let eT : T ≃* T' := (T : Subgroup _).equivMapOfInjective κ.toMonoidHom κ.injective
  let eA : A ≃* hermitianUnipotentCoord J :=
    (subgroupOfEquivOfLe (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).trans
      (simpleRootUnitaryEquiv J Q split hn hE hfixed hJ j hVj ν)
  have hc : Nat.card T = Nat.card A :=
    Nat.card_congr ((eT.trans (specialSylowCoordinates J hn hE hfixed hJ T')).trans eA.symm).toEquiv
  have hTA : (T : Subgroup _) = A := (eq_of_le_of_card_ge hT hc.le).symm
  obtain ⟨R,hR⟩ := exists_specialRootSylow J hn hE hfixed hJ
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J.specialSubgroup R T'
  let θ := (MulAut.conj g).trans κ.symm
  have hroot : ((hermitianUnipotentSU J hJ).range).map (MulAut.conj g).toMonoidHom =
      A.map κ.toMonoidHom := by
    have hh := congrArg (fun V : Sylow 2 J.specialSubgroup => (V : Subgroup J.specialSubgroup)) hg
    change (R : Subgroup _).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup _).map κ.toMonoidHom at hh
    rwa [hR,hTA] at hh
  refine ⟨g,θ,?_,fun a => κ.apply_symm_apply _⟩
  have hinv : κ.symm.toMonoidHom.comp κ.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro a
    exact κ.symm_apply_apply a
  calc
    _ = ((((hermitianUnipotentSU J hJ).range.map (MulAut.conj g).toMonoidHom).map
        κ.symm.toMonoidHom).map (rankOne Q split j).subtype) := by
      simp only [MonoidHom.range_comp,map_map]
      rfl
    _ = ((A.map κ.toMonoidHom).map κ.symm.toMonoidHom).map (rankOne Q split j).subtype := by
      rw [hroot]
    _ = simpleRoot Q split j := by
      rw [map_map _ κ.symm.toMonoidHom κ.toMonoidHom,hinv,map_id]
      exact map_subgroupOf_eq_of_le (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)



omit [Finite E] in
private theorem root_mulVec (p : hermitianUnipotentCoord J) (v : Fin 3 → E) :
    Matrix.mulVec (hermitianUnipotentMatrix J p) v =
      ![v 0 + p.val.1*v 1 + p.val.2*v 2, v 1 + J.conj p.val.1*v 2, v 2] := by
  ext i
  fin_cases i <;> simp [hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,CharTwo.neg_eq,add_assoc]

include hE hfixed in
/-- The entire nonabelian root fixes exactly the first coordinate line,
including over the field with four elements. -/
theorem unitary_root_fixed_iff (v : Fin 3 → E) :
    (∀ p : hermitianUnipotentCoord J,
      Matrix.mulVec (hermitianUnipotentMatrix J p) v = v) ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro hv
    let z : hermitianUnipotentCoord J := ⟨(0,1),by simp [CharTwo.add_self_eq_zero]⟩
    have hz := congrFun (hv z) 0
    rw [root_mulVec] at hz
    change v 0 + 0*v 1 + 1*v 2 = v 0 at hz
    have hv2 : v 2 = 0 := by simpa only [zero_mul,add_zero,one_mul,add_eq_left] using hz
    obtain ⟨p,hp⟩ := BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd 1)
    have hp1 : p.val.1 = 1 := congrArg Multiplicative.toAdd hp
    have hh := congrFun (hv p) 0
    rw [root_mulVec] at hh
    change v 0 + p.val.1*v 1 + p.val.2*v 2 = v 0 at hh
    exact ⟨by simpa only [hp1,hv2,mul_zero,add_zero,one_mul,add_eq_left] using hh,hv2⟩
  · rintro ⟨h1,h2⟩ p
    rw [root_mulVec]
    ext i
    fin_cases i <;> simp [h1,h2]

section Natural
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Algebra (ZMod 2) E]

omit [Finite E] in
/-- Changing the basis by the inverse of the explicit inner conjugator
preserves every actor element and puts the pinned root in upper matrix form. -/
theorem natural_coordinates_conjugate
    (ρ : Representation (ZMod 2) (rankOne Q split j) V)
    (c : V ≃ₗ[ZMod 2] (Fin 3 → E))
    (hc : ∀ r v, c (ρ r v) = Matrix.mulVec (κ r).val.val (c v))
    (g : J.specialSubgroup) (θ : J.specialSubgroup ≃* rankOne Q split j)
    (hθ : ∀ a, κ (θ a) = g*a*g⁻¹) :
    ∃ d : V ≃ₗ[ZMod 2] (Fin 3 → E),
      (∀ a v, d (ρ (θ a) v) = Matrix.mulVec a.val.val (d v)) ∧
      ∀ p v, d (ρ (θ (hermitianUnipotentSU J hJ p)) v) =
        ![d v 0 + p.val.1 * d v 1 + p.val.2 * d v 2,
          d v 1 + J.conj p.val.1 * d v 2, d v 2] := by
  let d := c.trans (((Matrix.GeneralLinearGroup.toLin (g⁻¹).val).toLinearEquiv).restrictScalars (ZMod 2))
  have hd (v : V) : d v = Matrix.mulVec (g⁻¹).val.val (c v) := rfl
  have he (a : J.specialSubgroup) (v : V) :
      d (ρ (θ a) v) = Matrix.mulVec a.val.val (d v) := by
    rw [hd,hc,hθ,hd,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    have hmat : (g⁻¹).val.val * (g*a*g⁻¹).val.val = a.val.val * (g⁻¹).val.val := by
      change (g⁻¹ * (g*a*g⁻¹)).val.val = (a*g⁻¹).val.val
      congr 2
      group
    rw [hmat]
  refine ⟨d,he,fun p v => ?_⟩
  rw [he]
  change Matrix.mulVec (hermitianUnipotentMatrix J p) (d v) = _
  ext i
  fin_cases i <;>
    simp [hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,CharTwo.neg_eq,add_assoc]
end Natural


section SourceFixed
variable [Algebra (ZMod 2) E]
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (hroot : ((rankOne Q split j).subtype.comp
    (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j)
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (Representation.elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))

include hE hfixed hroot hc in
/-- The actual crossed linear root lies on the fixed line of the pinned
natural coordinates. This uses its source commutator, not a model tag. -/
theorem crossed_root_natural_line (hm : rotationOrder Q = 4)
    (i : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (v : simpleRemainder Q split j) (hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j)) :
    let w := c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
    w 1 = 0 ∧ w 2 = 0 := by
  dsimp only
  apply (unitary_root_fixed_iff J hE hfixed _).mp
  intro p
  let a := θ (hermitianUnipotentSU J hJ p)
  have ha : (a : X ⧸ Q.D) ∈ simpleRoot Q split j := hroot ▸ ⟨p,rfl⟩
  have hcomm : Commute (a : X ⧸ Q.D) (v : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (adjacent_roots_commute Q split hm j i hij.symm hVj hVi) ha) v hv).symm
  have hact : remainderRankOneAction Q split j hVj a v = v := by
    apply Subtype.ext
    rw [remainderRankOneAction_apply,hcomm.eq,mul_inv_cancel_right]
  have he := hc (hermitianUnipotentSU J hJ p)
    (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (Additive.ofMul (remainderFrattiniAction Q split j hVj a
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at he
  rw [remainderFrattiniAction_mk,hact] at he
  exact he.symm
end SourceFixed

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
