module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalRootPinning

/-!
# Lifting the U₅ mixed-root equation from the natural section

The two middle roots have trivial intersection. Since the unitary radical's
Frattini subgroup is contained in the crossed unitary root, the crossed
linear root embeds in the natural section. Its fixed-line coordinates give
an isomorphism with the additive coefficient field, using its actual order.

For any element of the whole crossed unitary root, source commutation puts
its displacement under the whole simple unitary root in that linear root.
The natural SU₃ matrix action first forces its third coordinate to vanish,
then computes the displacement. Injectivity on the linear root lifts this
polynomial from the section to an exact product equation in the source group.
The proof retains both full nonabelian roots and works at q = 2 and q = 4.

Source: Fong--Seitz II (8.15)(ii)--(8.16), printed p.204. These native natural
coordinates still require comparison with the SL₂-derived coordinates
before they form the common labels of the full U₅ presentation.
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

include hm hij in
/-- The two middle root groups intersect trivially. -/
theorem crossed_roots_disjoint :
    Disjoint (rootAt Q split i (Q.simple j)) (rootAt Q split j (Q.simple i)) := by
  have hh := (simpleRoot_disjoint_remainder Q split i).mono_right
    (opposite_roots_le_remainder Q split j i hij.symm).2
  have he := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D))
    (disjoint_iff.mp hh)
  rw [rightConjugate_inf,←rootAt_eq Q split i (Q.simple j) _ (representative_spec _),
    cross_root_reflection_fixed Q split hm j i hij.symm _ (representative_spec _)] at he
  exact disjoint_iff.mpr (he.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]))

variable {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))

def naturalSectionMap : simpleRemainder Q split j →* Multiplicative (Fin 3 → E) where
  toFun v := .ofAdd (c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v)))
  map_one' := by simp
  map_mul' v w := by
    simp only [map_mul,ofMul_mul,map_add,ofAdd_add]

def naturalCrossCoordinate : rootAt Q split i (Q.simple j) →* Multiplicative E where
  toFun x := .ofAdd ((naturalSectionMap Q split j c
    ⟨x,(opposite_roots_le_remainder Q split i j hij).2 x.property⟩).toAdd 0)
  map_one' := by
    change Multiplicative.ofAdd ((naturalSectionMap Q split j c 1).toAdd 0) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd ((naturalSectionMap Q split j c
      (⟨x,(opposite_roots_le_remainder Q split i j hij).2 x.property⟩ *
        ⟨y,(opposite_roots_le_remainder Q split i j hij).2 y.property⟩)).toAdd 0) = _
    rw [map_mul]
    rfl

variable (J : HermitianForm 3 E) {n : ℕ}
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

include hm hE hfixed hVi hVj hroot hc hphi in
theorem naturalCrossCoordinate_injective :
    Function.Injective (naturalCrossCoordinate Q split i j hij c) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  let v : simpleRemainder Q split j :=
    ⟨x,(opposite_roots_le_remainder Q split i j hij).2 x.property⟩
  have h0 : c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v)) 0 = 0 :=
    congrArg Multiplicative.toAdd hx
  obtain ⟨h1,h2⟩ := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
    hm i hij hVi v x.property
  have hz : c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v)) = 0 := by
    ext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hq : QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v = 1 := by
    apply Additive.ofMul.injective
    exact c.injective (hz.trans c.map_zero.symm)
  have hp := hphi (mem_map_of_mem (simpleRemainder Q split j).subtype
    ((QuotientGroup.eq_one_iff v).mp hq))
  apply Subtype.ext
  exact (disjoint_iff.mp (crossed_roots_disjoint Q split hm i j hij)).le ⟨x.property,hp⟩

include hm hE hfixed hVi hVj hroot hc hphi in
def naturalCrossEquiv (hcard : Nat.card (simpleRoot Q split i) = Nat.card E) :
    rootAt Q split i (Q.simple j) ≃* Multiplicative E :=
  MulEquiv.ofBijective (naturalCrossCoordinate Q split i j hij c)
    ((naturalCrossCoordinate_injective Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi).bijective_of_nat_card_le
      (by simp only [rootAt,card_rightConjugate,hcard]; rfl))


include hc in
omit [Finite E] [CharP E 2] in
private theorem naturalSectionMap_action (a : J.specialSubgroup)
    (v : simpleRemainder Q split j) :
    (naturalSectionMap Q split j c (remainderRankOneAction Q split j hVj (θ a) v)).toAdd =
      Matrix.mulVec a.val.val (naturalSectionMap Q split j c v).toAdd := by
  have he := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at he
  rw [remainderFrattiniAction_mk] at he
  exact he

private def rootDisplacement (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j) : simpleRemainder Q split j :=
  remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ p)) v * v⁻¹

omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
private theorem rootDisplacement_val (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j) :
    (rootDisplacement Q split j J hJ hVj θ p v : X ⧸ Q.D) =
      ⁅(θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ := by
  change (remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ p)) v : X ⧸ Q.D) * v⁻¹ = _
  rw [remainderRankOneAction_apply]
  rfl

include hm hij hroot in
omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
private theorem rootDisplacement_mem (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (rootDisplacement Q split j J hJ hVj θ p v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
  rw [rootDisplacement_val]
  apply cross_root_commutator_le Q split hm j i hij.symm hVj
  exact commutator_mem_commutator (hroot ▸ ⟨p,rfl⟩) hv

include hc in
omit [Finite E] in
private theorem rootDisplacement_vector (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j) :
    (naturalSectionMap Q split j c (rootDisplacement Q split j J hJ hVj θ p v)).toAdd =
      ![p.val.1 * (naturalSectionMap Q split j c v).toAdd 1 +
          p.val.2 * (naturalSectionMap Q split j c v).toAdd 2,
        J.conj p.val.1 * (naturalSectionMap Q split j c v).toAdd 2, 0] := by
  change (naturalSectionMap Q split j c
    (remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ p)) v * v⁻¹)).toAdd = _
  rw [map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
  rw [naturalSectionMap_action Q split j c J hVj θ hc]
  ext k
  fin_cases k <;>
    simp [hermitianUnipotentSU,hermitianUnipotentMatrix,dotProduct,
      Fin.sum_univ_succ,CharTwo.neg_eq]

include hm hij hE hfixed hVi hroot hc in
/-- Every element of the whole crossed unitary root has third natural coordinate zero. -/
theorem crossed_unitary_natural_plane (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (naturalSectionMap Q split j c v).toAdd 2 = 0 := by
  obtain ⟨p,hp⟩ := BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd 1)
  have hp1 : p.val.1 = 1 := congrArg Multiplicative.toAdd hp
  have hk := rootDisplacement_mem Q split hm i j hij J hJ hVj θ hroot p v hv
  have hz := (crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
    hm i hij hVi (rootDisplacement Q split j J hJ hVj θ p v) hk).1
  change (naturalSectionMap Q split j c (rootDisplacement Q split j J hJ hVj θ p v)).toAdd 1 = 0 at hz
  rw [rootDisplacement_vector Q split j c J hJ hVj θ hc] at hz
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,hp1,map_one,one_mul] using hz

include hm hE hfixed hVi hroot hc hphi in
/-- The source commutator lifts the natural-section polynomial to an exact
product equation in the original quotient, with both full unitary roots. -/
theorem natural_unitary_crossing (hcard : Nat.card (simpleRoot Q split i) = Nat.card E)
    (p : hermitianUnipotentCoord J) (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D) * v =
      v * ((naturalCrossEquiv Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi hcard).symm
        (.ofAdd (p.val.1 * (naturalSectionMap Q split j c v).toAdd 1)) : X ⧸ Q.D) *
          (θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D) := by
  let k := rootDisplacement Q split j J hJ hVj θ p v
  have hk := rootDisplacement_mem Q split hm i j hij J hJ hVj θ hroot p v hv
  let e := naturalCrossEquiv Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc hphi hcard
  have he : e ⟨k,hk⟩ = .ofAdd (p.val.1 * (naturalSectionMap Q split j c v).toAdd 1) := by
    change Multiplicative.ofAdd ((naturalSectionMap Q split j c k).toAdd 0) = _
    rw [rootDisplacement_vector Q split j c J hJ hVj θ hc,
      crossed_unitary_natural_plane Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc v hv]
    simp
  have hek : ((e.symm (.ofAdd (p.val.1 * (naturalSectionMap Q split j c v).toAdd 1))) : X ⧸ Q.D) = k := by
    rw [←he,e.symm_apply_apply]
  rw [hek]
  have hcomm : Commute (k : X ⧸ Q.D) (v : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (middle_roots_commute Q split hm i j hij hVi hVj) hk) v hv).symm
  rw [←hcomm.eq,rootDisplacement_val]
  group

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
