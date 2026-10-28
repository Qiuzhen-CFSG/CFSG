module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.LinearAxes

/-!
# Multiplicative comparison of the actual U₅ natural sections

The intersection of the two source radicals is the product of the two
middle roots. On it, the constructed whole-root labels compare the SL₂
first coordinate and the SU₃ middle coordinate. Evaluate the same A–B
commutator in both natural modules: this yields a scalar intertwining
identity, forcing the common additive label to be a nonzero scalar times
a field isomorphism. It also pins the A-root bottom coordinate using that
same isomorphism. Both nonabelian roots and all positive binary degrees
are retained. No field compatibility is assumed.

The original-profile application constructs every local input in
CFSG's FieldApplication module. Center synchronization and the remaining
full root, Cartan and Weyl equations remain separate obligations.
Source: Fong--Seitz II (8C), pp.203--208, especially (8.15)--(8.16),
(8.21)--(8.23), (8.32)--(8.33). The root-product argument specializes the
ordered products already proved in QuadrangleStructure.RootCommutators.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped Pointwise MatrixGroups IsMulCommutative commutatorElement
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simple_sq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem simple_mul_cancel (i : Fin 2) (w : Weyl Q) :
    Q.simple i * (Q.simple i * w) = w := by
  rw [← mul_assoc, simple_sq, one_mul]
private theorem longest_four (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i * (Q.simple j * (Q.simple i * Q.simple j)) := by
  have h (b : Bool) := alternatingWord_longest Q b
  rw [hm] at h
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa [alternatingWord] using (h false).symm
  · simpa [alternatingWord] using (h true).symm
  · exact (hij rfl).elim

private theorem orderedRoots_three (hm : rotationOrder Q = 4) (b : Bool) :
    orderedRoots Q split b 3 =
      [simpleRoot Q split (if b then 1 else 0),
       rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)),
       rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1))] := by
  cases b <;> simp only [orderedRoots, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true, List.map_cons, List.map_nil]
  · change [simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 0) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 0 1 (by decide) _ (representative_spec _)]
  · change [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 1 0 (by decide) _ (representative_spec _)]

private theorem remainder_product (hm : rotationOrder Q = 4) (b : Bool) :
    (simpleRemainder Q split (if b then 0 else 1) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1)) : Set (X ⧸ Q.D)) := by
  have hprod := orderedRoots_product Q split b 3 (by omega)
  rw [orderedRoots_three Q split hm b] at hprod
  change (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) *
    ((rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1)) : Set (X ⧸ Q.D)) * 1)) = _ at hprod
  rw [mul_one, ← mul_assoc] at hprod
  have hs (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i := inv_eq_of_mul_eq_one_right (simple_sq Q i)
  have hw : longest Q * (alternatingWord Q b 3)⁻¹ = Q.simple (if b then 0 else 1) := by
    cases b
    · rw [longest_four Q hm 1 0 (by decide)]
      simp only [alternatingWord, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, mul_one, mul_inv_rev, hs, mul_assoc, simple_mul_cancel, simple_sq]
    · rw [longest_four Q hm 0 1 (by decide)]
      simp only [alternatingWord, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, mul_one, mul_inv_rev, hs, mul_assoc, simple_mul_cancel, simple_sq]
  rw [rootIntersection, hw] at hprod
  exact hprod.symm


/-- The intersection of the two actual radicals is the ordered product of
the two middle roots. This is also the collection boundary for the full
noncentral B–A displacement. -/
theorem radical_intersection_factors (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (v : X ⧸ Q.D)
    (hi : v ∈ simpleRemainder Q split i) (hj : v ∈ simpleRemainder Q split j) :
    ∃ d : rootAt Q split j (Q.simple i), ∃ c : rootAt Q split i (Q.simple j),
      v = (d : X ⧸ Q.D) * c := by
  have hp : (simpleRemainder Q split j : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
        (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact remainder_product Q split hm false
    · exact remainder_product Q split hm true
    · exact (hij rfl).elim
  change v ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) at hj
  rw [hp] at hj
  obtain ⟨_,⟨a,ha,d,hd,rfl⟩,c,hc,he⟩ := hj
  have hdc : d*c ∈ simpleRemainder Q split i := mul_mem
    ((opposite_roots_le_remainder Q split j i hij.symm).2 hd)
    (cross_root_le_own_remainder Q split hm i j hij hc)
  have hav : a ∈ simpleRemainder Q split i := by
    have hh := mul_mem hi (inv_mem hdc)
    have he' : v * (d*c)⁻¹ = a := by rw [←he]; dsimp only; group
    rwa [he'] at hh
  have ha1 : a = 1 := (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨ha,hav⟩
  exact ⟨⟨d,hd⟩,⟨c,hc⟩,by simpa only [ha1,one_mul] using he.symm⟩

/-- A scalar intertwining identity forces an additive bijection to be a
nonzero scalar times a field isomorphism. -/
theorem scalar_pairing_field {E K : Type*} [Field E] [Field K]
    (ψ : E ≃+ K) (β : K → E)
    (h : ∀ a x, ψ (x * β a) = a * ψ x) :
    ∃ ξ : E ≃+* K, ∀ x, ψ x = ψ 1 * ξ x := by
  have h1 : ψ 1 ≠ 0 := fun he => one_ne_zero (ψ.injective (he.trans ψ.map_zero.symm))
  have hb (a) : ψ (β a) = a * ψ 1 := by simpa only [one_mul] using h a 1
  have hsurj : Function.Surjective β := by
    intro y
    refine ⟨ψ y / ψ 1, ψ.injective ?_⟩
    rw [hb,div_mul_cancel₀ _ h1]
  have hm (x y) : ψ (x*y) = ψ x * ψ y / ψ 1 := by
    obtain ⟨a,rfl⟩ := hsurj y
    rw [h,hb]
    field_simp
  let ξ : E ≃+* K := {
    toFun := fun x => ψ x / ψ 1
    invFun := fun y => ψ.symm (y * ψ 1)
    left_inv := fun x => by dsimp only; rw [div_mul_cancel₀ _ h1,ψ.symm_apply_apply]
    right_inv := fun y => by dsimp only; rw [ψ.apply_symm_apply,mul_div_cancel_right₀ _ h1]
    map_add' := fun x y => by rw [map_add,add_div]
    map_mul' := fun x y => by rw [hm]; ring }
  exact ⟨ξ,fun x => (mul_div_cancel₀ (ψ x) h1).symm⟩


section Comparison
variable {E K : Type*} [Field E] [Finite E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) E] [Algebra (ZMod 2) K]
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ₀ : localGroup Q split i ≃* PSL(2,K))
  (c₂ : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
    ≃ₗ[ZMod 2] (Fin 2 → K))
  (hc₂ : ∀ a v, c₂ (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
    (alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c₂ v))
  (c₃ : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (J : HermitianForm 3 E) {n : ℕ}
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (hc₃ : ∀ a v, c₃ (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c₃ v))
  (ψ : E ≃+ K) (k : E) (hk : k ≠ 0)
  (hψ : ∀ p : hermitianUnipotentCoord J,
    linearSimpleCoordinate Q split i j hij c₂ (b p) = .ofAdd (ψ p.val.1) ∧
    linearCrossedCoordinate Q split i j hij c₂ (reflectedUnitaryChart Q split i j s b p) = .ofAdd (ψ p.val.1))
  (hδ : ∀ p : hermitianUnipotentCoord J,
    (naturalUnitaryCoordinate Q split hm i j hij c₃ (reflectedUnitaryChart Q split i j s b p)).toAdd =
      k*J.conj p.val.1)
  (hC : rootAt Q split i (Q.simple j) ≤ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆)

local notation "M" => linearNaturalSectionMap Q split i c₂
local notation "N" => naturalSectionMap Q split j c₃
local notation "A" => alignedSimpleParameter Q split i hVi μ₀ s
local notation "d" => reflectedUnitaryChart Q split i j s b

include hb in
omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
private theorem pinned_root_range :
    ((rankOne Q split j).subtype.comp
      (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    change (θ (hermitianUnipotentSU J hJ p) : X ⧸ Q.D) ∈ _
    rw [←hb]
    exact (b p).property
  · intro hy
    obtain ⟨p,hp⟩ := b.surjective ⟨y,hy⟩
    exact ⟨p,(hb p).symm.trans (congrArg Subtype.val hp)⟩

include hC in
omit [Finite K] [CharP K 2] in
private theorem linear_cross_zero (v : simpleRemainder Q split i)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j)) : M v = 1 := by
  have hh := hC hv
  rw [←map_subtype_commutator] at hh
  obtain ⟨w,hw,he⟩ := hh
  have hwv : w = v := Subtype.val_injective he
  subst w
  exact Abelianization.commutator_subset_ker M hw

include hm hE hfixed hVi hVj hb hc₃ hψ hδ hC in
omit [Finite K] [CharP K 2] in
private theorem intersection_coordinate (v : simpleRemainder Q split i)
    (w : simpleRemainder Q split j) (hvw : (v : X ⧸ Q.D) = w) :
    (N w).toAdd 1 = k*J.conj (ψ.symm ((M v).toAdd 0)) := by
  obtain ⟨D,C,he⟩ := radical_intersection_factors Q split hm i j hij v v.property (hvw ▸ w.property)
  obtain ⟨p,rfl⟩ := (d).surjective D
  let di := inclusion (opposite_roots_le_remainder Q split j i hij.symm).2 (d p)
  let ci := inclusion (cross_root_le_own_remainder Q split hm i j hij) C
  let dj := inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d p)
  let cj := inclusion (opposite_roots_le_remainder Q split i j hij).2 C
  have hv : v = di*ci := Subtype.ext he
  have hw : w = dj*cj := Subtype.ext (hvw.symm.trans he)
  have hci : M ci = 1 := linear_cross_zero Q split i j c₂ hC ci C.property
  have hcj : (N cj).toAdd 1 = 0 := (crossed_root_natural_line J hE hfixed hJ Q split j hVj θ
    (pinned_root_range Q split j J hJ θ b hb) c₃ hc₃ hm i hij hVi cj C.property).1
  have hdi : (M di).toAdd 0 = ψ p.val.1 := congrArg Multiplicative.toAdd (hψ p).2
  have hdj : (N dj).toAdd 1 = k*J.conj p.val.1 := hδ p
  simp only [hv,hw,map_mul,hci,mul_one,toAdd_mul,Pi.add_apply,hcj,add_zero,hdj,hdi,ψ.symm_apply_apply]

include hc₂ in
private theorem linear_action (a : SL(2,K)) (v : simpleRemainder Q split i) :
    (M (remainderRankOneAction Q split i hVi (alignedPinning Q split i hVi μ₀ s a) v)).toAdd =
      Matrix.mulVec a.val (M v).toAdd := by
  have ht := hc₂ a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v))
  change c₂ (.ofMul (remainderFrattiniAction Q split i hVi (alignedPinning Q split i hVi μ₀ s a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v))) = _ at ht
  rw [remainderFrattiniAction_mk] at ht
  exact ht

include hc₃ in
omit [Finite E] [CharP E 2] in
private theorem unitary_action (a : J.specialSubgroup) (v : simpleRemainder Q split j) :
    (N (remainderRankOneAction Q split j hVj (θ a) v)).toAdd =
      Matrix.mulVec a.val.val (N v).toAdd := by
  have ht := hc₃ a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c₃ (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at ht
  rw [remainderFrattiniAction_mk] at ht
  exact ht

/-- The specified linear root element, in the actual opposite unitary radical. -/
def linearRootInUnitaryRadical (a : K) : simpleRemainder Q split j :=
  ⟨A (.ofAdd a), (opposite_roots_le_remainder Q split i j hij).1
    (alignedSimpleParameter_range Q split i hVi μ₀ s ▸ ⟨.ofAdd a,rfl⟩)⟩

include hm hE hfixed hVi hVj hb hc₂ hc₃ hk hψ hδ hC in
private theorem mixed_scalar_pairing (a : K) (x : E) :
    ψ (x * J.conj ((N (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ a)).toAdd 2 / k)) = a * ψ x := by
  obtain ⟨p,hp⟩ := HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hE hfixed (.ofAdd x)
  have hp1 : p.val.1 = x := congrArg Multiplicative.toAdd hp
  let bv := inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 (b p)
  let av := linearRootInUnitaryRadical Q split i j hij hVi s μ₀ a
  let u : simpleRemainder Q split i :=
    remainderRankOneAction Q split i hVi (alignedPinning Q split i hVi μ₀ s (uni a)) bv * bv⁻¹
  let v : simpleRemainder Q split j :=
    (remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ p)) av * av⁻¹)⁻¹
  have huv : (u : X ⧸ Q.D) = v := by
    change (remainderRankOneAction Q split i hVi (alignedPinning Q split i hVi μ₀ s (uni a)) bv : X ⧸ Q.D) * (bv : X ⧸ Q.D)⁻¹ =
      ((remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ p)) av : X ⧸ Q.D) * (av : X ⧸ Q.D)⁻¹)⁻¹
    rw [remainderRankOneAction_apply,remainderRankOneAction_apply,←hb,alignedPinning_coe]
    change A (.ofAdd a)*(b p : X ⧸ Q.D)*(A (.ofAdd a))⁻¹*(b p : X ⧸ Q.D)⁻¹ =
      ((b p : X ⧸ Q.D)*A (.ofAdd a)*(b p : X ⧸ Q.D)⁻¹*(A (.ofAdd a))⁻¹)⁻¹
    group
  have hu : (M u).toAdd 0 = a*ψ x := by
    have hb1 : (M bv).toAdd 1 = ψ x := (congrArg Multiplicative.toAdd (hψ p).1).trans (congrArg ψ hp1)
    change (M (_ * bv⁻¹)).toAdd 0 = _
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,Pi.add_apply,Pi.neg_apply]
    rw [linear_action Q split i hVi s μ₀ c₂ hc₂]
    simp [uni_val,Matrix.mulVec,dotProduct,Fin.sum_univ_two,hb1]
  have hv : (N v).toAdd 1 = J.conj x * (N av).toAdd 2 := by
    change (N ((_ * av⁻¹)⁻¹)).toAdd 1 = _
    simp only [map_inv,map_mul,toAdd_mul,toAdd_inv,Pi.add_apply,Pi.neg_apply]
    rw [unitary_action Q split j hVj c₃ J θ hc₃]
    simp [hermitianUnipotentSU,hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,CharTwo.neg_eq,hp1]
    rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]
  have hh := intersection_coordinate Q split hm i j hij hVi hVj s c₂ c₃ J hE hfixed hJ θ b hb hc₃ ψ k hψ hδ hC u v huv
  rw [hu,hv] at hh
  have hy : ψ.symm (a*ψ x) = x * J.conj ((N av).toAdd 2 / k) := by
    apply J.conj.injective
    rw [map_mul J.conj x (J.conj ((N av).toAdd 2 / k)),J.conj_involutive,←mul_div_assoc]
    apply (eq_div_iff hk).mpr
    exact (mul_comm _ _).trans hh.symm
  apply ψ.symm.injective
  rw [ψ.symm_apply_apply]
  exact hy.symm

include hm hE hfixed hVi hVj hb hc₂ hc₃ hk hψ hδ hC in
/-- Comparing the same A–B commutator in the actual natural SL₂ and SU₃
sections makes their common additive label a scalar times a field equivalence. -/
theorem common_label_field :
    ∃ ξ : E ≃+* K, (∀ x, ψ x = ψ 1 * ξ x) ∧
      ∀ a : K, (N (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ a)).toAdd 2 =
        k * J.conj (ξ.symm a) := by
  let β := fun a => J.conj ((N (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ a)).toAdd 2 / k)
  have hp := mixed_scalar_pairing Q split hm i j hij hVi hVj s μ₀ c₂ hc₂ c₃ J hE hfixed hJ θ b hb hc₃ ψ k hk hψ hδ hC
  obtain ⟨ξ,hξ⟩ := scalar_pairing_field ψ β hp
  refine ⟨ξ,hξ,?_⟩
  intro a
  have hψ1 : ψ 1 ≠ 0 := fun he => one_ne_zero (ψ.injective (he.trans ψ.map_zero.symm))
  have hh := hp a 1
  change ψ (1*β a) = a*ψ 1 at hh
  rw [one_mul,hξ (β a),mul_comm a (ψ 1)] at hh
  have hh' : ξ (β a) = a := (mul_left_cancel₀ hψ1) hh
  have hb : β a = ξ.symm a := ξ.injective (hh'.trans (ξ.apply_symm_apply a).symm)
  have hc := congrArg J.conj hb
  change J.conj (J.conj ((N (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ a)).toAdd 2 / k)) = _ at hc
  rw [J.conj_involutive] at hc
  exact (div_eq_iff hk).mp hc |>.trans (mul_comm _ _)

include hc₂ in
/-- The A–B displacement in the actual linear Frattini section, for every
whole unitary-root element. The second coordinate vanishes exactly. -/
theorem linear_mixed_coordinates (a : K) (B : simpleRoot Q split j) :
    let v := inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 B
    (M (remainderRankOneAction Q split i hVi
      (alignedPinning Q split i hVi μ₀ s (uni a)) v * v⁻¹)).toAdd =
        ![a * (linearSimpleCoordinate Q split i j hij c₂ B).toAdd, 0] := by
  dsimp only
  simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
  rw [linear_action Q split i hVi s μ₀ c₂ hc₂]
  ext r
  fin_cases r <;> simp [uni_val,dotProduct,Fin.sum_univ_two,linearSimpleCoordinate]

end Comparison
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
