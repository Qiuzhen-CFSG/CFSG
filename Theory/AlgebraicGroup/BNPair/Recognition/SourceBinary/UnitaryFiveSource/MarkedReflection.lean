module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RankOneBruhat
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MarkedWeyl

/-!
# The marked unitary reflection on the full U₅ source roots

The natural section identifies the supplied second reflection as an exchanger
of the two outer axes. Hermitian column pairings and determinant one factor
its SU₃ preimage as a diagonal times the fixed Weyl matrix. The diagonal is
already in the actual Cartan, so this Weyl matrix has the required marking.
Its natural action exchanges the entire A and C roots with their pinned
labels. A central-root SU₃ word removes the possible central correction on
D and proves that it fixes the whole nonabelian D root. The resulting two
normalizer lifts retain the supplied linear reflection and the same actor.
Source: Fong--Seitz II (8C), pp.203–210, through (8.37).
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

section Matrices
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hJ in
private theorem weyl_column_pairing (a : J.specialSubgroup) (x y : Fin 3) :
    J.conj (a.val.val 2 x)*a.val.val 0 y + J.conj (a.val.val 1 x)*a.val.val 1 y +
      J.conj (a.val.val 0 x)*a.val.val 2 y = J.form x y := by
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M x y)
    ((J.mem_specialSubgroup_iff a.val).mp a.property).1
  simpa [hJ,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_three] using he

private theorem unitary_axis_exchanger (a : J.specialSubgroup)
    (h00 : a.val.val 0 0 = 0) (h10 : a.val.val 1 0 = 0)
    (h12 : a.val.val 1 2 = 0) (h22 : a.val.val 2 2 = 0) :
    ∃ u : Eˣ, a = hermitianTorusSU J hJ u * hermitianWeylSU J hJ := by
  have hp : J.conj (a.val.val 2 0)*a.val.val 0 2 = 1 := by
    simpa [hJ,h00,h10] using weyl_column_pairing J hJ a 0 2
  have hu : a.val.val 2 0 ≠ 0 := by
    intro hz
    simp [hz] at hp
  have hc : J.conj (a.val.val 2 0) ≠ 0 := (map_ne_zero J.conj).mpr hu
  have hv : a.val.val 0 2 ≠ 0 := (mul_ne_zero_iff.mp (hp ▸ one_ne_zero)).2
  have h01 : a.val.val 0 1 = 0 := by
    have he : J.conj (a.val.val 2 0)*a.val.val 0 1 = 0 := by
      simpa [hJ,h00,h10] using weyl_column_pairing J hJ a 0 1
    exact (mul_eq_zero.mp he).resolve_left hc
  have h21 : a.val.val 2 1 = 0 := by
    have he : J.conj (a.val.val 0 2)*a.val.val 2 1 = 0 := by
      simpa [hJ,h12,h22] using weyl_column_pairing J hJ a 2 1
    exact (mul_eq_zero.mp he).resolve_left ((map_ne_zero J.conj).mpr hv)
  have h02 : a.val.val 0 2 = (J.conj (a.val.val 2 0))⁻¹ := eq_inv_of_mul_eq_one_right hp
  have hdet : a.val.val.det = 1 := by
    exact congrArg Units.val ((J.mem_specialSubgroup_iff a.val).mp a.property).2
  have hd : -(a.val.val 0 2 * a.val.val 1 1 * a.val.val 2 0) = 1 := by
    simpa [Matrix.det_fin_three,h00,h10,h12,h22,h01,h21] using hdet
  have h11 : a.val.val 1 1 = -(J.conj (a.val.val 2 0)*(a.val.val 2 0)⁻¹) := by
    rw [h02] at hd
    field_simp [hu,hc] at hd ⊢
    linear_combination -hd
  refine ⟨Units.mk0 (a.val.val 2 0) hu,?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  change a.val.val x y = (hermitianTorusMatrix J (Units.mk0 (a.val.val 2 0) hu) *
    hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) E) x y
  fin_cases x <;> fin_cases y <;>
    simp [hermitianTorusMatrix,hermitianWeylMatrix,Matrix.mul_apply,Fin.sum_univ_three,
      h00,h10,h12,h22,h01,h21,h02,h11]
end Matrices

variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
local notation "N" => naturalSectionMap Q split j c
variable (hA : ∀ a : E, (naturalSectionMap Q split j c
  (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])

include hc in
omit [CharP E 2] in
private theorem weyl_section_action (a : J.specialSubgroup) (v : simpleRemainder Q split j) :
    (N (remainderRankOneAction Q split j hVj (θ a) v)).toAdd = Matrix.mulVec a.val.val (N v).toAdd := by
  have he := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at he
  rw [remainderFrattiniAction_mk] at he
  exact he

include hA in
omit [CharP E 2] in
private theorem weyl_source_A_axis (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split i) :
    ∃ a : E, v = av a ∧ (N v).toAdd = ![0,0,k*J.conj a] := by
  rw [←alignedSimpleParameter_range Q split i hVi μ s] at hv
  obtain ⟨a,ha⟩ := hv
  let z := ξ.symm a.toAdd
  have he : v = av z := by
    apply Subtype.ext
    change (v : X ⧸ Q.D) = alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ z))
    rw [ξ.apply_symm_apply]
    exact ha.symm
  exact ⟨z,he,he.symm ▸ hA z⟩


variable (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (hC : ∀ a : E, (naturalSectionMap Q split j c (inclusion (opposite_roots_le_remainder Q split i j hij).2
    (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])
  (t : RootReflection Q split j)

include hc hk hA hC in
omit [CharP E 2] in
private theorem source_unitary_axis_exchanger :
    ∃ u : Eˣ, θ.symm ⟨t.val,t.mem_rankOne⟩ =
      hermitianTorusSU J hJ u * hermitianWeylSU J hJ := by
  let τ : rankOne Q split j := ⟨t.val,t.mem_rankOne⟩
  let a := θ.symm τ
  let v := remainderRankOneAction Q split j hVj τ (av 1)
  have hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    have he := rootAt_right Q split i (Q.simple j) (Q.simple j) t.val t.class_eq
    have hsq : Q.simple j * Q.simple j = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
    rw [hsq,rootAt_one] at he
    have hv0 : (av 1 : X ⧸ Q.D) ∈ simpleRoot Q split i :=
      alignedSimpleParameter_range Q split i hVi μ s ▸ ⟨_,rfl⟩
    exact (SetLike.ext_iff.mp he _).mpr hv0
  obtain ⟨z,hz⟩ := γ.surjective ⟨v,hv⟩
  have hvz : v = inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ z) :=
    Subtype.ext (congrArg Subtype.val hz).symm
  have hvec := weyl_section_action Q split j hVj J θ c hc a (av 1)
  rw [θ.apply_symm_apply] at hvec
  change (N v).toAdd = _ at hvec
  rw [hvz] at hvec
  change (N (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd z.toAdd)))).toAdd = _ at hvec
  rw [hC,hA,map_one,mul_one] at hvec
  have h12 : a.val.val 1 2 = 0 := by
    have he : a.val.val 1 2 * k = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three] using (congrFun hvec 1).symm
    exact (mul_eq_zero.mp he).resolve_right hk
  have h22 : a.val.val 2 2 = 0 := by
    have he : a.val.val 2 2 * k = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three] using (congrFun hvec 2).symm
    exact (mul_eq_zero.mp he).resolve_right hk
  let cv := inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd 1))
  let v' := remainderRankOneAction Q split j hVj τ cv
  have hv' : (v' : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    have he := (γ (.ofAdd 1)).property
    exact (SetLike.ext_iff.mp (rootAt_eq Q split i (Q.simple j) t.val t.class_eq) _).mp he
  obtain ⟨z',hz',hzv'⟩ := weyl_source_A_axis Q split i j hij hVi s μ J c ξ k hA v' hv'
  have hvec' := weyl_section_action Q split j hVj J θ c hc a cv
  rw [θ.apply_symm_apply] at hvec'
  change (N v').toAdd = _ at hvec'
  rw [hzv'] at hvec'
  change ![0,0,k*J.conj z'] = Matrix.mulVec a.val.val
    (N (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd 1)))).toAdd at hvec'
  rw [hC,map_one,mul_one] at hvec'
  have h00 : a.val.val 0 0 = 0 := by
    have he : a.val.val 0 0 * k = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three] using (congrFun hvec' 0).symm
    exact (mul_eq_zero.mp he).resolve_right hk
  have h10 : a.val.val 1 0 = 0 := by
    have he : a.val.val 1 0 * k = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three] using (congrFun hvec' 1).symm
    exact (mul_eq_zero.mp he).resolve_right hk
  exact unitary_axis_exchanger J hJ a h00 h10 h12 h22

include hc hk hA hC in
omit [CharP E 2] in
/-- The supplied source reflection differs from the SAME unitary Weyl image
by a torus element already proved to lie in the actual Cartan. -/
theorem unitaryWeyl_source_factor :
    ∃ u : Eˣ, (t.val : X ⧸ Q.D) = unitaryTorus Q split j J hJ θ u * unitaryWeyl Q split j J hJ θ := by
  obtain ⟨u,hu⟩ := source_unitary_axis_exchanger Q split i j hij hVi hVj s μ J hJ θ c hc ξ k hk hA γ hC t
  refine ⟨u,?_⟩
  have he := congrArg (fun a : J.specialSubgroup => (θ a : X ⧸ Q.D)) hu
  simpa [unitaryTorus,unitaryWeyl] using he

include hb hc hk hA hC t in
omit [CharP E 2] in
/-- The actual SU₃ Weyl image has the required normalizer marking. -/
theorem unitaryWeyl_marking :
    ∃ n : Q.tits.N, (n : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ ∧
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple j := by
  obtain ⟨u,hu⟩ := unitaryWeyl_source_factor Q split i j hij hVi hVj s μ J hJ θ c hc ξ k hk hA γ hC t
  have hh := unitaryTorus_mem_cartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA u
  let z : Q.tits.N := ⟨unitaryTorus Q split j J hJ θ u,hh.2⟩
  refine ⟨z⁻¹*t.val,?_,?_⟩
  · change (unitaryTorus Q split j J hJ θ u)⁻¹ * (t.val : X ⧸ Q.D) = _
    rw [hu,inv_mul_cancel_left]
  · have hz : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) z = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hh
    rw [map_mul,map_inv,hz,inv_one,one_mul,t.class_eq]

include hb hc hk hA hC t in
/-- The marked reflection whose value is precisely the fixed SU₃ Weyl image. -/
def unitaryReflection : RootReflection Q split j where
  val := (unitaryWeyl_marking Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).choose
  class_eq := (unitaryWeyl_marking Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).choose_spec.2
  mem_rankOne := by
    rw [(unitaryWeyl_marking Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).choose_spec.1]
    exact (θ (hermitianWeylSU J hJ)).property

include hb hc hk hA hC t in
omit [CharP E 2] in
theorem unitaryReflection_val :
    ((unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).val : X ⧸ Q.D) =
      unitaryWeyl Q split j J hJ θ :=
  (unitaryWeyl_marking Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).choose_spec.1

include hb hc hk hA hC t in
omit [CharP E 2] in
/-- The marked SU₃ Weyl image exchanges the two entire linear roots with
exactly their synchronized labels. -/
theorem unitaryWeyl_A (x : E) :
    unitaryWeyl Q split j J hJ θ * A x * unitaryWeyl Q split j J hJ θ =
      (γ (.ofAdd x) : X ⧸ Q.D) := by
  let w := unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw : (w.val : X ⧸ Q.D) = unitaryWeyl Q split j J hJ θ :=
    unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hw2 := unitaryWeyl_square Q split j J hJ θ
  have hwi : (unitaryWeyl Q split j J hJ θ)⁻¹ = unitaryWeyl Q split j J hJ θ :=
    inv_eq_of_mul_eq_one_right hw2
  let a := hermitianWeylSU J hJ
  let v := remainderRankOneAction Q split j hVj (θ a) (av x)
  have hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    have he := rootAt_right Q split i (Q.simple j) (Q.simple j) w.val w.class_eq
    have hsq : Q.simple j * Q.simple j = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
    rw [hsq,rootAt_one] at he
    have ha : (av x : X ⧸ Q.D) ∈ simpleRoot Q split i := by
      rw [←alignedSimpleParameter_range Q split i hVi μ s]
      exact ⟨Multiplicative.ofAdd (ξ x),rfl⟩
    have hh : (w.val : X ⧸ Q.D)*A x*(w.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split i (Q.simple j) :=
      (SetLike.ext_iff.mp he _).mpr ha
    rw [hw] at hh
    exact hh
  obtain ⟨z,hz⟩ := γ.surjective ⟨v,hv⟩
  have hvz : v = inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ z) :=
    Subtype.ext (congrArg Subtype.val hz).symm
  have hvec := weyl_section_action Q split j hVj J θ c hc a (av x)
  change (N v).toAdd = _ at hvec
  rw [hvz] at hvec
  change (N (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd z.toAdd)))).toAdd = _ at hvec
  rw [hC,hA] at hvec
  have hz' : z.toAdd = x := by
    apply J.conj.injective
    apply mul_left_cancel₀ hk
    simpa [a,hermitianWeylSU,hermitianWeylGL,hermitianWeylMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
      using congrFun hvec 0
  have he := congrArg Subtype.val hvz
  rw [remainderRankOneAction_apply] at he
  change unitaryWeyl Q split j J hJ θ * A x * (unitaryWeyl Q split j J hJ θ)⁻¹ =
    (γ (.ofAdd z.toAdd) : X ⧸ Q.D) at he
  rwa [hwi,hz'] at he

include hb hc hk hA hC t in
omit [CharP E 2] in
theorem unitaryWeyl_C (x : E) :
    unitaryWeyl Q split j J hJ θ * (γ (.ofAdd x) : X ⧸ Q.D) * unitaryWeyl Q split j J hJ θ = A x := by
  rw [←unitaryWeyl_A Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t x]
  have hw := unitaryWeyl_square Q split j J hJ θ
  calc
    _ = (unitaryWeyl Q split j J hJ θ * unitaryWeyl Q split j J hJ θ) * A x *
      (unitaryWeyl Q split j J hJ θ * unitaryWeyl Q split j J hJ θ) := by group
    _ = _ := by rw [hw,one_mul,mul_one]

section WholeD
variable (hm : rotationOrder Q = 4)
  (hrel : Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive.Relations (fiveForm J)
    (synchronizedRoots Q split i j hVi s μ J b γ ξ))

private def centralWeylParameter : hermitianUnipotentCoord J :=
  ⟨(0,1),by simp [CharTwo.add_self_eq_zero]⟩

include hb in
omit [Algebra (ZMod 2) E] in
/-- The fixed SU₃ Weyl element is a word in a central-root involution and
its opposite. This identity is in SU₃, including its scalar center. -/
private theorem unitaryWeyl_central_word :
    let z := (b (centralWeylParameter J) : X ⧸ Q.D)
    let w := unitaryWeyl Q split j J hJ θ
    z*(w*z*w)*z = w := by
  have he : hermitianUnipotentSU J hJ (centralWeylParameter J) *
      (hermitianWeylSU J hJ * hermitianUnipotentSU J hJ (centralWeylParameter J) * hermitianWeylSU J hJ) *
        hermitianUnipotentSU J hJ (centralWeylParameter J) = hermitianWeylSU J hJ := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro x y
    change (hermitianUnipotentMatrix J (centralWeylParameter J) *
      (hermitianWeylMatrix * hermitianUnipotentMatrix J (centralWeylParameter J) * hermitianWeylMatrix) *
        hermitianUnipotentMatrix J (centralWeylParameter J) : Matrix (Fin 3) (Fin 3) E) x y = hermitianWeylMatrix x y
    fin_cases x <;> fin_cases y <;>
      simp [centralWeylParameter,hermitianUnipotentMatrix,hermitianWeylMatrix,
        Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero,CharTwo.neg_eq]
  dsimp only
  rw [hb]
  simpa [unitaryWeyl] using congrArg (fun a : J.specialSubgroup => (θ a : X ⧸ Q.D)) he

include hb hc hk hA hC hm hrel t in
/-- The unitary Weyl image fixes the WHOLE crossed unitary root. Its
central-root word eliminates the possible central correction directly. -/
theorem unitaryWeyl_D (p : hermitianUnipotentCoord J) :
    unitaryWeyl Q split j J hJ θ * (reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D) *
      unitaryWeyl Q split j J hJ θ = reflectedUnitaryChart Q split i j s b p := by
  let w := unitaryWeyl Q split j J hJ θ
  let z := (b (centralWeylParameter J) : X ⧸ Q.D)
  let D := rootAt Q split j (Q.simple i)
  let δ := reflectedUnitaryChart Q split i j s b
  have hw2 : w*w=1 := unitaryWeyl_square Q split j J hJ θ
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right hw2
  have hz (d : X ⧸ Q.D) (hd : d ∈ D) : Commute z d := by
    obtain ⟨q,hq⟩ := δ.surjective ⟨d,hd⟩
    have hq' : (δ q : X ⧸ Q.D) = d := congrArg Subtype.val hq
    rw [←hq']
    have he := hrel.BD (centralWeylParameter J) q
    change z*(δ q : X ⧸ Q.D) = (δ q : X ⧸ Q.D)*
      (γ (.ofAdd (q.val.1 * J.conj (centralWeylParameter J).val.1)) : X ⧸ Q.D)*z at he
    change z*(δ q : X ⧸ Q.D) = (δ q : X ⧸ Q.D)*z
    simpa [centralWeylParameter] using he
  let wt := unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hwt : (wt.val : X ⧸ Q.D) = w :=
    unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t
  have hnorm (d : X ⧸ Q.D) (hd : d ∈ D) : w*d*w ∈ D := by
    have he := (SetLike.ext_iff.mp
      (cross_root_reflection_fixed Q split hm j i hij.symm wt.val wt.class_eq) d).mpr hd
    change (wt.val : X ⧸ Q.D)*d*(wt.val : X ⧸ Q.D)⁻¹ ∈ D at he
    rwa [hwt,hwi] at he
  have hz' : Commute (w*z*w) (δ p : X ⧸ Q.D) := by
    have he := congrArg (MulAut.conj w) (hz (w*(δ p : X ⧸ Q.D)*w) (hnorm _ (δ p).property)).eq
    have hc : MulAut.conj w (w*(δ p : X ⧸ Q.D)*w) = δ p := by
      change w*(w*(δ p : X ⧸ Q.D)*w)*w⁻¹ = δ p
      rw [hwi]
      calc
        _ = (w*w)*(δ p : X ⧸ Q.D)*(w*w) := by group
        _ = _ := by rw [hw2,one_mul,mul_one]
    rw [map_mul (MulAut.conj w) z (w*(δ p : X ⧸ Q.D)*w),
      map_mul (MulAut.conj w) (w*(δ p : X ⧸ Q.D)*w) z,hc] at he
    change (w*z*w)*(δ p : X ⧸ Q.D) = (δ p : X ⧸ Q.D)*(w*z*w)
    simpa only [MulAut.conj_apply,hwi] using he
  have hw : Commute w (δ p : X ⧸ Q.D) := by
    have he : z*(w*z*w)*z = w := unitaryWeyl_central_word Q split j J hJ θ b hb
    rw [←he]
    exact ((hz _ (δ p).property).mul_left hz').mul_left (hz _ (δ p).property)
  change w*(δ p : X ⧸ Q.D)*w = δ p
  rw [hw.eq,mul_assoc,hw2,mul_one]
end WholeD

open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation

include hb hc hk hA hC t in
/-- The actual source reflections, with the unitary endpoint as marked index. -/
def synchronizedWeylLifts : MarkedWeyl.Lifts Q j where
  s := s.val
  t := (unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).val
  s_class := by
    have hi : i = 1-j := by
      fin_cases i <;> fin_cases j <;> first | rfl | exact (hij rfl).elim
    simpa only [←hi] using s.class_eq
  t_class := (unitaryReflection Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).class_eq

include hb hc hk hA hC t in
omit [CharP E 2] in
@[simp] theorem synchronizedWeylLifts_s :
    (synchronizedWeylLifts Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).s = s.val := rfl

include hb hc hk hA hC t in
omit [CharP E 2] in
@[simp] theorem synchronizedWeylLifts_t :
    ((synchronizedWeylLifts Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t).t : X ⧸ Q.D) =
      unitaryWeyl Q split j J hJ θ :=
  unitaryReflection_val Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA γ hC t

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
