module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FieldCompatibility

/-!
# Synchronizing the U₅ derived centers with the full root parameters

Evaluate the existing derived Hermitian B–A equation in the actual SU₃
natural section. The derived D term lies in the intrinsic center of the
crossed unitary root and therefore vanishes in that section. The remaining
C coordinate forces its field label to be multiplication by a single
nonzero fixed-field scalar. Varying the central B parameter identifies
its whole center by the same scalar; the specified reflection gives the
identical label on the opposite center.

The full nonabelian B and D charts are retained. The FieldApplication
constructor supplies the synchronized field and natural coordinates;
CenterApplication supplies the actual derived charts and both literal
marked/original source applications, including q=2 and q=4.
Source: Fong--Seitz II (8C), pp.206--207, comparison through (8.21)--(8.23).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

variable {X E F K : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  [Field F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) E] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ₀ : localGroup Q split i ≃* PSL(2,K))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (k : E) (hk : k ≠ 0)
  (hγ : ∀ a : E, naturalCrossCoordinate Q split i j hij c (γ (.ofAdd a)) = .ofAdd (k*J.conj a))
  (ξ : E ≃+* K)
  (hA : ∀ a : E, (naturalSectionMap Q split j c
    (linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (ξ a))).toAdd 2 = k*J.conj a)
  (hZ : _root_.commutator (simpleRoot Q split j) = center (simpleRoot Q split j))
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "FE" => fixedField J
local notation "FF" => Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField F σ
variable (r : PositiveMaps (X ⧸ Q.D) (Multiplicative F)
    (Multiplicative (FixedBy.subfield F σ))
    (Multiplicative F) (Multiplicative (FixedBy.subfield F σ)))
  (hr : FourPositive.Relations F σ hσ r)
  (α : F ≃+* K)
  (hrA : ∀ a : F, r.A (.ofAdd a) = alignedSimpleParameter Q split i hVi μ₀ s (.ofAdd (α a)))
  (hrB : r.B.range = (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype)
  (hrC : r.C.range = rootAt Q split i (Q.simple j))
  (hrD : r.D.range = (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype)

local notation "N" => naturalSectionMap Q split j c
local notation "ζ" => (α.trans ξ.symm)
local notation "B₀" => (fun z : FE => ((b (centralCoord J (Multiplicative.ofAdd z))) : X ⧸ Q.D))

include hn hE hfixed in
omit [Algebra (ZMod 2) E] in
private theorem central_chart_onto (v : center (simpleRoot Q split j)) :
    ∃ z : FE, B₀ z = v.val := by
  let p := b.symm v.val
  have hp : p ∈ center (hermitianUnipotentCoord J) := by
    apply mem_center_iff.mpr
    intro x
    apply b.injective
    simpa only [p,map_mul,b.apply_symm_apply] using mem_center_iff.mp v.property (b x)
  rw [binary_coord_center J hn hE hfixed] at hp
  obtain ⟨z,hz⟩ := hp
  refine ⟨z.toAdd,?_⟩
  have he := congrArg (fun p => (b p : X ⧸ Q.D)) hz
  simpa only [p,b.apply_symm_apply,ofAdd_toAdd] using he

include hm hij s hZ in
omit [Finite E] [CharP E 2] in
private theorem natural_center_zero (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype) :
    N v = 1 := by
  rw [←crossed_derived_center_eq Q split i j s hZ] at hv
  have hh := commutator_mono (cross_root_le_own_remainder Q split hm j i hij.symm)
    (cross_root_le_own_remainder Q split hm j i hij.symm) hv
  rw [←map_subtype_commutator] at hh
  obtain ⟨w,hw,he⟩ := hh
  have hwv : w = v := Subtype.val_injective he
  subst w
  exact Abelianization.commutator_subset_ker N hw

include hc in
omit [Finite E] [CharP E 2] in
private theorem center_unitary_action (a : J.specialSubgroup)
    (v : simpleRemainder Q split j) :
    (N (remainderRankOneAction Q split j hVj (θ a) v)).toAdd =
      Matrix.mulVec a.val.val (N v).toAdd := by
  have ht := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at ht
  rw [remainderFrattiniAction_mk] at ht
  exact ht

include hc in
omit [Finite E] in
private theorem central_action_top (t : FE) (v : simpleRemainder Q split j) :
    (N (remainderRankOneAction Q split j hVj
      (θ (hermitianUnipotentSU J hJ (centralCoord J (.ofAdd t)))) v)).toAdd 0 =
      (N v).toAdd 0 + (t:E)*(N v).toAdd 2 := by
  rw [center_unitary_action Q split j hVj c J θ hc]
  change Matrix.mulVec !![1,0,(t:E);0,1,-J.conj (0:E);0,0,1] (N v).toAdd 0 = _
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

include hb hr in
omit [Finite E] [Algebra (ZMod 2) E] [CharP F 2] in
private theorem central_action_collected (a : F) (z : FF) (t : FE)
    (av dv cv : simpleRemainder Q split j)
    (ha : (av : X ⧸ Q.D) = r.A (.ofAdd a))
    (hd : (dv : X ⧸ Q.D) = r.D (.ofAdd (FourPositive.normParameter F σ hσ a z)))
    (hcval : (cv : X ⧸ Q.D) = r.C (.ofAdd (a*(z:F))))
    (hzt : r.B (.ofAdd z) = B₀ t) :
    remainderRankOneAction Q split j hVj
      (θ (hermitianUnipotentSU J hJ (centralCoord J (.ofAdd t)))) av = av*dv*cv := by
  apply Subtype.ext
  rw [remainderRankOneAction_apply,←hb]
  change B₀ t*(av : X ⧸ Q.D)*(B₀ t)⁻¹ = (av : X ⧸ Q.D)*(dv : X ⧸ Q.D)*(cv : X ⧸ Q.D)
  rw [ha,hd,hcval,←hzt,hr.BA,mul_inv_cancel_right]

include r hm hb hc hγ hk hA hZ hr hrA hrC hrD in
omit [Finite E] [CharP F 2] in
/-- The central B–A equation compares the derived C coordinate with the
already synchronized SU₃/SL₂ field labels, without an assumed center label. -/
theorem derived_central_pairing (a : F) (z : FF) (t : FE)
    (hzt : r.B (.ofAdd z) = B₀ t) :
    r.C (.ofAdd (a*(z:F))) = (γ (.ofAdd (ζ a * (t:E))) : X ⧸ Q.D) := by
  have hDm (u : Multiplicative FF) : r.D u ∈ (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := hrD ▸ ⟨u,rfl⟩
  let av := linearRootInUnitaryRadical Q split i j hij hVi s μ₀ (α a)
  let dv : simpleRemainder Q split j := ⟨r.D (.ofAdd (FourPositive.normParameter F σ hσ a z)),
    cross_root_le_own_remainder Q split hm j i hij.symm
      (map_subtype_le _ (hDm (.ofAdd (FourPositive.normParameter F σ hσ a z))))⟩
  let cv : simpleRemainder Q split j := ⟨r.C (.ofAdd (a*(z:F))),
    (opposite_roots_le_remainder Q split i j hij).2 (hrC ▸ ⟨.ofAdd _,rfl⟩)⟩
  have hae : (av : X ⧸ Q.D) = r.A (.ofAdd a) := (hrA a).symm
  have he := central_action_collected Q split j hVj J hJ θ b hb σ hσ r hr
    a z t av dv cv hae rfl rfl hzt
  have hd0 : N dv = 1 := natural_center_zero Q split hm i j hij s c hZ dv (hDm _)
  have ha2 : (N av).toAdd 2 = k*J.conj (ζ a) := by
    have hh := hA (ζ a)
    simpa only [RingEquiv.trans_apply,ξ.apply_symm_apply] using hh
  have hact := central_action_top Q split j hVj c J hJ θ hc t av
  rw [he] at hact
  simp only [map_mul,hd0,mul_one,toAdd_mul,Pi.add_apply] at hact
  have hc0 : (N cv).toAdd 0 = (t:E)*(k*J.conj (ζ a)) := by
    rw [ha2] at hact
    exact add_left_cancel hact
  let c' : rootAt Q split i (Q.simple j) := ⟨r.C (.ofAdd (a*(z:F))),hrC ▸ ⟨.ofAdd _,rfl⟩⟩
  let u := (γ.symm c').toAdd
  have hu : γ (.ofAdd u) = c' := γ.apply_symm_apply c'
  have huc : k*J.conj u = (N cv).toAdd 0 := by
    have hh := congrArg Multiplicative.toAdd (hγ u)
    rw [hu] at hh
    exact hh.symm
  have hue : u = ζ a*(t:E) := by
    apply J.conj.injective
    apply mul_left_cancel₀ hk
    rw [huc,hc0,map_mul J.conj, fixedField_mem J t]
    ring
  have hv := congrArg Subtype.val hu
  rw [hue] at hv
  exact hv.symm


include r hm hn hE hfixed hb hc hγ hk hA hZ hr hrA hrB hrC hrD in
omit [CharP F 2] in
/-- The derived Hermitian charts and the two whole unitary charts differ
by exactly one nonzero fixed-field scalar, with the same scalar on both centers. -/
theorem derived_center_synchronization
    (hBinj : Function.Injective r.B)
    (hsB : ∀ z : FF, (s.val : X ⧸ Q.D)*r.B (.ofAdd z)*s.val = r.D (.ofAdd z)) :
    ∃ t : FE, t ≠ 0 ∧
      (∀ a : F, r.C (.ofAdd a) = (γ (.ofAdd ((t:E)*ζ a)) : X ⧸ Q.D)) ∧
      ∀ z : FF, ∃ u : FE, (u:E) = (t:E)*ζ (z:F) ∧
        r.B (.ofAdd z) = B₀ u ∧
        r.D (.ofAdd z) = (reflectedUnitaryChart Q split i j s b (centralCoord J (.ofAdd u)) : X ⧸ Q.D) := by
  have hlabel (z : FF) : ∃ t : FE, r.B (.ofAdd z) = B₀ t := by
    obtain ⟨v,hv,he⟩ := (show r.B (.ofAdd z) ∈ (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype from hrB ▸ ⟨.ofAdd z,rfl⟩)
    obtain ⟨t,ht⟩ := central_chart_onto Q split j J hn hE hfixed b ⟨v,hv⟩
    exact ⟨t,he.symm.trans ht.symm⟩
  obtain ⟨t,ht⟩ := hlabel 1
  have ht0 : t ≠ 0 := by
    intro hzero
    have he : r.B (.ofAdd (1 : FF)) = r.B 1 := by
      rw [ht,hzero,map_one]
      exact congrArg Subtype.val (b.map_one)
    have hh := congrArg Multiplicative.toAdd (hBinj he)
    exact one_ne_zero hh
  have hCparam (a : F) : r.C (.ofAdd a) = (γ (.ofAdd ((t:E)*ζ a)) : X ⧸ Q.D) := by
    have hh := derived_central_pairing Q split hm i j hij hVi hVj s μ₀ c J hJ θ b hb hc γ k hk hγ ξ hA hZ σ hσ r hr α hrA hrC hrD a 1 t ht
    simpa only [OneMemClass.coe_one,mul_one,mul_comm (ζ a)] using hh
  refine ⟨t,ht0,hCparam,fun z => ?_⟩
  obtain ⟨u,hu⟩ := hlabel z
  have hh := derived_central_pairing Q split hm i j hij hVi hVj s μ₀ c J hJ θ b hb hc γ k hk hγ ξ hA hZ σ hσ r hr α hrA hrC hrD 1 z u hu
  simp only [map_one,one_mul] at hh
  have he : (u:E) = (t:E)*ζ (z:F) := by
    have hx := γ.injective (Subtype.val_injective ((hCparam (z:F)).symm.trans hh))
    exact (congrArg Multiplicative.toAdd hx).symm
  refine ⟨u,he,hu,?_⟩
  rw [←hsB,hu,reflectedUnitaryChart_apply,
    inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i hVi μ₀ s)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
