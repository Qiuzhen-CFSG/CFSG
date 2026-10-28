module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.NaturalCrossing

/-!
# Pinning the actual U₅ natural flag

The specified unitary reflection carries the crossed linear root onto the
simple linear root. Hence its natural image is an E-line, rather than
merely an additive subgroup of the correct order. An explicit upper-root
element clears that isotropic line to the last coordinate axis. Changing
the SU₃ actor and natural basis together preserves every actor element.
The same source reflection and the Hermitian pairing then force the entire
crossed unitary root onto the middle axis. The crossed linear root stays
on the first axis, and both noncentral coordinate labels are unchanged.

These statements keep the whole nonabelian roots and work in every positive
binary degree, including q=2 and q=4. They supply the natural flag used in
the original mixed-displacement calculation in NaturalFlagApplication.
Source: Fong--Seitz II (8C), (8.14)--(8.16), (8.24), pp.203--207.
The isotropic-column calculation adapts the repository's
CFSG/.../RankOneBorels/Unitary/RootGeneration/Bruhat.lean private
normalize_column proof, following Huppert II.10.12, to this lower layer.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure

section Matrix
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private theorem conj_conj (x : E) : J.conj (J.conj x) = x := J.conj_involutive x

include hJ in
private theorem column_pairing (g : J.specialSubgroup) (i j : Fin 3) :
    J.conj (g.val.val 2 i)*g.val.val 0 j +
      J.conj (g.val.val 1 i)*g.val.val 1 j +
      J.conj (g.val.val 0 i)*g.val.val 2 j = J.form i j := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j)
    ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  simpa [hJ,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_three] using h

/-- An explicit element of the full Hermitian root clears an isotropic
column with nonzero last entry. -/
theorem clear_unitary_column (g : J.specialSubgroup) (hc : g.val.val 2 0 ≠ 0) :
    ∃ p : hermitianUnipotentCoord J,
      ((hermitianUnipotentSU J hJ p)⁻¹*g).val.val 0 0 = 0 ∧
      ((hermitianUnipotentSU J hJ p)⁻¹*g).val.val 1 0 = 0 := by
  let x := g.val.val 0 0
  let y := g.val.val 1 0
  let c := g.val.val 2 0
  have hc' : c ≠ 0 := hc
  have hcc : J.conj c ≠ 0 := (map_ne_zero J.conj).2 hc
  have hi : J.conj c*x + J.conj y*y + J.conj x*c = 0 := by
    simpa [x,y,c,hJ] using column_pairing J hJ g 0 0
  have hp : x/c + J.conj (x/c) + (-J.conj (y/c))*J.conj (-J.conj (y/c)) = 0 := by
    simp only [map_div₀,map_neg,conj_conj,neg_mul_neg]
    field_simp [hc',hcc]
    linear_combination hi
  let p : hermitianUnipotentCoord J := ⟨(-J.conj (y/c),x/c),hp⟩
  refine ⟨p,?_,?_⟩
  all_goals rw [←map_inv]
  all_goals change (hermitianUnipotentMatrix J (hermitianUnipotentInv J p)*g.val.val) _ 0 = 0
  all_goals simp [hermitianUnipotentMatrix,hermitianUnipotentInv,p,
    Matrix.mul_apply,Fin.sum_univ_three,map_div₀,conj_conj]
  all_goals dsimp [x,y,c] at hi hc hcc ⊢
  · field_simp [hc,hcc]
    linear_combination hi
  · field_simp [hc,hcc]
    ring
end Matrix

variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  [Algebra (ZMod 2) E] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (j : Fin 2) (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (J : HermitianForm 3 E) (θ : J.specialSubgroup ≃* rankOne Q split j)
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))

/-- Change the natural basis by exactly the same inner unitary element
used to change the actor marking. -/
def unitaryBasisChange (g : J.specialSubgroup) :
    Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
      ≃ₗ[ZMod 2] (Fin 3 → E) :=
  c.trans (((Matrix.GeneralLinearGroup.toLin (g⁻¹).val).toLinearEquiv).restrictScalars (ZMod 2))

omit [Finite E] [CharP E 2] in
theorem unitaryBasisChange_section (g : J.specialSubgroup) (v : simpleRemainder Q split j) :
    (naturalSectionMap Q split j (unitaryBasisChange Q split j c J g) v).toAdd =
      Matrix.mulVec (g⁻¹).val.val (naturalSectionMap Q split j c v).toAdd := rfl

include hc in
omit [Finite E] [CharP E 2] in
theorem unitaryBasisChange_action (g a : J.specialSubgroup) (v) :
    unitaryBasisChange Q split j c J g
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
        (θ (g*a*g⁻¹)) v) = Matrix.mulVec a.val.val (unitaryBasisChange Q split j c J g v) := by
  change Matrix.mulVec (g⁻¹).val.val (c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ (g*a*g⁻¹)) v)) = _
  rw [hc]
  change Matrix.mulVec (g⁻¹).val.val (Matrix.mulVec (g*a*g⁻¹).val.val (c v)) =
    Matrix.mulVec a.val.val (Matrix.mulVec (g⁻¹).val.val (c v))
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  have he : (g⁻¹).val.val * (g*a*g⁻¹).val.val = a.val.val * (g⁻¹).val.val := by
    change (g⁻¹*(g*a*g⁻¹)).val.val = (a*g⁻¹).val.val
    congr 2
    group
  rw [he]

include hc in
omit [Finite E] [CharP E 2] in
private theorem flag_action (a : J.specialSubgroup) (v : simpleRemainder Q split j) :
    (naturalSectionMap Q split j c (remainderRankOneAction Q split j hVj (θ a) v)).toAdd =
      Matrix.mulVec a.val.val (naturalSectionMap Q split j c v).toAdd := by
  have he := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))
  change c (.ofMul (remainderFrattiniAction Q split j hVj (θ a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) v))) = _ at he
  rw [remainderFrattiniAction_mk] at he
  exact he

variable (hm : rotationOrder Q = 4) (i : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (t : RootReflection Q split j)
  {n : ℕ} (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hroot : ((rankOne Q split j).subtype.comp
    (θ.toMonoidHom.comp (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j)

local notation "N" => naturalSectionMap Q split j c
local notation "τ" => (Subtype.mk t.val t.mem_rankOne : rankOne Q split j)
local notation "m" => θ.symm τ⁻¹

include hc hm hij hVi t hE hfixed hJ hroot in
/-- The specified source reflection makes the full A image a single
E-line in the natural SU₃ section. -/
theorem simple_linear_natural_line (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split i) :
    ∃ z : E, ∀ a : Fin 3, (N v).toAdd a = (m).val.val a 0 * z := by
  let w := remainderRankOneAction Q split j hVj τ v
  have hw : (w : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    have hh := rootAt_right Q split i (Q.simple j) (Q.simple j) t.val t.class_eq
    have hsq : Q.simple j * Q.simple j = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
    rw [hsq,rootAt_one] at hh
    have ht := (SetLike.ext_iff.mp hh (v : X ⧸ Q.D)).mpr hv
    change (t.val : X ⧸ Q.D)*(v : X ⧸ Q.D)*(t.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split i (Q.simple j) at ht
    simpa only [w,remainderRankOneAction_apply] using ht
  have hwline := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
    hm i hij hVi w hw
  change (N w).toAdd 1 = 0 ∧ (N w).toAdd 2 = 0 at hwline
  have hact : remainderRankOneAction Q split j hVj (θ m) w = v := by
    rw [θ.apply_symm_apply]
    change remainderRankOneAction Q split j hVj τ⁻¹
      (remainderRankOneAction Q split j hVj τ v) = v
    rw [map_inv]
    exact (remainderRankOneAction Q split j hVj τ).symm_apply_apply v
  have he := flag_action Q split j hVj c J θ hc m w
  rw [hact] at he
  refine ⟨(N w).toAdd 0,fun a => ?_⟩
  rw [he]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hwline.1,hwline.2,mul_zero,add_zero]

include hc hm hij hVi t hE hfixed hJ hroot in
/-- One explicit upper-root basis change places the entire actual A root
on the last coordinate axis. Its last coordinate is unchanged. -/
theorem exists_natural_flag_basis
    (v₀ : simpleRemainder Q split j) (hv₀ : (v₀ : X ⧸ Q.D) ∈ simpleRoot Q split i)
    (hne : (N v₀).toAdd 2 ≠ 0) :
    ∃ p : hermitianUnipotentCoord J,
      let c' := unitaryBasisChange Q split j c J (hermitianUnipotentSU J hJ p)
      (∀ v : simpleRemainder Q split j,
        (naturalSectionMap Q split j c' v).toAdd 2 = (N v).toAdd 2) ∧
      ∀ v : simpleRemainder Q split j, (v : X ⧸ Q.D) ∈ simpleRoot Q split i →
        (naturalSectionMap Q split j c' v).toAdd = ![0,0,(N v).toAdd 2] := by
  obtain ⟨z,hz⟩ := simple_linear_natural_line Q split j hVj c J θ hc hm i hij hVi t
    hE hfixed hJ hroot v₀ hv₀
  have hm20 : (m).val.val 2 0 ≠ 0 := by
    intro hzero
    exact hne ((hz 2).trans (by rw [hzero,zero_mul]))
  obtain ⟨p,hp0,hp1⟩ := clear_unitary_column J hJ m hm20
  let u := hermitianUnipotentSU J hJ p
  have hlast (v : simpleRemainder Q split j) :
      (naturalSectionMap Q split j (unitaryBasisChange Q split j c J u) v).toAdd 2 = (N v).toAdd 2 := by
    rw [unitaryBasisChange_section]
    rw [←map_inv]
    change Matrix.mulVec (hermitianUnipotentMatrix J p⁻¹) (N v).toAdd 2 = _
    simp [hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  refine ⟨p,hlast,fun v hv => ?_⟩
  obtain ⟨z,hz⟩ := simple_linear_natural_line Q split j hVj c J θ hc hm i hij hVi t
    hE hfixed hJ hroot v hv
  have hvmat : (N v).toAdd = fun a => (m).val.val a 0*z := funext hz
  have hmvec (a : Fin 3) :
      (naturalSectionMap Q split j (unitaryBasisChange Q split j c J u) v).toAdd a =
        (u⁻¹*m).val.val a 0*z := by
    rw [unitaryBasisChange_section,hvmat]
    change Matrix.mulVec (u⁻¹).val.val (fun a => (m).val.val a 0*z) a =
      ((u⁻¹).val.val*(m).val.val) a 0*z
    simp only [Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_three]
    ring
  ext a
  fin_cases a
  · exact (hmvec 0).trans ((congrArg (fun x : E => x*z) hp0).trans (zero_mul z))
  · exact (hmvec 1).trans ((congrArg (fun x : E => x*z) hp1).trans (zero_mul z))
  · exact hlast v


include hc hm hij hVi t hE hfixed hJ hroot in
/-- Once the actual A line is the last axis, reflection and the Hermitian
form force the whole D image onto the middle axis. -/
theorem crossed_unitary_natural_axis
    (v₀ : simpleRemainder Q split j) (hv₀ : (v₀ : X ⧸ Q.D) ∈ simpleRoot Q split i)
    (hz₀ : (N v₀).toAdd 0 = 0) (hz₁ : (N v₀).toAdd 1 = 0)
    (hne : (N v₀).toAdd 2 ≠ 0)
    (v : simpleRemainder Q split j)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (N v).toAdd 0 = 0 ∧ (N v).toAdd 2 = 0 := by
  let a := θ.symm τ
  let w₀ := remainderRankOneAction Q split j hVj τ v₀
  have hw₀ : (w₀ : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    have hh := rootAt_right Q split i (Q.simple j) (Q.simple j) t.val t.class_eq
    have hsq : Q.simple j * Q.simple j = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
    rw [hsq,rootAt_one] at hh
    exact (SetLike.ext_iff.mp hh (v₀ : X ⧸ Q.D)).mpr hv₀
  obtain ⟨h1,h2⟩ := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
    hm i hij hVi w₀ hw₀
  change (N w₀).toAdd 1 = 0 at h1
  change (N w₀).toAdd 2 = 0 at h2
  have he₀ := flag_action Q split j hVj c J θ hc a v₀
  rw [θ.apply_symm_apply] at he₀
  have h12 : a.val.val 1 2 = 0 := by
    have hh := congrFun he₀ 1
    change (N w₀).toAdd 1 = _ at hh
    rw [h1] at hh
    have he : a.val.val 1 2 * (N v₀).toAdd 2 = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hz₀,hz₁] using hh.symm
    exact (mul_eq_zero.mp he).resolve_right hne
  have h22 : a.val.val 2 2 = 0 := by
    have hh := congrFun he₀ 2
    change (N w₀).toAdd 2 = _ at hh
    rw [h2] at hh
    have he : a.val.val 2 2 * (N v₀).toAdd 2 = 0 := by
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hz₀,hz₁] using hh.symm
    exact (mul_eq_zero.mp he).resolve_right hne
  have hp : J.conj (a.val.val 0 2)*a.val.val 2 0 = 1 := by
    simpa [hJ,h12,h22] using column_pairing J hJ a 2 0
  have ha : J.conj (a.val.val 0 2) ≠ 0 := (mul_ne_zero_iff.mp (hp ▸ one_ne_zero)).1
  have hb : a.val.val 2 0 ≠ 0 := (mul_ne_zero_iff.mp (hp ▸ one_ne_zero)).2
  have h21 : a.val.val 2 1 = 0 := by
    have hh : J.conj (a.val.val 0 2)*a.val.val 2 1 = 0 := by
      simpa [hJ,h12,h22] using column_pairing J hJ a 2 1
    exact (mul_eq_zero.mp hh).resolve_left ha
  let w := remainderRankOneAction Q split j hVj τ v
  have hw : (w : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) :=
    (SetLike.ext_iff.mp (cross_root_reflection_fixed Q split hm j i hij.symm t.val t.class_eq) _).mpr hv
  have hw2 := crossed_unitary_natural_plane Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc w hw
  have he := congrFun (flag_action Q split j hVj c J θ hc a v) 2
  rw [θ.apply_symm_apply] at he
  change (N w).toAdd 2 = _ at he
  rw [hw2] at he
  have hx : a.val.val 2 0 * (N v).toAdd 0 = 0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three,h21,h22] using he.symm
  exact ⟨(mul_eq_zero.mp hx).resolve_left hb,
    crossed_unitary_natural_plane Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc v hv⟩

omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
/-- Inner re-pinning of the full root preserves its noncentral coordinate. -/
theorem root_inner_first (p q : hermitianUnipotentCoord J) :
    (p*q*p⁻¹).val.1 = q.val.1 := by
  change (p.val.1+q.val.1)+(-p.val.1) = q.val.1
  abel

include hroot in
omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
/-- The same inner root change still covers the entire actual simple root. -/
theorem repinned_root_range (p : hermitianUnipotentCoord J) :
    ((rankOne Q split j).subtype.comp
      (((MulAut.conj (hermitianUnipotentSU J hJ p)).trans θ).toMonoidHom.comp
        (hermitianUnipotentSU J hJ))).range = simpleRoot Q split j := by
  have he : ((rankOne Q split j).subtype.comp
      (((MulAut.conj (hermitianUnipotentSU J hJ p)).trans θ).toMonoidHom.comp
        (hermitianUnipotentSU J hJ))) =
      ((rankOne Q split j).subtype.comp (θ.toMonoidHom.comp
        (hermitianUnipotentSU J hJ))).comp (MulAut.conj p).toMonoidHom := by
    ext q
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.trans_apply,
      MulAut.conj_apply,map_mul,map_inv]
  rw [he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (MulAut.conj p).surjective,←MonoidHom.range_eq_map,hroot]

include hc hm hij hVi hE hfixed hJ hroot in
/-- Upper-root re-pinning fixes the crossed linear coordinates exactly. -/
theorem root_basis_cross (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j) (hv : (v : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j)) :
    (naturalSectionMap Q split j (unitaryBasisChange Q split j c J (hermitianUnipotentSU J hJ p)) v).toAdd = (N v).toAdd := by
  obtain ⟨h1,h2⟩ := crossed_root_natural_line J hE hfixed hJ Q split j hVj θ hroot c hc
    hm i hij hVi v hv
  change (N v).toAdd 1 = 0 at h1
  change (N v).toAdd 2 = 0 at h2
  rw [unitaryBasisChange_section,←map_inv]
  change Matrix.mulVec (hermitianUnipotentMatrix J p⁻¹) (N v).toAdd = _
  ext a
  fin_cases a <;> simp [hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,h1,h2]

include hc hm hij hVi hE hfixed hJ hroot in
/-- Upper-root re-pinning leaves the whole D root's middle coordinate unchanged. -/
theorem root_basis_middle (p : hermitianUnipotentCoord J)
    (v : simpleRemainder Q split j) (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (naturalSectionMap Q split j (unitaryBasisChange Q split j c J (hermitianUnipotentSU J hJ p)) v).toAdd 1 = (N v).toAdd 1 := by
  have h2 := crossed_unitary_natural_plane Q split hm i j hij c J hE hfixed hJ hVi hVj θ hroot hc v hv
  rw [unitaryBasisChange_section,←map_inv]
  change Matrix.mulVec (hermitianUnipotentMatrix J p⁻¹) (N v).toAdd 1 = _
  simp [hermitianUnipotentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,h2]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
