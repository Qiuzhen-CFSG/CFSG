module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.FixedFlag
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry

/-!
# Normalizing the descended graph-fixed flag in unitary dimension five

The identity bilinear form in characteristic two is the orthogonal sum of
an alternating four-space and the all-ones axis. Extend an independent
isotropic pair in the alternating part to a symplectic basis. This gives
one dot isometry normalizing an entire isotropic line-plane flag.

A fixed-field isometry extends to a unitary matrix over the original field,
and scalar extension retains both subspaces. Correcting a graph descent
basis by this fixed matrix preserves its graph equation and makes it
preserve the original flag. The Chapter6 consumer applies this construction
to a represented middle involution on the same projective extension.

Source: Aschbacher--Smith F.4.29(2), F.4.37(2), printed pp.289,293 of
refs/quasithin.pdf. This removes the flag-normalization premise; it does not
represent an arbitrary abstract automorphism as a unitary graph twist.
-/

public noncomputable section
open Matrix Module BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent.FlagNormalization
variable {K : Type*} [Field K] [CharP K 2]
local notation "V" => Matrix.PSp4Three.Vector 2 K

private def coordinates : (V × K) ≃ₗ[K] (Fin 5 → K) where
  toFun x := ![x.1 (.inl 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 0)+x.1 (.inr 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 1)+x.2, x.1 (.inl 1)+x.1 (.inr 1)+x.2,
    x.1 (.inr 0)+x.1 (.inr 1)+x.2]
  invFun v := (Sum.elim ![v 1+v 4,v 0+v 1+v 3+v 4] ![v 0+v 1,v 2+v 3],
    v 0+v 1+v 2+v 3+v 4)
  left_inv x := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> simp <;>
        ring_nf <;> simp [CharTwo.ofNat_eq_mod]
    · simp
      ring_nf
      simp [CharTwo.ofNat_eq_mod]
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

private theorem coordinates_dot (x y : V × K) :
    dotProduct (coordinates x) (coordinates y) =
      Matrix.PSp4Three.form x.1 y.1+x.2*y.2 := by
  simp [coordinates,dotProduct,Fin.sum_univ_succ,Matrix.PSp4Three.form_apply,
    CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]



private theorem coordinates_axis_zero (x : Fin 5 → K) (hx : dotProduct x x=0) :
    (coordinates.symm x).2=0 := by
  have hh := coordinates_dot (coordinates.symm x) (coordinates.symm x)
  rw [LinearEquiv.apply_symm_apply, hx, Matrix.PSp4Three.form_self,zero_add] at hh
  exact (mul_self_eq_zero.mp hh.symm)

/-- Extend an independent isotropic pair to an isometry of the identity form. -/
private theorem normalize_pair (x y : Fin 5 → K) (hx : x≠0)
    (hy : y∉Submodule.span K {x})
    (hxx : dotProduct x x=0) (hyy : dotProduct y y=0) (hxy : dotProduct x y=0) :
    ∃ a : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K),
      (∀ v w, dotProduct (a v) (a w)=dotProduct v w) ∧
      a x=![1,1,0,0,0] ∧ a y=![0,0,1,1,0] := by
  let u := (coordinates.symm x).1
  let v := (coordinates.symm y).1
  have hx0 := coordinates_axis_zero x hxx
  have hy0 := coordinates_axis_zero y hyy
  have hu : u≠0 := by
    intro he
    apply hx
    apply coordinates.symm.injective
    exact Prod.ext (by simpa only [map_zero,Prod.fst_zero] using he)
      (by simpa only [map_zero,Prod.snd_zero] using hx0)
  have hv : v∉Submodule.span K {u} := by
    intro he
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp he
    apply hy
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    apply coordinates.symm.injective
    rw [map_smul]
    exact Prod.ext hc (by simp [hx0,hy0])
  have huv : Matrix.PSp4Three.form u v=0 := by
    have he := coordinates_dot (coordinates.symm x) (coordinates.symm y)
    simpa only [LinearEquiv.apply_symm_apply,hxy,hx0,zero_mul,add_zero] using he.symm
  obtain ⟨g,hgx,hgy⟩ := Matrix.PSp4Three.exists_isometry_orthogonal_pair 0
    (Matrix.PSp4Three.form (n:=2) (F:=K)) Matrix.PSp4Three.form_alternating
    Matrix.PSp4Three.form_nondegenerate (by simp [Matrix.PSp4Three.Vector]) u v hu hv huv
  let a := (coordinates.symm.trans (g.toLinearEquiv.prodCongr (LinearEquiv.refl K K))).trans coordinates
  refine ⟨a,?_,?_,?_⟩
  · intro s t
    change dotProduct (coordinates (g (coordinates.symm s).1,(coordinates.symm s).2))
      (coordinates (g (coordinates.symm t).1,(coordinates.symm t).2))=dotProduct s t
    rw [coordinates_dot]
    simp only [g.map_app]
    rw [←coordinates_dot]
    simp
  · change coordinates (g u,(coordinates.symm x).2)=_
    rw [hgx,hx0]
    simp [coordinates,Matrix.PSp4Three.e]
  · change coordinates (g v,(coordinates.symm y).2)=_
    rw [hgy,hy0]
    simp [coordinates,Matrix.PSp4Three.e]


/-- Normalize an entire isotropic line-plane flag by a single dot isometry. -/
private theorem normalize_flag (L P : Submodule K (Fin 5 → K)) (hLP : L≤P)
    (hL : Module.finrank K L=1) (hP : Module.finrank K P=2)
    (hiso : ∀ x∈P, ∀ y∈P, dotProduct x y=0) :
    ∃ a : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K),
      (∀ v w, dotProduct (a v) (a w)=dotProduct v w) ∧
      L.map a.toLinearMap=line K ∧ P.map a.toLinearMap=plane K := by
  have hLb : L≠⊥ := by
    intro he
    have hh : Module.finrank K L=0 := by rw [he]; exact finrank_bot K (Fin 5 → K)
    omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLb
  have hn : ¬P≤L := by
    intro he
    have hh := Submodule.finrank_mono he
    rw [hL,hP] at hh
    omega
  obtain ⟨y,hy,hyL⟩ : ∃ y∈P, y∉L := by
    by_contra he
    push Not at he
    exact hn he
  have hyx : y∉Submodule.span K {x} := by
    rwa [←eq_span_singleton_of_mem_of_finrank_eq_one hL hx hx0]
  obtain ⟨a,ha,hax,hay⟩ := normalize_pair x y hx0 hyx
    (hiso x (hLP hx) x (hLP hx)) (hiso y hy y hy) (hiso x (hLP hx) y hy)
  refine ⟨a,ha,?_,?_⟩
  · apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro v hv
      change v 1=v 0 ∧ v 2=0 ∧ v 3=0 ∧ v 4=0 at hv
      have he : v=v 0 • (![1,1,0,0,0] : Fin 5 → K) := by
        ext i
        fin_cases i <;> simp_all
      rw [he,←hax]
      exact (L.map a.toLinearMap).smul_mem _ (Submodule.mem_map_of_mem hx)
    · rw [finrank_line,a.finrank_map_eq,hL]
  · apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro v hv
      change v 1=v 0 ∧ v 3=v 2 ∧ v 4=0 at hv
      have he : v=v 0 • (![1,1,0,0,0] : Fin 5 → K)+v 2 • ![0,0,1,1,0] := by
        ext i
        fin_cases i <;> simp_all
      rw [he,←hax,←hay]
      exact (P.map a.toLinearMap).add_mem
        ((P.map a.toLinearMap).smul_mem _ (Submodule.mem_map_of_mem (hLP hx)))
        ((P.map a.toLinearMap).smul_mem _ (Submodule.mem_map_of_mem hy))
    · rw [finrank_plane,a.finrank_map_eq,hP]


variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)
local notation "K₀" => FixedBy.subfield F J.conj

omit [CharP F 2] in
/-- Extend a fixed-field dot isometry to a unitary matrix over the original field. -/
private theorem extend_isometry (hJ : J.form=1)
    (a : (Fin 5 → K₀) ≃ₗ[K₀] (Fin 5 → K₀))
    (ha : ∀ x y, dotProduct (a x) (a y)=dotProduct x y) :
    ∃ u : J.unitarySubgroup,
      u.val.val.map J.conj=u.val.val ∧
      ∀ x : Fin 5 → K₀, unitaryLinear J u (fun i => (x i:F))=fun i => (a x i:F) := by
  let E : GL (Fin 5) K₀ ≃* ((Fin 5 → K₀) ≃ₗ[K₀] (Fin 5 → K₀)) :=
    GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K₀ (Fin 5 → K₀))
  let A := E.symm a
  have hA (x : Fin 5 → K₀) : A.val *ᵥ x=a x :=
    congrArg (fun z : (Fin 5 → K₀) ≃ₗ[K₀] (Fin 5 → K₀) => z x) (E.apply_symm_apply a)
  have horth : A.val.transpose*A.val=1 := by
    apply Matrix.ext
    intro i j
    have hh := ha (Pi.single i 1) (Pi.single j 1)
    simpa [←hA,Matrix.mulVec_single,dotProduct,Pi.single_apply,
      Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,eq_comm] using hh
  let B := GeneralLinearGroup.map (FixedBy.subfield F J.conj).subtype A
  have hfix : B.val.map J.conj=B.val := by
    ext i j
    exact (A.val i j).property
  have hB : B∈J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff,hJ,mul_one]
    change (B.val.map J.conj).transpose*B.val=1
    rw [hfix]
    change (A.val.map (FixedBy.subfield F J.conj).subtype).transpose*A.val.map (FixedBy.subfield F J.conj).subtype=1
    change (A.val.transpose.map (FixedBy.subfield F J.conj).subtype)*
      A.val.map (FixedBy.subfield F J.conj).subtype=1
    rw [←Matrix.map_mul,horth]
    exact map_one (FixedBy.subfield F J.conj).subtype.mapMatrix
  refine ⟨⟨B,hB⟩,hfix,?_⟩
  intro x
  change A.val.map (FixedBy.subfield F J.conj).subtype *ᵥ (fun i => (x i:F))=fun i => (a x i:F)
  have he := (FixedBy.subfield F J.conj).subtype.map_mulVec A.val x
  rw [hA] at he
  exact (funext he).symm

omit [CharP F 2] in
/-- Scalar extension intertwines a literal fixed-coordinate matrix action. -/
private theorem scalarSpan_map (u : J.unitarySubgroup)
    (a : (Fin 5 → K₀) ≃ₗ[K₀] (Fin 5 → K₀))
    (ha : ∀ x : Fin 5 → K₀, unitaryLinear J u (fun i => (x i:F))=fun i => (a x i:F))
    (W : Submodule K₀ (Fin 5 → K₀)) :
    FixedFlag.scalarSpan J (W.map a.toLinearMap)=
      (FixedFlag.scalarSpan J W).map (unitaryLinear J u).toLinearMap := by
  rw [FixedFlag.scalarSpan,FixedFlag.scalarSpan,Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨_,⟨y,hy,rfl⟩,ha y⟩
  · rintro ⟨z,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨a y,Submodule.mem_map_of_mem hy,(ha y).symm⟩

omit [CharP F 2] in
private theorem coordinates_line : FixedFlag.coordinates J (line F)=line K₀ := by
  ext x
  change ((x 1:F)=(x 0:F) ∧ (x 2:F)=0 ∧ (x 3:F)=0 ∧ (x 4:F)=0) ↔ _
  simp only [Subtype.coe_inj,ZeroMemClass.coe_eq_zero]
  rfl

omit [CharP F 2] in
private theorem coordinates_plane : FixedFlag.coordinates J (plane F)=plane K₀ := by
  ext x
  change ((x 1:F)=(x 0:F) ∧ (x 3:F)=(x 2:F) ∧ (x 4:F)=0) ↔ _
  simp only [Subtype.coe_inj,ZeroMemClass.coe_eq_zero]
  rfl

/-- A coefficient-stable isotropic flag can be normalized by a fixed unitary
matrix. Both subspace equations refer to the original field and native flag. -/
theorem normalize_stable_flag (hJ : J.form=1) (hσ : J.conj≠1)
    (L P : Submodule F (Fin 5 → F)) (hLP : L≤P)
    (hL : Module.finrank F L=1) (hP : Module.finrank F P=2)
    (hLc : ∀ x, J.conj ∘ x∈L ↔ x∈L)
    (hPc : ∀ x, J.conj ∘ x∈P ↔ x∈P)
    (hiso : ∀ x∈P, ∀ y∈P, IsotropicGeometry.pairing J x y=0) :
    ∃ u : J.unitarySubgroup, u.val.val.map J.conj=u.val.val ∧
      L.map (unitaryLinear J u).toLinearMap=line F ∧
      P.map (unitaryLinear J u).toLinearMap=plane F := by
  have hL₀ : Module.finrank K₀ (FixedFlag.coordinates J L)=1 := by
    rw [FixedFlag.finrank_coordinates J hσ L hLc,hL]
  have hP₀ : Module.finrank K₀ (FixedFlag.coordinates J P)=2 := by
    rw [FixedFlag.finrank_coordinates J hσ P hPc,hP]
  obtain ⟨a,ha,haL,haP⟩ := normalize_flag (FixedFlag.coordinates J L)
    (FixedFlag.coordinates J P) (FixedFlag.coordinates_mono J hLP) hL₀ hP₀
    (fun x hx y hy => FixedFlag.dot_zero J P hiso ⟨x,hx⟩ ⟨y,hy⟩)
  obtain ⟨u,huf,hu⟩ := extend_isometry J hJ a ha
  refine ⟨u,huf,?_,?_⟩
  · rw [←FixedFlag.scalarSpan_coordinates J hσ L hLc,←scalarSpan_map J u a hu,
      haL,←coordinates_line J,FixedFlag.scalarSpan_coordinates J hσ (line F) (conj_line J)]
  · rw [←FixedFlag.scalarSpan_coordinates J hσ P hPc,←scalarSpan_map J u a hu,
      haP,←coordinates_plane J,FixedFlag.scalarSpan_coordinates J hσ (plane F) (conj_plane J)]


omit [CharP F 2] in
/-- Fixed-coordinate unitary conjugation commutes with the standard graph action. -/
private theorem fixed_unitaryConj_commute (hJ : J.form=1) (u : J.unitarySubgroup)
    (hu : u.val.val.map J.conj=u.val.val) :
    Commute (unitaryConj J u) (GraphFixed.projectiveAut J hJ) := by
  have hu' : GeneralLinearGroup.map J.conj.toRingHom u.val=u.val := Units.ext hu
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [MulAut.mul_apply,unitaryConj_apply_val,projectiveAut_apply_val,
    map_mul,map_inv,Matrix.ProjGenLinGroup.map_mk,hu']

omit [CharP F 2] in
/-- Multiplying a graph conjugator by a fixed isometry retains its graph equation. -/
theorem conjugate_graph_fixed_correction (hJ : J.form=1) (v u : J.unitarySubgroup)
    (hu : u.val.val.map J.conj=u.val.val) :
    unitaryConj J (v*u⁻¹)*GraphFixed.projectiveAut J hJ*(unitaryConj J (v*u⁻¹))⁻¹ =
      unitaryConj J v*GraphFixed.projectiveAut J hJ*(unitaryConj J v)⁻¹ := by
  have hu1 : unitaryConj J (1:J.unitarySubgroup)=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp [unitaryConj_apply_val]
  have huinv : unitaryConj J u⁻¹=(unitaryConj J u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←unitaryConj_mul,inv_mul_cancel,hu1]
  rw [unitaryConj_mul,huinv]
  have hc := (fixed_unitaryConj_commute J hJ u hu).inv_left.eq
  calc
    _ = unitaryConj J v * ((unitaryConj J u)⁻¹*GraphFixed.projectiveAut J hJ) *
        unitaryConj J u*(unitaryConj J v)⁻¹ := by group
    _ = _ := by rw [hc]; group

omit [CharP F 2] in
/-- Correcting a pulled-back flag by its normalizing matrix makes the whole
coordinate change preserve the original subspace. -/
theorem correction_preserves (v u : J.unitarySubgroup)
    (W : Submodule F (Fin 5 → F))
    (hu : (W.comap (unitaryLinear J v).toLinearMap).map
      (unitaryLinear J u).toLinearMap=W) : Preserves J (v*u⁻¹) W := by
  intro x
  have he : unitaryLinear J (v*u⁻¹) x=
      unitaryLinear J v ((unitaryLinear J u).symm x) := by
    have hlin : unitaryLinear J u⁻¹=(unitaryLinear J u).symm := by
      apply LinearEquiv.ext
      intro y
      apply (unitaryLinear J u).injective
      rw [LinearEquiv.apply_symm_apply]
      change u.val.val *ᵥ ((u.val⁻¹).val *ᵥ y)=y
      rw [mulVec_mulVec,Units.mul_inv,one_mulVec]
    rw [←hlin]
    change (v.val*u.val⁻¹).val *ᵥ x=v.val.val *ᵥ ((u.val⁻¹).val *ᵥ x)
    rw [Units.val_mul,mulVec_mulVec]
  rw [he]
  change (unitaryLinear J u).symm x∈W.comap (unitaryLinear J v).toLinearMap ↔ x∈W
  conv_rhs => rw [←hu]
  exact (Submodule.mem_map_equiv _ (e:=unitaryLinear J u)).symm

end Theory.SpecificGroups.UnitaryFive.Descent.FlagNormalization
