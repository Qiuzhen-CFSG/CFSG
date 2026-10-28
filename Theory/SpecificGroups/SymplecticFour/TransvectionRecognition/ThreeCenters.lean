module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionFusion
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Theory.Representation.Quotient

/-!
# Three transvection centers in the actual point-local group

The orbit of a nonzero transvection center under an F-irreducible subgroup
spans the natural four-space. Nondegeneracy gives a second center with nonzero
pairing, and the dimension bound gives a third outside their plane. Their
three-space has a one-dimensional perpendicular fixed by all three conjugate
transvections. An actual symplectic change of frame carries this point to e0
and places the generated subgroup in the literal pointLocal matrix group.

The configuration retains its conjugating elements, center vectors, common
fixed point and local embedding. Normalization supplies the exact coset aX.
This proves the opening geometry of Aschbacher--Smith G.4.9, printed p.341;
the subsequent Dickson/radical lift producing a C2 element is separate.
-/

@[expose] public noncomputable section
open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem exists_orbit_three_centers (X : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp X.subtype))
    (u : Vector F) (hu : u≠0) :
    ∃ x y : X, form F u ((x : Sp F) • u)≠0 ∧
      (y : Sp F) • u ∉ Submodule.span F (Set.range ![u,(x : Sp F) • u]) := by
  classical
  let ρ : Representation F X (Vector F) := (Representation.symplecticNatural 2).comp X.subtype
  let : ρ.IsIrreducible := hi
  have hspan := Representation.TraceFieldDescent.span_orbit_eq_top ρ u hu
  obtain ⟨x,hx⟩ : ∃ x : X, form F u (ρ x u)≠0 := by
    by_contra! hz
    have hle : Submodule.span F (Set.range (fun x => ρ x u))≤LinearMap.ker (form F u) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,rfl⟩
      exact hz x
    rw [hspan] at hle
    exact hu (TwoLocalCover.form_nondegenerate.1 u (fun v => hle (Submodule.mem_top)))
  let U := Submodule.span F (Set.range ![u,ρ x u])
  have hdim : finrank F U≤2 := by
    simpa only [Set.finrank,U,Fintype.card_fin] using finrank_range_le_card ![u,ρ x u]
  obtain ⟨y,hy⟩ : ∃ y : X, ρ y u∉U := by
    by_contra! hz
    have hle : Submodule.span F (Set.range (fun x => ρ x u))≤U :=
      Submodule.span_le.mpr (by rintro _ ⟨y,rfl⟩; exact hz y)
    rw [hspan] at hle
    have he : U=⊤ := top_unique hle
    rw [he,finrank_top] at hdim
    have hd : finrank F (Vector F)=4 := by simp [Vector]
    omega
  exact ⟨x,y,hx,hy⟩

omit [CharP F 2] in
theorem exists_common_orthogonal (u v w : Vector F) :
    ∃ p : Vector F, p≠0 ∧ form F u p=0 ∧ form F v p=0 ∧ form F w p=0 := by
  classical
  let U := Submodule.span F (Set.range ![u,v,w])
  have hdim : finrank F U≤3 := by
    simpa only [Set.finrank,U,Fintype.card_fin] using finrank_range_le_card ![u,v,w]
  have hn : (form F).orthogonal U≠⊥ := by
    intro hz
    have hd := (form F).finrank_orthogonal TwoLocalCover.form_nondegenerate (W:=U)
    rw [hz,finrank_bot] at hd
    have hv : finrank F (Vector F)=4 := by simp [Vector]
    omega
  obtain ⟨p,hp,hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact ⟨p,hp0,hp u (Submodule.subset_span ⟨0,rfl⟩),
    hp v (Submodule.subset_span ⟨1,rfl⟩),hp w (Submodule.subset_span ⟨2,rfl⟩)⟩

omit [CharP F 2] in
theorem rank_one_formula_conjugate (a g : Sp F) (u : Vector F) (c : F)
    (ha : ∀ v, a • v=v+(c*form F u v) • u) :
    ∀ v, (g*a*g⁻¹) • v=v+(c*form F (g • u) v) • (g • u) := by
  intro v
  have hp : form F u (g⁻¹ • v)=form F (g • u) v := by
    simpa only [smul_inv_smul] using (preserves_form g u (g⁻¹ • v)).symm
  rw [mul_smul,mul_smul,ha]
  have hlin : g • (g⁻¹ • v+(c*form F u (g⁻¹ • v)) • u)=
      g • (g⁻¹ • v)+(c*form F u (g⁻¹ • v)) • (g • u) := by
    change toLinear g (g⁻¹ • v+(c*form F u (g⁻¹ • v)) • u)=_
    rw [map_add,(toLinear g).map_smul (c*form F u (g⁻¹ • v)) u]
    rfl
  rw [hlin,smul_inv_smul,hp]

/-- The actual three-center geometry, with a literal point-local embedding. -/
structure ThreeCenterConfiguration (X : Subgroup (Sp F)) (a : Sp F) where
  x : X
  y : X
  center : Vector F
  center_ne_zero : center≠0
  parameter : F
  parameter_ne_zero : parameter≠0
  formula : ∀ v, a • v=v+(parameter*form F center v) • center
  pairing_ne_zero : form F center ((x : Sp F) • center)≠0
  third_outside : (y : Sp F) • center ∉
    Submodule.span F (Set.range ![center,(x : Sp F) • center])
  point : Vector F
  point_ne_zero : point≠0
  first_fixes : a • point=point
  second_fixes : ((x : Sp F)*a*(x : Sp F)⁻¹) • point=point
  third_fixes : ((y : Sp F)*a*(y : Sp F)⁻¹) • point=point
  frame : Sp F
  frame_point : frame • point=e 0
  local_containment :
    (closure {a,(x : Sp F)*a*(x : Sp F)⁻¹,(y : Sp F)*a*(y : Sp F)⁻¹}).map
      (MulAut.conj frame).toMonoidHom≤pointLocal

omit [CharP F 2] in
/-- An irreducible subgroup supplies the marked three-center configuration
for every ambient transvection. -/
theorem exists_threeCenterConfiguration (X : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp X.subtype))
    (a : Sp F) (ha : IsB1 a) : Nonempty (ThreeCenterConfiguration X a) := by
  obtain ⟨u,c,hu,hc,haform⟩ := rank_one_formula a ha
  obtain ⟨x,y,hx,hy⟩ := exists_orbit_three_centers X hi u hu
  obtain ⟨p,hp,hup,hxp,hyp⟩ := exists_common_orthogonal u ((x : Sp F) • u) ((y : Sp F) • u)
  have hfa : a • p=p := by rw [haform,hup,mul_zero,zero_smul,add_zero]
  have hfx : ((x : Sp F)*a*(x : Sp F)⁻¹) • p=p := by
    rw [rank_one_formula_conjugate a x u c haform,hxp,mul_zero,zero_smul,add_zero]
  have hfy : ((y : Sp F)*a*(y : Sp F)⁻¹) • p=p := by
    rw [rank_one_formula_conjugate a y u c haform,hyp,mul_zero,zero_smul,add_zero]
  have he : e (F:=F) 0≠0 := by
    intro hz
    have hh := congrFun hz (.inl 0)
    exact one_ne_zero (by simpa only [e,Pi.single_eq_same,Pi.zero_apply] using hh)
  obtain ⟨k,hk⟩ := TwoLocalCover.nonzero_vector_transitive hp he
  have hle : closure {a,(x : Sp F)*a*(x : Sp F)⁻¹,(y : Sp F)*a*(y : Sp F)⁻¹}≤
      MulAction.stabilizer (Sp F) p := by
    rw [closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact hfa
    · exact hfx
    · exact hfy
  refine ⟨{
    x:=x
    y:=y
    center:=u
    center_ne_zero:=hu
    parameter:=c
    parameter_ne_zero:=hc
    formula:=haform
    pairing_ne_zero:=hx
    third_outside:=hy
    point:=p
    point_ne_zero:=hp
    first_fixes:=hfa
    second_fixes:=hfx
    third_fixes:=hfy
    frame:=k
    frame_point:=hk
    local_containment:=?_ }⟩
  rw [map_le_iff_le_comap]
  intro g hg
  apply (mem_pointLocal_iff_fixed _).mpr
  change (k*g*k⁻¹) • e 0=e 0
  rw [←hk,mul_smul,mul_smul,inv_smul_smul]
  change k • (g • p)=k • p
  rw [show g • p=p from hle hg]

namespace ThreeCenterConfiguration
variable {X : Subgroup (Sp F)} {a : Sp F}

/-- The first two marked transvections really do not commute. -/
theorem second_noncommuting (D : ThreeCenterConfiguration X a) :
    ¬Commute a ((D.x : Sp F)*a*(D.x : Sp F)⁻¹) := by
  intro hcomm
  let v := (D.x : Sp F) • D.center
  have hv : v≠0 := by
    change (toLinear (D.x : Sp F)) D.center≠0
    exact (map_ne_zero_iff _ (toLinear (D.x : Sp F)).injective).mpr D.center_ne_zero
  have hf := fixes_center_of_commute a ((D.x : Sp F)*a*(D.x : Sp F)⁻¹)
    D.center D.parameter D.center_ne_zero D.parameter_ne_zero D.formula hcomm.symm
  rw [rank_one_formula_conjugate a D.x D.center D.parameter D.formula] at hf
  have hz : (D.parameter*form F v D.center) • v=0 := by
    exact add_left_cancel (hf.trans (add_zero D.center).symm)
  have hz' := (smul_eq_zero.mp hz).resolve_right hv
  have hform := (mul_eq_zero.mp hz').resolve_left D.parameter_ne_zero
  apply D.pairing_ne_zero
  exact TwoLocalCover.form_alternating.isRefl _ _ hform

omit [CharP F 2] in
/-- Normalization puts a conjugate in the literal left coset aX. -/
theorem conjugate_in_coset (_D : ThreeCenterConfiguration X a)
    (hn : a∈normalizer (X : Set (Sp F))) (x : X) :
    a⁻¹*((x : Sp F)*a*(x : Sp F)⁻¹)∈X := by
  have hx : a⁻¹*(x : Sp F)*a∈X := by
    have h := (mem_normalizer_iff.mp ((normalizer (X : Set (Sp F))).inv_mem hn)
      (x : Sp F)).mp x.property
    simpa only [inv_inv] using h
  simpa only [mul_assoc] using X.mul_mem hx (X.inv_mem x.property)


omit [CharP F 2] in
/-- The three marked centers span exactly a three-dimensional space. -/
theorem centers_finrank (D : ThreeCenterConfiguration X a) :
    finrank F (Submodule.span F (Set.range
      ![D.center,(D.x : Sp F) • D.center,(D.y : Sp F) • D.center]))=3 := by
  have hpair : LinearIndependent F ![D.center,(D.x : Sp F) • D.center] :=
    (LinearIndependent.pair_iff' D.center_ne_zero).mpr (fun c hc => by
      apply D.pairing_ne_zero
      rw [←hc,map_smul,TwoLocalCover.form_alternating.self_eq_zero,smul_zero])
  have htriple := linearIndependent_finSnoc.mpr ⟨hpair,D.third_outside⟩
  have he : Fin.snoc ![D.center,(D.x : Sp F) • D.center] ((D.y : Sp F) • D.center)=
      ![D.center,(D.x : Sp F) • D.center,(D.y : Sp F) • D.center] := by
    ext i
    fin_cases i <;> rfl
  have ht : LinearIndependent F
      ![D.center,(D.x : Sp F) • D.center,(D.y : Sp F) • D.center] := by
    rw [←he]
    exact htriple
  simpa only [Fintype.card_fin] using finrank_span_eq_card ht

omit [CharP F 2] in
/-- The common fixed point is the one-dimensional orthogonal complement
of the marked three-space. -/
theorem orthogonal_finrank (D : ThreeCenterConfiguration X a) :
    finrank F ((form F).orthogonal (Submodule.span F (Set.range
      ![D.center,(D.x : Sp F) • D.center,(D.y : Sp F) • D.center])))=1 := by
  rw [(form F).finrank_orthogonal TwoLocalCover.form_nondegenerate,D.centers_finrank]
  simp [Vector]

end ThreeCenterConfiguration

omit [CharP F 2] in
/-- The nested subgroup action agrees with its literal ambient image. -/
theorem mapped_subgroup_irreducible (H : Subgroup (Sp F)) (N : Subgroup H)
    (hi : Representation.IsIrreducible (((Representation.symplecticNatural 2).comp H.subtype).comp
      N.subtype)) :
    Representation.IsIrreducible ((Representation.symplecticNatural 2).comp (N.map H.subtype).subtype) := by
  let e := N.equivMapOfInjective H.subtype H.subtype_injective
  apply (Representation.irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mp
  exact hi

omit [CharP F 2] in
/-- Exact application to the ambient image of the actual normal closure. -/
theorem transvectionClosure_threeCenterConfiguration (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible (((Representation.symplecticNatural 2).comp H.subtype).comp
      (transvectionClosure H).subtype)) (a : transvectionClosure H)
    (ha : IsB1 ((a : H) : Sp F)) :
    Nonempty (ThreeCenterConfiguration ((transvectionClosure H).map H.subtype) ((a : H) : Sp F)) :=
  exists_threeCenterConfiguration _ (mapped_subgroup_irreducible H _ hi) _ ha

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
