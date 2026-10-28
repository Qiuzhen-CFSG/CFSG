module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.Actor
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.Branches
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Cover
public import Theory.Representation.SymplecticFourOrthogonalCover.InvariantRefinement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.ArbitraryOrthogonalActors

/-!
# Saturation of the original symplectic plane cover

An actor of order q² in a conjugate of the plane radical has the full plane as
its field displacement space. If its commutator missed the original central
kernel, the cover would supply an invariant quadratic refinement. The bound
2q for a quadratic group preserving such a refinement contradicts q² > 2q.
Surjectivity of the original projection then lifts the entire plane, including
the central kernel, into the ambient commutator.

This proves the normalized-pair saturation step of source 11.2.4 without a
splitting or root-avoidance assumption. It applies to the published actor
specification and to the literal plane-alignment consumer. Construction of the
actor and parabolic geometry remains with the nonnormalization assembly owner
`qt-d-1222-natural-conjugate-nonnormalization`.

Source: Aschbacher--Smith, 11.2.4, refs/quasithin.pdf, printed pp.769--770.
-/

public noncomputable section
open scoped IsMulCommutative
open Matrix Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.RootPair

section Model
variable {F : Type*} [Field F]

private theorem radical_geometry {a : Sp F}
    (ha : a ∈ Plane.radical.map planeLocal.subtype) :
    (∀ v ∈ plane F, a • v = v) ∧ (∀ v : Theory.SpecificGroups.SymplecticFour.Vector F, a • v-v ∈ plane F) := by
  obtain ⟨q,hq,rfl⟩ := ha
  have hm := Plane.radical_matrix (⟨q,hq⟩ : Plane.radical (F := F))
  constructor
  · intro v hv
    have hv' := (mem_plane v).mp hv
    ext i
    change (q.val.val *ᵥ v) i = v i
    rw [hm]
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.fromBlocks, hv']
  · intro v
    rw [mem_plane]
    intro i
    change (q.val.val *ᵥ v) (.inr i)-v (.inr i)=0
    rw [hm]
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.fromBlocks]

private theorem conjugate_radical_geometry (b : Sp F) {a : Sp F}
    (ha : a ∈ (Plane.radical.map planeLocal.subtype).map (MulAut.conj b).toMonoidHom) :
    (∀ v ∈ (plane F).map (symplecticNatural 2 b), a • v=v) ∧
    (∀ v : Theory.SpecificGroups.SymplecticFour.Vector F, a • v-v ∈ (plane F).map (symplecticNatural 2 b)) := by
  obtain ⟨q,hq,rfl⟩ := ha
  obtain ⟨hfix,hmove⟩ := radical_geometry hq
  constructor
  · rintro v ⟨w,hw,rfl⟩
    change (b*q*b⁻¹) • (b • w) = b • w
    simp only [mul_smul,inv_smul_smul,hfix w hw]
  · intro v
    refine ⟨q • (b⁻¹ • v)-b⁻¹ • v,hmove _,?_⟩
    change toLinear b (_-_) = (b*q*b⁻¹) • v-v
    simp only [map_sub,toLinear_apply,mul_smul,smul_inv_smul]

private theorem radical_displacement_eq [Finite F]
    (H : Subgroup (Sp F)) (b : Sp F)
    (hH : H ≤ (Plane.radical.map planeLocal.subtype).map (MulAut.conj b).toMonoidHom)
    (hlarge : Nat.card F < Nat.card H) :
    displacementSpace H = (plane F).map (symplecticNatural 2 b) := by
  have hq : ∀ x ∈ H, ∀ y ∈ H, ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F, x • (y • v-v)=y • v-v := by
    intro x hx y hy v
    exact (conjugate_radical_geometry b (hH hx)).1 _
      ((conjugate_radical_geometry b (hH hy)).2 v)
  have hself := large_quadratic_displacement_self_orthogonal H hq hlarge
  have hd : Module.finrank F (displacementSpace H) = 2 := by
    have he := LinearMap.BilinForm.finrank_orthogonal
      (W := displacementSpace H) TwoLocalCover.form_nondegenerate
    rw [hself] at he
    have hv : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hv] at he
    omega
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,v⟩,rfl⟩
    exact (conjugate_radical_geometry b (hH x.property)).2 v
  · rw [hd,← (Submodule.equivMapOfInjective (symplecticNatural 2 b)
      ((symplecticNatural (k := F) 2).apply_bijective b).1 (plane F)).finrank_eq,
      finrank_plane]

variable [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
open SymplecticFourOrthogonalCover

private theorem cover_kernel_le_of_large_quadratic
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F)))
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
      ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F, x • (y • v-v)=y • v-v)
    (hlarge : 2*Nat.card F < Nat.card A) :
    p.toLinearMap.ker ≤ Coinvariants.ker (σ.comp A.subtype) := by
  by_contra he
  obtain ⟨c,hc⟩ := cover_preserves_refinement_of_kernel_escape p hp A he
  let H := A.map (commutator (Sp F)).subtype
  have hcard : Nat.card H = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hbig : Nat.card F < Nat.card H := by rw [hcard]; omega
  have hP := large_quadratic_displacement_self_orthogonal H hq hbig
  have hle := card_le_of_fixes_self_orthogonal_plane H (displacementSpace H) hP
    (fun a v hv => displacementSpace_le_fixedSpace_of_quadratic H hq hv a.val a.property)
    c (by
      rintro ⟨a,⟨x,hx,rfl⟩⟩ v
      exact hc ⟨x,hx⟩ v)
  rw [hcard] at hle
  omega

omit [Finite F] [CharP F 2] in
private theorem natural_coinvariants_map (A : Subgroup (L (K := F))) :
    Coinvariants.ker ((binaryNatural (K := F)).comp A.subtype) =
      (displacementSpace (A.map (commutator (Sp F)).subtype)).restrictScalars (ZMod 2) := by
  change Coinvariants.ker (restrictScalars (k := ZMod 2)
    ((symplecticDerivedNatural 2).comp A.subtype)) = _
  rw [coinvariants_restrictScalars]
  congr 1
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨a,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (A.map (commutator (Sp F)).subtype).subtype)
      ⟨a.val.val,⟨a.val,a.property,rfl⟩⟩ v
  · rintro _ ⟨⟨⟨a,⟨x,hx,rfl⟩⟩,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticDerivedNatural 2).comp A.subtype) ⟨x,hx⟩ v

private theorem cover_preimage_displacement_le_of_large_quadratic
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F)))
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
      ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F, x • (y • v-v)=y • v-v)
    (hlarge : 2*Nat.card F < Nat.card A) :
    ((displacementSpace (A.map (commutator (Sp F)).subtype)).restrictScalars
      (ZMod 2)).comap p.toLinearMap ≤ Coinvariants.ker (σ.comp A.subtype) := by
  let pA : Representation.IntertwiningMap (σ.comp A.subtype) ((binaryNatural (K := F)).comp A.subtype) :=
    p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun a v => LinearMap.congr_fun (p.isIntertwining' a.val) v)
  have hm := map_coinvariants_of_surjective pA hp.1
  rw [natural_coinvariants_map] at hm
  rw [←hm]
  change ((Coinvariants.ker (σ.comp A.subtype)).map p.toLinearMap).comap p.toLinearMap ≤ _
  rw [Submodule.comap_map_eq]
  exact sup_le le_rfl (cover_kernel_le_of_large_quadratic p hp A hq hlarge)
end Model
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open SymplecticFourOrthogonalCover hiding L
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- A large plane actor moves the entire marked plane preimage, including
all of the original central kernel. No complement to that kernel is chosen. -/
theorem plane_le_commutator_of_action
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) (A : Subgroup G)
    (actor : A →* Sp S.field.Carrier) (basis : Sp S.field.Carrier)
    (plane_eq : f.space 1 = (plane S.field.Carrier).map (symplecticNatural 2 basis))
    (action_eq : ∀ (a : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (actor a) v)) : G) =
        (a : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (a : G)⁻¹)
    (range_le : actor.range ≤
      (Plane.radical.map planeLocal.subtype).map (MulAut.conj basis).toMonoidHom)
    (card_range : Nat.card actor.range = 2 ^ (2 * S.field.degree)) :
    f.Vi 1 ≤ ⁅V,A⁆ := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Sp S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let α : A →* SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    actor.codRestrict (commutator (Sp S.field.Carrier))
      (fun _ => Group.IsPerfect.mem_commutator)
  have hα : α.range.map (commutator (Sp S.field.Carrier)).subtype = actor.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have hcard : Nat.card α.range = Nat.card actor.range := by
    rw [←hα]
    exact Nat.card_congr (α.range.equivMapOfInjective _ Subtype.val_injective).toEquiv
  have hfield : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) S.nonbinary
  have hc : Nat.card actor.range = Nat.card S.field.Carrier ^ 2 := by
    rw [card_range,S.field.card_eq,←pow_mul,Nat.mul_comm 2]
  have hlarge : 2*Nat.card S.field.Carrier < Nat.card α.range := by
    rw [hcard,hc,pow_two]
    exact Nat.mul_lt_mul_of_pos_right hfield Nat.card_pos
  have hbig : Nat.card S.field.Carrier < Nat.card actor.range := by
    rw [←hcard]
    omega
  have hplane := radical_displacement_eq actor.range basis range_le hbig
  have hq : ∀ x ∈ α.range.map (commutator (Sp S.field.Carrier)).subtype,
      ∀ y ∈ α.range.map (commutator (Sp S.field.Carrier)).subtype,
      ∀ v : Theory.SpecificGroups.SymplecticFour.Vector S.field.Carrier, x • (y • v-v)=y • v-v := by
    rw [hα]
    intro x hx y hy v
    exact (conjugate_radical_geometry basis (range_le hx)).1 _
      ((conjugate_radical_geometry basis (range_le hy)).2 v)
  let σ := RootParabolic.sp4CoverAction D S m
  let p := RootParabolic.sp4CoverProjection D S m
  have hs := cover_preimage_displacement_le_of_large_quadratic p
    (RootParabolic.sp4CoverProjection_isCover D S m) α.range hq hlarge
  rw [hα,hplane,←plane_eq] at hs
  let j : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom
  let C : Submodule (ZMod 2) D.space :=
    AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm (⁅V,A⁆.comap j))
  have hcomm : Coinvariants.ker (σ.comp α.range.subtype) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨x,hx⟩ := a.property
    change j (Multiplicative.ofAdd (σ a.val w-w)) ∈ ⁅V,A⁆
    rw [←hx,ofAdd_sub,map_div,div_eq_mul_inv]
    change (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (actor x) w)) : G) *
      (D.spaceEquiv (Multiplicative.ofAdd w) : G)⁻¹ ∈ ⁅V,A⁆
    rw [action_eq,commutator_comm V A]
    exact commutator_mem_commutator x.property (D.spaceEquiv (Multiplicative.ofAdd w)).property
  intro v hv
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let w : D.space := (D.spaceEquiv.symm v').toAdd
  have hw : p w ∈ f.space 1 := by
    exact ((Coordinates.sp4 m).mem_preimage (f.space 1) v').mp hv
  have hm := hcomm (hs hw)
  change j (Multiplicative.ofAdd w) ∈ ⁅V,A⁆ at hm
  simpa only [j,w,v',Subgroup.coe_subtype,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,ofAdd_toAdd,
    MulEquiv.apply_symm_apply] using hm

/-- The exact actor specification from the root-pair contract supplies all
inputs to the stronger cover calculation above. Root avoidance is unnecessary. -/
theorem plane_le_commutator
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) (A : Subgroup G)
    (r : InnerPlaneActor (S := S) m f A) : f.Vi 1 ≤ ⁅V,A⁆ :=
  plane_le_commutator_of_action m f A r.hom r.basis r.plane r.action r.range_le r.card_range

/-- The exact first-preimage containment required by the normalized pair. -/
theorem point_le_commutator
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) (A : Subgroup G)
    (r : InnerPlaneActor (S := S) m f A) : f.Vi 0 ≤ ⁅V,A⁆ :=
  (f.Vi_mono (by decide : (0 : Fin 3) ≤ 1)).trans (plane_le_commutator m f A r)

/-- The original parabolic quotient-plane equality lifts through its actual
central kernel after the large-actor argument. -/
theorem commutator_eq_plane
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) (A : Subgroup G)
    (r : InnerPlaneActor (S := S) m f A) (hp : ParabolicGeometry f A) :
    ⁅V,A⁆ = f.Vi 1 :=
  commutator_eq_of_point_le f hp (point_le_commutator m f A r)

/-- Application on the literal original conjugate to the plane-alignment
consumer. The parent still constructs the actor and the parabolic geometry. -/
theorem alignment_of_innerPlaneActor
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V,V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (r : InnerPlaneActor (S := S) m f (V.map (MulAut.conj g).toMonoidHom)) :
    Alignment (f.Vi 1) V g :=
  alignment_of_point_le f hp g hg hne hn (point_le_commutator m f _ r)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.RootPair
