module
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Basis
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Generation by the roots of an SL₃ frame

Choose one spanning vector on each of the three frame lines. Their spanning
property makes them a basis. Every element of a point radical is the product
of its two coordinate shears, which fix the two corresponding frame planes.
Changing matrix coordinates to this basis carries the elementary generators
of SL₃ into the six frame roots. Thus both generation statements hold over
any field, in particular over every finite field of characteristic two,
including F₂.

The second index of `axisRoot i j` is the other fixed point: its moving
coordinate is the third index. No ambient subgroup is identified with a
point radical by this construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.1.1–2 and
G.2.5, printed pp.327,335–336, PDF pp.338,346–347.
-/

@[expose] public section
noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry
open Matrix Subgroup Module
open scoped MatrixGroups
variable {F : Type*} [Field F]

private theorem coord_zero_of_mem (b : Frame F) (v : Basis (Fin 3) F (Fin 3 → F))
    (hv : ∀ i, Submodule.span F {v i} = b.point i)
    {i j : Fin 3} (hji : j ≠ i) {x : Fin 3 → F} (hx : x ∈ b.point i) :
    v.coord j x = 0 := by
  rw [← hv i, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [Basis.coord_apply, hji]

private def fromBasis (v : Basis (Fin 3) F (Fin 3 → F)) : SL(3, F) →* SL(3, F) where
  toFun g := ⟨LinearMap.toMatrix' (Matrix.toLin v v (g : Matrix (Fin 3) (Fin 3) F)), by
    rw [LinearMap.det_toMatrix', LinearMap.det_toLin]
    exact g.property⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul]
    rw [Matrix.toLin_mul v v v, LinearMap.toMatrix'_comp]
    rfl

private theorem natural_fromBasis (v : Basis (Fin 3) F (Fin 3 → F)) (g : SL(3, F)) :
    natural (fromBasis v g) = Matrix.toLin v v (g : Matrix (Fin 3) (Fin 3) F) :=
  Matrix.toLin'_toMatrix' _

private theorem fromBasis_surjective (v : Basis (Fin 3) F (Fin 3 → F)) :
    Function.Surjective (fromBasis v) := by
  intro g
  refine ⟨⟨LinearMap.toMatrix v v (natural g), ?_⟩, ?_⟩
  · rw [LinearMap.det_toMatrix]
    change LinearMap.det (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)) = 1
    rw [LinearMap.det_toLin']
    exact g.property
  · apply Subtype.ext
    change LinearMap.toMatrix' (Matrix.toLin v v (LinearMap.toMatrix v v (natural g))) = _
    rw [Matrix.toLin_toMatrix]
    exact LinearMap.toMatrix'_toLin' _

private theorem fromBasis_transvection_apply
    (v : Basis (Fin 3) F (Fin 3 → F)) {i j : Fin 3} (hij : i ≠ j)
    (a : F) (x : Fin 3 → F) :
    natural (fromBasis v (transvection hij a)) x = x + (a * v.coord j x) • v i := by
  rw [natural_fromBasis]
  apply v.repr.injective
  ext k
  simp [Matrix.repr_toLin, transvection_coe,
    Matrix.single_mulVec_eq, Basis.coord_apply, Finsupp.single_apply, Pi.single_apply, mul_comm, eq_comm]

private theorem shear_coord_mem_axisRoot (b : Frame F)
    (v : Basis (Fin 3) F (Fin 3 → F))
    (hv : ∀ i, Submodule.span F {v i} = b.point i)
    {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (x : Fin 3 → F) (hx : x ∈ b.point i) :
    shear (v.coord k) x (coord_zero_of_mem b v hv hki hx) ∈ b.axisRoot i j := by
  apply shear_mem_root le_sup_left x hx
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro y hy
  obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, coord_zero_of_mem b v hv hki hz,
    coord_zero_of_mem b v hv hkj hw, add_zero]

/-- The two frame roots centered at a point generate its whole point radical. -/
theorem Frame.pointRadical_eq_sup_axisRoot (b : Frame F)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pointRadical (b.point i) = b.axisRoot i j ⊔ b.axisRoot i k := by
  obtain ⟨v, hv⟩ := b.exists_basis
  have hvi (l : Fin 3) : v l ∈ b.point l := by
    rw [← hv l]
    exact Submodule.subset_span (Set.mem_singleton _)
  apply le_antisymm
  · intro g hg
    let x := natural g (v k) - v k
    let y := natural g (v j) - v j
    have hx : x ∈ b.point i := hg.1 _
    have hy : y ∈ b.point i := hg.1 _
    let a := shear (v.coord k) x (coord_zero_of_mem b v hv hik.symm hx)
    let c := shear (v.coord j) y (coord_zero_of_mem b v hv hij.symm hy)
    have ha : a ∈ b.axisRoot i j := shear_coord_mem_axisRoot b v hv hik.symm hjk.symm x hx
    have hc : c ∈ b.axisRoot i k := shear_coord_mem_axisRoot b v hv hij.symm hjk y hy
    have hac : g = a * c := by
      apply Subtype.ext
      apply Matrix.toLin'.injective
      apply v.ext
      intro l
      change natural g (v l) = natural (a * c) (v l)
      rw [map_mul, Module.End.mul_apply]
      have hl : l = i ∨ l = j ∨ l = k := by omega
      rcases hl with hl | hl | hl
      all_goals subst l
      · rw [hc.2 _ (Submodule.mem_sup_left (hvi i)), ha.2 _ (Submodule.mem_sup_left (hvi i)),
          hg.2 _ (hvi i)]
      · have hcj : natural c (v j) = v j + y := by
          simp [c, shear_apply, Basis.coord_apply]
        rw [hcj, map_add, ha.2 _ (Submodule.mem_sup_right (hvi j)),
          ha.2 _ (Submodule.mem_sup_left hy)]
        dsimp [y]
        abel
      · rw [hc.2 _ (Submodule.mem_sup_right (hvi k))]
        simp [a, shear_apply, Basis.coord_apply, x]
    rw [hac]
    exact (b.axisRoot i j ⊔ b.axisRoot i k).mul_mem
      ((le_sup_left : b.axisRoot i j ≤ _) ha) ((le_sup_right : b.axisRoot i k ≤ _) hc)
  · exact sup_le (b.axisRoot_le_pointRadical i j) (b.axisRoot_le_pointRadical i k)

/-- All six frame roots generate the actual special linear group. -/
theorem Frame.iSup_axisRoot_eq_top (b : Frame F) :
    (⨆ i, ⨆ j, ⨆ (_ : i ≠ j), b.axisRoot i j) = ⊤ := by
  obtain ⟨v, hv⟩ := b.exists_basis
  apply top_unique
  intro g _
  obtain ⟨g, rfl⟩ := fromBasis_surjective v g
  apply Atlas.sl_elementary_induction
    (fun g => fromBasis v g ∈ ⨆ i, ⨆ j, ⨆ (_ : i ≠ j), b.axisRoot i j)
    ?_ ?_ g
  · intro i j hij a
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
    have hle : b.axisRoot i k ≤ ⨆ i, ⨆ j, ⨆ (_ : i ≠ j), b.axisRoot i j :=
      le_iSup_of_le i (le_iSup_of_le k (le_iSup_of_le hki.symm le_rfl))
    apply hle
    constructor
    · intro x
      rw [fromBasis_transvection_apply, add_sub_cancel_left]
      apply (b.point i).smul_mem
      rw [← hv i]
      exact Submodule.subset_span (Set.mem_singleton _)
    · intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [fromBasis_transvection_apply, map_add,
        coord_zero_of_mem b v hv hij.symm hy, coord_zero_of_mem b v hv hkj.symm hz]
      simp
  · intro a c ha hc
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hc

/-- The three point radicals generate SL₃, as used for the source triple. -/
theorem Frame.iSup_pointRadical_eq_top (b : Frame F) :
    (⨆ i, pointRadical (b.point i)) = ⊤ := by
  apply top_unique
  rw [← b.iSup_axisRoot_eq_top]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun _ => ?_
  exact (b.axisRoot_le_pointRadical i j).trans (le_iSup (fun i => pointRadical (b.point i)) i)

end Matrix.SpecialLinearGroup.FrameGeometry
