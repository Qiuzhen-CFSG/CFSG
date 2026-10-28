module
public import Theory.AlgebraicGroup.Radical.Image
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Bor1.GeometricQuotientDescent
public import Theory.AlgebraicGroup.Tori.SolvableKernelImage
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree

public section
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

omit [IsAlgClosed k] in
/-- The kernel of a quotient by the solvable radical is solvable on points. -/
theorem IsRadicalSubgroup.quotient_kernel_isSolvable
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    (q : AlgebraicGroup.Morphism G Q) (hker : q.kernel = R.toSubgroup) :
    Group.IsSolvable q.kernel := by
  rw [hker]
  let := hR.solvable
  exact Group.isSolvable_of_surjective
    (f := (Equiv.mulEquiv R.pointEquiv).toMonoidHom)
    (Equiv.mulEquiv R.pointEquiv).surjective

/-- The actual surjective quotient with kernel the radical is semisimple. -/
theorem IsRadicalSubgroup.quotient_isSemisimple
    (hG : Variety.IsConnected G) {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : q.kernel = R.toSubgroup) : IsSemisimpleAlgebraicGroup Q := by
  refine ⟨connected_of_surjective_morphism q hG hq, ?_⟩
  intro A hA
  have hRA := hR.imageClosedSubgroup_eq_of_surjective_of_kernel_isSolvable
    q hq hA (hR.quotient_kernel_isSolvable q hker)
  rw [← hRA]
  apply le_antisymm _ bot_le
  rintro y ⟨x,rfl⟩
  apply Subgroup.mem_bot.mpr
  apply (show R.inclusion.onPoints x ∈ q.kernel from ?_)
  rw [hker]
  exact (R.pointEquiv x).property

omit [IsAlgClosed k] in
/-- A nonsolvable group remains nonsolvable after quotienting by its radical. -/
theorem IsRadicalSubgroup.quotient_not_isSolvable
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    (hns : ¬ Group.IsSolvable (Variety.Point G))
    (q : AlgebraicGroup.Morphism G Q) (hker : q.kernel = R.toSubgroup) :
    ¬ Group.IsSolvable (Variety.Point Q) := by
  intro hQ
  let := hQ
  let := hR.quotient_kernel_isSolvable q hker
  apply hns
  exact Group.isSolvable_of_ker_le_range q.kernel.subtype q.onPoints (by
    intro x hx
    exact ⟨⟨x,hx⟩,rfl⟩)

/-- A maximal torus of a connected nonsolvable group is nontrivial. -/
theorem maximalTorus_ne_bot_of_not_isSolvable (hG : Variety.IsConnected G)
    (hns : ¬ Group.IsSolvable (Variety.Point G))
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) : T.toSubgroup ≠ ⊥ := by
  intro hbot
  apply hns
  apply isSolvable_of_isUnipotentAlgebraicGroup
  apply TorusFree.isUnipotent_of_torusFree hG
  intro S hS
  have hTS : T ≤ S := by
    intro x hx
    change x ∈ T.toSubgroup at hx
    rw [hbot] at hx
    exact Subgroup.mem_bot.mp hx ▸ S.toSubgroup.one_mem
  rw [hT.2 S hS hTS]
  exact hbot

/-- A connected nonsolvable radical quotient retains a positive-dimensional
maximal torus, along the original quotient morphism. -/
theorem IsRadicalSubgroup.quotient_maximalTorus_positive
    (hG : Variety.IsConnected G) {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    (hns : ¬ Group.IsSolvable (Variety.Point G))
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : q.kernel = R.toSubgroup)
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    IsMaximalTorus (q.comp T.inclusion).imageClosedSubgroup ∧
      0 < Variety.dimension (q.comp T.inclusion).imageClosedSubgroup.carrierVariety := by
  have hM := maximalTorus_image_of_solvable_kernel q hq
    (hR.quotient_kernel_isSolvable q hker) hT
  refine ⟨hM, ?_⟩
  apply connected_closedSubgroup_dimension_pos_of_ne_bot
  · exact (q.comp T.inclusion).imageClosedSubgroup_isConnected hT.1.isConnected
  · exact maximalTorus_ne_bot_of_not_isSolvable
      (connected_of_surjective_morphism q hG hq)
      (hR.quotient_not_isSolvable hns q hker) hM

private theorem image_dimension_eq_of_injective
    (f : AlgebraicGroup.Morphism G Q) (hf : Function.Injective f.onPoints) :
    Variety.dimension f.imageClosedSubgroup.carrierVariety = Variety.dimension G := by
  let : Subsingleton f.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hf
    exact x.property.trans y.property.symm
  let : Subsingleton (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
    f.kernelClosedSubgroup.pointEquiv.subsingleton
  have hzero : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points _).2 inferInstance
  have heq := morphism_dimension_eq_kernel_add_image f
  rw [hzero,zero_add] at heq
  exact heq.symm

/-- Killing a connected codimension-one subgroup of a torus leaves an image
of dimension at most one. The kernel and restriction are the literal maps. -/
theorem torus_image_dimension_le_one
    (q : AlgebraicGroup.Morphism G Q)
    {S T : ClosedSubgroup G} (hS : IsSubtorus S) (hST : S ≤ T)
    (hSk : S.toSubgroup ≤ q.kernel)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety) :
    Variety.dimension (q.comp T.inclusion).imageClosedSubgroup.carrierVariety ≤ 1 := by
  let j := S.inclusion.codRestrictClosedSubgroup T
    (fun x => hST (S.pointEquiv x).property)
  let f := q.comp T.inclusion
  have hj : Function.Injective j.onPoints := by
    intro x y hxy
    apply S.inclusion_injective
    simpa [j, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
      congrArg T.inclusion.onPoints hxy
  have hJk : j.imageClosedSubgroup ≤ f.kernelClosedSubgroup := by
    rintro x ⟨s,rfl⟩
    change q.onPoints (T.inclusion.onPoints (j.onPoints s)) = 1
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hSk (S.pointEquiv s).property
  have hdimle := connected_closedSubgroup_dimension_le_of_le
    j.imageClosedSubgroup f.kernelClosedSubgroup
    (j.imageClosedSubgroup_isConnected hS.isConnected) hJk
  rw [image_dimension_eq_of_injective j hj] at hdimle
  have hdim := morphism_dimension_eq_kernel_add_image f
  have hbound : Variety.dimension S.carrierVariety +
      Variety.dimension f.imageClosedSubgroup.carrierVariety ≤
      Variety.dimension S.carrierVariety + 1 := by
    rw [hcodim, hdim]
    exact add_le_add hdimle le_rfl
  have hnat := (Cardinal.toNat_le_iff_le_of_lt_aleph0
    (Cardinal.add_lt_aleph0 (variety_dimension_lt_aleph0 _) (variety_dimension_lt_aleph0 _))
    (Cardinal.add_lt_aleph0 (variety_dimension_lt_aleph0 _) Cardinal.one_lt_aleph0)).mpr hbound
  rw [Cardinal.toNat_add (variety_dimension_lt_aleph0 _) (variety_dimension_lt_aleph0 _),
    Cardinal.toNat_add (variety_dimension_lt_aleph0 _) Cardinal.one_lt_aleph0] at hnat
  apply (Cardinal.toNat_le_iff_le_of_lt_aleph0
    (variety_dimension_lt_aleph0 _) Cardinal.one_lt_aleph0).mp
  exact Nat.le_of_add_le_add_left hnat


/-- A connected nonsolvable algebraic group with a central codimension-one
subtorus of a maximal torus has an actual semisimple radical quotient of rank
one. This is the quotient step in Borel IV, 13.11. -/
theorem exists_rankOne_radical_quotient_of_central_codimension_one
    (hG : Variety.IsConnected G) (hns : ¬ Group.IsSolvable (Variety.Point G))
    {S T : ClosedSubgroup G} (hS : IsSubtorus S) (hT : IsMaximalTorus T)
    (hST : S ≤ T) (hSc : S.toSubgroup ≤ Subgroup.center (Variety.Point G))
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety) :
    ∃ R : ClosedSubgroup G, IsRadicalSubgroup R ∧
      ∃ d : Bor1.Theorem112BQuotientData R,
        let _ : AlgebraicGroup d.quotient := d.quotientAlgebraicGroup
        IsSemisimpleAlgebraicGroup d.quotient ∧
        IsMaximalTorus (d.projection.comp T.inclusion).imageClosedSubgroup ∧
        Variety.dimension (d.projection.comp T.inclusion).imageClosedSubgroup.carrierVariety = 1 := by
  obtain ⟨R,hR⟩ := exists_radical G
  let d := Bor1.theorem_1_1_2_b_quotientData R hR.normal
  let _ : AlgebraicGroup d.quotient := d.quotientAlgebraicGroup
  have hSR : S ≤ R := by
    apply hR.maximal S
    · constructor
      intro s hs g
      have heq : g * s * g⁻¹ = s := by
        calc
          g * s * g⁻¹ = s * g * g⁻¹ := by rw [Subgroup.mem_center_iff.mp (hSc hs) g]
          _ = s := by simp
      rw [heq]
      exact hs
    · let : ConnectedSpace (Variety.Point S.carrierVariety) :=
        connectedSpace_iff_univ.mpr hS.isConnected
      change _root_.IsConnected (S.toSubgroup : Set (Variety.Point G))
      rw [← S.range_inclusion]
      exact isConnected_range S.inclusion.toVariety.continuous
    · exact Group.isSolvable_of_comm (isMulCommutative_iff.mp hS.isMulCommutative)
  have hSk : S.toSubgroup ≤ d.projection.kernel := by
    rw [d.kernel_eq]
    exact hSR
  have hpos := hR.quotient_maximalTorus_positive hG hns d.projection
    d.pointSurjective d.kernel_eq hT
  refine ⟨R,hR,d,hR.quotient_isSemisimple hG d.projection
    d.pointSurjective d.kernel_eq,hpos.1,le_antisymm ?_ ?_⟩
  · exact torus_image_dimension_le_one d.projection hS hST hSk hcodim
  · exact Cardinal.one_le_iff_ne_zero.mpr (ne_of_gt hpos.2)

end Theory.AlgebraicGroup

