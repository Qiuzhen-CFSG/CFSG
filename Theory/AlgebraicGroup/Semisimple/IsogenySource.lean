module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Semisimple.Defs

universe u

/-!
Semisimplicity lifts through an isogeny with connected source.  For a source
radical, its closed image is connected, normal, and solvable, hence lies in the
trivial target radical.  The radical therefore embeds into the finite kernel;
connectedness and the zero-dimensional/finite-point dimension criterion force
it to be trivial.  This is the source-side counterpart to GLS3, Chapter 1,
Proposition 1.10.3(c), used in the version constructions around Theorem 1.10.4.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_isConnected
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G))) :
    Variety.IsConnected S.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- A connected source of an isogeny onto a semisimple group is semisimple. -/
public theorem isogeny_source_semisimple
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : AlgebraicGroup.Morphism H G) (hφ : IsIsogeny φ)
    (hH : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
    (hG : IsSemisimpleAlgebraicGroup G) :
    IsSemisimpleAlgebraicGroup H := by
  refine ⟨hH, ?_⟩
  intro R hR
  let q := φ.comp R.inclusion
  let Q := q.imageClosedSubgroup
  have hQmap : Q.toSubgroup = R.toSubgroup.map φ.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ q.image at hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨R.inclusion.onPoints x, (R.pointEquiv x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      change φ.onPoints x ∈ q.image
      let xR : Variety.Point R.carrierVariety :=
        R.pointEquiv.symm ⟨x, hx⟩
      refine ⟨xR, ?_⟩
      change φ.onPoints (R.inclusion.onPoints xR) = φ.onPoints x
      apply congrArg φ.onPoints
      change (R.pointEquiv xR).val = x
      simp [xR]
  have hQnormal : Q.toSubgroup.Normal := by
    rw [hQmap]
    exact Subgroup.Normal.map hR.normal φ.onPoints hφ.1
  have hRvar : Variety.IsConnected R.carrierVariety :=
    R.carrierVariety_isConnected hR.connected
  have hQconnected : _root_.IsConnected (Q : Set (Variety.Point G)) :=
    q.imageClosedSubgroup_isConnected hRvar
  have hQsolvable : Group.IsSolvable (Variety.Point Q.carrierVariety) :=
    q.imageClosedSubgroup_isSolvable hR.solvable
  obtain ⟨S, hS⟩ := exists_radical G
  have hQle : Q ≤ S := hS.maximal Q hQnormal hQconnected hQsolvable
  have hQbot : Q.toSubgroup = ⊥ := by
    apply le_antisymm
    · rw [← hG.2 S hS]
      exact hQle
    · exact bot_le
  have hRker : R.toSubgroup ≤ φ.kernel := by
    intro x hx
    change φ.onPoints x = 1
    apply Subgroup.mem_bot.mp
    rw [← hQbot]
    change φ.onPoints x ∈ q.image
    let xR : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm ⟨x, hx⟩
    refine ⟨xR, ?_⟩
    change φ.onPoints (R.inclusion.onPoints xR) = φ.onPoints x
    apply congrArg φ.onPoints
    change (R.pointEquiv xR).val = x
    simp [xR]
  let : Finite φ.kernel := hφ.2
  let embed : R.toSubgroup → φ.kernel := fun x => ⟨x.1, hRker x.2⟩
  let : Finite R.toSubgroup := Finite.of_injective embed (by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : φ.kernel => (z : Variety.Point H)) hxy)
  have hRpointsFinite : Finite (Variety.Point R.carrierVariety) :=
    (Equiv.finite_iff R.pointEquiv).mpr inferInstance
  have hRdim : Variety.dimension R.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points R.carrierVariety).mpr hRpointsFinite
  by_contra hRne
  have hRpos := connected_closedSubgroup_dimension_pos_of_ne_bot
    R hR.connected hRne
  rw [hRdim] at hRpos
  exact (lt_irrefl 0 hRpos)

end Theory.AlgebraicGroup
