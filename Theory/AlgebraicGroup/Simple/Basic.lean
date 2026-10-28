module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Solvable.Basic

universe u

/-! Centers and proper normal subgroups of simple algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma properNormalSubgroup_finite
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSimpleAlgebraicGroup G) (H : ClosedSubgroup G)
    (hHnormal : H.toSubgroup.Normal) (hHproper : H.toSubgroup ≠ ⊤) :
    Finite H.toSubgroup := by
  have hdim : Variety.dimension H.carrierVariety = 0 :=
    hG.2.2 H hHnormal hHproper
  have hHfinitePoints : Finite (Variety.Point H.carrierVariety) :=
    (dimension_zero_iff_finite_points H.carrierVariety).mp hdim
  exact (Equiv.finite_iff H.pointEquiv).mp hHfinitePoints

/-- A connected normal closed subgroup of a simple algebraic group is trivial
or the whole group. -/
public theorem IsSimpleAlgebraicGroup.normal_subgroup_dichotomy
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSimpleAlgebraicGroup G) (N : ClosedSubgroup G)
    (hNnormal : N.toSubgroup.Normal)
    (hNconnected : _root_.IsConnected (N : Set (Variety.Point G))) :
    N.toSubgroup = ⊥ ∨ N.toSubgroup = ⊤ := by
  by_cases hNtop : N.toSubgroup = ⊤
  · exact Or.inr hNtop
  · left
    let : Finite N.toSubgroup :=
      properNormalSubgroup_finite hG N hNnormal hNtop
    have hNfiniteSet : (N : Set (Variety.Point G)).Finite := Set.toFinite _
    let : T1Space (Variety.Point G) :=
      ⟨fun x => Variety.isClosed_iff_isZariskiClosed.mpr
        (isZariskiClosed_singleton G x)⟩
    have hNsubsingleton : (N : Set (Variety.Point G)).Subsingleton := by
      rw [← Set.not_nontrivial_iff]
      intro hnontrivial
      exact hNfiniteSet.not_infinite
        (hNconnected.isPreconnected.infinite_of_nontrivial hnontrivial)
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_bot.mpr (hNsubsingleton hx N.toSubgroup.one_mem)
    · exact bot_le

/-- Theorem 1.7.2(f): a simple algebraic group has finite center. -/
public theorem simple_center_finite
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSimpleAlgebraicGroup G) :
    Finite (Subgroup.center (Variety.Point G)) := by
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  have hZcenter : Z.toSubgroup = Subgroup.center (Variety.Point G) := by
    change Subgroup.centralizer
      ((ClosedSubgroup.top (G := G)).toSubgroup : Set (Variety.Point G)) = _
    rw [show (ClosedSubgroup.top (G := G)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ]
  have hZnormal : Z.toSubgroup.Normal := by
    rw [hZcenter]
    infer_instance
  have hZproper : Z.toSubgroup ≠ ⊤ := by
    intro hZtop
    have hcomm : IsMulCommutative (Variety.Point G) := by
      refine ⟨⟨?_⟩⟩
      intro a b
      have ha : a ∈ Z.toSubgroup := by rw [hZtop]; trivial
      have haCenter : a ∈ Subgroup.center (Variety.Point G) := by
        rw [← hZcenter]
        exact ha
      exact (Subgroup.mem_center_iff.mp haCenter b).symm
    exact hG.2.1 ((commutator_eq_bot_iff (Variety.Point G)).mpr hcomm)
  have hZfinite : Finite Z.toSubgroup :=
    properNormalSubgroup_finite hG Z hZnormal hZproper
  show Finite (Subgroup.center (Variety.Point G))
  rw [← hZcenter]
  exact hZfinite

/-- Theorem 1.7.2(f): every proper closed normal subgroup of a simple
algebraic group is central. -/
public theorem proper_normal_subgroup_le_center
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSimpleAlgebraicGroup G) :
    ∀ N : ClosedSubgroup G, N.toSubgroup.Normal → N.toSubgroup ≠ ⊤ →
      N.toSubgroup ≤ Subgroup.center (Variety.Point G) := by
  intro N hNnormal hNproper x hx
  let : Finite N.toSubgroup :=
    properNormalSubgroup_finite hG N hNnormal hNproper
  have hNrangeFinite :
      (Set.range (AlgebraicGroup.conjugateMorphism G x).toFun).Finite := by
    apply Set.Finite.subset (Set.toFinite (N : Set (Variety.Point G)))
    intro y hy
    rcases hy with ⟨g, rfl⟩
    rw [AlgebraicGroup.conjugateMorphism_apply]
    exact hNnormal.conj_mem x hx g
  have hNrangeSubsingleton := connected_finite_morphism_range_subsingleton
    (AlgebraicGroup.conjugateMorphism G x) hG.1 hNrangeFinite
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hconj := hNrangeSubsingleton ⟨1, rfl⟩ ⟨g, rfl⟩
  have hconj' : x = g * x * g⁻¹ := by
    simpa [AlgebraicGroup.conjugateMorphism_apply] using hconj
  calc
    g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [← hconj']

/-- A simple algebraic group is semisimple. -/
public theorem IsSimpleAlgebraicGroup.semisimple
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    (hG : IsSimpleAlgebraicGroup G) :
    IsSemisimpleAlgebraicGroup G := by
  refine ⟨hG.1, ?_⟩
  intro R hR
  rcases hG.normal_subgroup_dichotomy R hR.normal hR.connected with hRbot | hRtop
  · exact hRbot
  · exfalso
    let : Group.IsSolvable (Variety.Point R.carrierVariety) := hR.solvable
    let toTop : AlgebraicGroup.Morphism R.carrierVariety G := R.inclusion
    have hsurj : Function.Surjective toTop.onPoints := by
      intro y
      refine ⟨R.pointEquiv.symm ⟨y, by simp [hRtop]⟩, ?_⟩
      change R.inclusion.onPoints (R.pointEquiv.symm ⟨y, _⟩) = y
      rw [← R.pointEquiv.apply_symm_apply ⟨y, _⟩]
      rfl
    have hGsolvable : Group.IsSolvable (Variety.Point G) :=
      Group.isSolvable_of_surjective hsurj
    have hnontriv : Nontrivial (Variety.Point G) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro hsub
      let : Subsingleton (Variety.Point G) := hsub
      have hcomm : ⁅(⊤ : Subgroup (Variety.Point G)),
          (⊤ : Subgroup (Variety.Point G))⁆ =
          (⊥ : Subgroup (Variety.Point G)) := by
        apply Subsingleton.elim
      exact hG.2.1 hcomm
    let D : ClosedSubgroup G :=
      subgroupZariskiClosure G (commutator (Variety.Point G))
    have hDnormal : D.toSubgroup.Normal :=
      subgroupZariskiClosure_isNormal G _
        (derivedSeries_normal (Variety.Point G) 1)
    have hDconnected : _root_.IsConnected (D : Set (Variety.Point G)) :=
      subgroupZariskiClosure_commutator_isConnected hG.1
    have hDproper : D.toSubgroup ≠ ⊤ := by
      have hsource := subgroupZariskiClosure_commutator_ne_top_of_isSolvable
        hGsolvable inferInstance
      intro htop
      apply hsource
      exact congrArg Theory.AlgebraicGroup.ClosedSubgroup.mk
        (_root_.ClosedSubgroup.toSubgroup_injective htop)
    have hDbot : D.toSubgroup = ⊥ :=
      (hG.normal_subgroup_dichotomy D hDnormal hDconnected).resolve_right hDproper
    have hcommle : commutator (Variety.Point G) ≤ D.toSubgroup := by
      intro x hx
      change x ∈ closure (commutator (Variety.Point G) : Set (Variety.Point G))
      exact subset_closure hx
    exact False.elim (hG.2.1 (le_antisymm (hDbot ▸ hcommle) bot_le))

end Theory.AlgebraicGroup
