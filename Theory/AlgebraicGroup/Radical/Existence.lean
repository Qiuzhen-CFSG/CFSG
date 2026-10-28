module

public import Theory.AlgebraicGroup.ClosedSubgroup.Maximal
public import Theory.AlgebraicGroup.ClosedSubgroup.Product
public import Theory.AlgebraicGroup.Radical.Defs

universe u

/-! Existence of radical subgroups. -/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Theorem 1.7.2(a): every algebraic group has a radical subgroup. -/
public theorem exists_radical (G : Variety k) [AlgebraicGroup G] :
    ∃ R : ClosedSubgroup G, IsRadicalSubgroup R := by
  obtain ⟨R, hR, hmax⟩ := exists_maximal_connected_closedSubgroup G
    (fun S =>
      S.toSubgroup.Normal ∧
        _root_.IsConnected (S : Set (Variety.Point G)) ∧
        Group.IsSolvable (Variety.Point S.carrierVariety))
    (by
      let R : ClosedSubgroup G := ClosedSubgroup.bot
      refine ⟨R, ?_, ?_, ?_⟩
      · exact Subgroup.normal_bot
      · change _root_.IsConnected ({1} : Set (Variety.Point G))
        exact isConnected_singleton
      · let : Subsingleton R.toSubgroup := by
          constructor
          intro x y
          apply Subtype.ext
          exact (Subgroup.mem_bot.mp x.property).trans
            (Subgroup.mem_bot.mp y.property).symm
        let : Subsingleton (Variety.Point R.carrierVariety) :=
          R.pointEquiv.subsingleton
        exact (inferInstance : Group.IsSolvable (Variety.Point R.carrierVariety)))
    (fun _ hS => hS.2.1)
  refine ⟨R, hR.1, hR.2.1, hR.2.2, ?_⟩
  intro N hNnormal hNconnected hNsolvable
  let : R.toSubgroup.Normal := hR.1
  let : N.toSubgroup.Normal := hNnormal
  obtain ⟨m, hm⟩ :=
    exists_closedSubgroup_productMorphism_range_eq_pointwise_mul R N
  have hsupConstructible : Topology.IsConstructible
      ((R.toSubgroup ⊔ N.toSubgroup : Subgroup (Variety.Point G)) :
        Set (Variety.Point G)) := by
    rw [Subgroup.normal_mul, ← hm]
    exact m.range_isConstructible
  have hsupClosed : IsClosed
      ((R.toSubgroup ⊔ N.toSubgroup : Subgroup (Variety.Point G)) :
        Set (Variety.Point G)) :=
    constructible_subgroup_isClosed G _ hsupConstructible
  let P : ClosedSubgroup G := ClosedSubgroup.ofSubgroup
    (R.toSubgroup ⊔ N.toSubgroup)
    (Variety.isClosed_iff_isZariskiClosed.mp hsupClosed)
  have hPconnected : _root_.IsConnected (P : Set (Variety.Point G)) := by
    change _root_.IsConnected
      ((R.toSubgroup ⊔ N.toSubgroup : Subgroup (Variety.Point G)) :
        Set (Variety.Point G))
    rw [Subgroup.normal_mul]
    let S : R.toSubgroup → Set (Variety.Point G) := fun r =>
      (R.toSubgroup : Set (Variety.Point G)) ∪
        (fun n : Variety.Point G => r.1 * n) ''
          (N.toSubgroup : Set (Variety.Point G))
    have htranslate (r : R.toSubgroup) : _root_.IsConnected
        ((fun n : Variety.Point G => r.1 * n) ''
          (N.toSubgroup : Set (Variety.Point G))) :=
      hNconnected.image _ (continuous_const_mul r.1).continuousOn
    have hS (r : R.toSubgroup) : _root_.IsConnected (S r) := by
      apply hR.2.1.union
      · exact ⟨r.1, r.2, ⟨1, N.toSubgroup.one_mem, by simp⟩⟩
      · exact htranslate r
    have hinter : (⋂ r, S r).Nonempty := by
      refine ⟨1, ?_⟩
      rw [Set.mem_iInter]
      intro r
      exact Or.inl R.toSubgroup.one_mem
    have hunion : _root_.IsConnected (⋃ r, S r) := by
      refine ⟨?_, isPreconnected_iUnion hinter fun r => (hS r).isPreconnected⟩
      refine ⟨1, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨(1 : R.toSubgroup), Or.inl R.toSubgroup.one_mem⟩
    rw [← show (⋃ r, S r) =
        (R.toSubgroup : Set (Variety.Point G)) *
          (N.toSubgroup : Set (Variety.Point G)) by
      ext g
      constructor
      · intro hg
        rw [Set.mem_iUnion] at hg
        rcases hg with ⟨r, hg | ⟨n, hn, rfl⟩⟩
        · exact ⟨g, hg, 1, N.toSubgroup.one_mem, mul_one g⟩
        · exact ⟨r.1, r.2, n, hn, rfl⟩
      · rintro ⟨r, hr, n, hn, rfl⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨r, hr⟩, Or.inr ⟨n, hn, rfl⟩⟩]
    exact hunion
  have hPsolvable : Group.IsSolvable (Variety.Point P.carrierVariety) := by
    let : Group.IsSolvable R.toSubgroup := by
      let : Group.IsSolvable (Variety.Point R.carrierVariety) := hR.2.2
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv R.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv R.pointEquiv).surjective
    let : Group.IsSolvable N.toSubgroup := by
      let : Group.IsSolvable (Variety.Point N.carrierVariety) := hNsolvable
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv N.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv N.pointEquiv).surjective
    let T := R.toSubgroup ⊔ N.toSubgroup
    let RT : Subgroup T := R.toSubgroup.subgroupOf T
    let : RT.Normal := inferInstance
    let q := QuotientGroup.mk' RT
    let iN : N.toSubgroup →* T := Subgroup.inclusion le_sup_right
    let qN : N.toSubgroup →* T ⧸ RT := q.comp iN
    have hqNsurj : Function.Surjective qN := by
      intro y
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective RT y
      have ht : t.1 ∈ (R.toSubgroup : Set (Variety.Point G)) *
          (N.toSubgroup : Set (Variety.Point G)) := by
        rw [← Subgroup.normal_mul R.toSubgroup N.toSubgroup]
        exact t.2
      rcases ht with ⟨r, hr, n, hn, hrt⟩
      refine ⟨⟨n, hn⟩, ?_⟩
      apply (QuotientGroup.eq_iff_div_mem).2
      change (⟨n, (show N.toSubgroup ≤ T from le_sup_right) hn⟩ : T) / t ∈ RT
      change n / t.1 ∈ R.toSubgroup
      rw [← hrt]
      simpa using R.toSubgroup.inv_mem hr
    let : Group.IsSolvable (T ⧸ RT) := Group.isSolvable_of_surjective hqNsurj
    have hTsolvable : Group.IsSolvable T := by
      apply Group.isSolvable_of_ker_le_range (Subgroup.inclusion le_sup_left) q
      simp [q, RT, T]
    let : Group.IsSolvable P.toSubgroup := hTsolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Equiv.mulEquiv P.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv P.pointEquiv).injective
  have hPnormal : P.toSubgroup.Normal := by
    change (R.toSubgroup ⊔ N.toSubgroup).Normal
    infer_instance
  have hRP : R ≤ P := by
    change R.toSubgroup ≤ R.toSubgroup ⊔ N.toSubgroup
    exact le_sup_left
  have hNP : N ≤ P := by
    change N.toSubgroup ≤ R.toSubgroup ⊔ N.toSubgroup
    exact le_sup_right
  have hPR : P = R := hmax P ⟨hPnormal, hPconnected, hPsolvable⟩ hRP
  simpa [hPR] using hNP

end Theory.AlgebraicGroup
