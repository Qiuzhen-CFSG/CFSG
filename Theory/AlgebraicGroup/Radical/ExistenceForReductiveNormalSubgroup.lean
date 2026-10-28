module

public import Theory.AlgebraicGroup.Morphism.Connected

public import Theory.AlgebraicGroup.Morphism.Solvable

public import Theory.AlgebraicGroup.Radical.Defs

public import Theory.AlgebraicGroup.Radical.Preimage

public import Theory.AlgebraicGroup.Reductive.Defs

public import Theory.AlgebraicGroup.Semisimple.Defs

/-!
Existence of a radical subgroup containing a prescribed connected normal
solvable closed subgroup.  Following Definition 1.7.1, the proof chooses a
candidate of maximal (finite) dimension.  The supremum of two candidates is
again a candidate: normality and solvability are group-theoretic, while its
carrier is the regular multiplication image of the product of the two closed
subgroups, which gives closedness and connectedness.  Strict dimension growth
under a proper inclusion then proves the required universal containment.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem ClosedSubgroup.exists_le_isRadicalSubgroup
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G)
    (hSnormal : S.toSubgroup.Normal)
    (hSconnected : _root_.IsConnected (S : Set (Variety.Point G)))
    (hSsolvable : Group.IsSolvable (Variety.Point S.carrierVariety)) :
    ∃ R : ClosedSubgroup G, S ≤ R ∧ IsRadicalSubgroup R := by
  classical
  let Good : ClosedSubgroup G → Prop := fun H =>
    H.toSubgroup.Normal ∧
      _root_.IsConnected (H : Set (Variety.Point G)) ∧
        Group.IsSolvable (Variety.Point H.carrierVariety)
  have hSgood : Good S := ⟨hSnormal, hSconnected, hSsolvable⟩
  have join_good (A B : ClosedSubgroup G) (hA : Good A) (hB : Good B) :
      ∃ J : ClosedSubgroup G, Good J ∧ A ≤ J ∧ B ≤ J := by
    let : A.toSubgroup.Normal := hA.1
    let : B.toSubgroup.Normal := hB.1
    let U : Subgroup (Variety.Point G) := A.toSubgroup ⊔ B.toSubgroup
    let fA : Variety.Morphism
        (Variety.prod A.carrierVariety B.carrierVariety) G :=
      A.inclusion.toVariety.comp
        (Variety.Morphism.fst A.carrierVariety B.carrierVariety)
    let fB : Variety.Morphism
        (Variety.prod A.carrierVariety B.carrierVariety) G :=
      B.inclusion.toVariety.comp
        (Variety.Morphism.snd A.carrierVariety B.carrierVariety)
    let f : Variety.Morphism
        (Variety.prod A.carrierVariety B.carrierVariety) G :=
      (Theory.AlgebraicGroup.mulMorphism G).comp (fA.pair fB)
    have hf_apply
        (x : Variety.Point (Variety.prod A.carrierVariety B.carrierVariety)) :
        f.toFun x =
          A.inclusion.onPoints
              (Variety.prodPointEquiv A.carrierVariety B.carrierVariety x).1 *
            B.inclusion.onPoints
              (Variety.prodPointEquiv A.carrierVariety B.carrierVariety x).2 := by
      rfl
    have hf_range : Set.range f.toFun = (U : Set (Variety.Point G)) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        rw [hf_apply]
        exact Subgroup.mul_mem_sup
          (A.pointEquiv
            (Variety.prodPointEquiv A.carrierVariety B.carrierVariety x).1).property
          (B.pointEquiv
            (Variety.prodPointEquiv A.carrierVariety B.carrierVariety x).2).property
      · intro hz
        rcases Subgroup.mem_sup_of_normal_right.mp hz with
          ⟨a, ha, b, hb, hab⟩
        let a' : Variety.Point A.carrierVariety :=
          A.pointEquiv.symm ⟨a, ha⟩
        let b' : Variety.Point B.carrierVariety :=
          B.pointEquiv.symm ⟨b, hb⟩
        refine ⟨(Variety.prodPointEquiv A.carrierVariety B.carrierVariety).symm
          (a', b'), ?_⟩
        rw [hf_apply, Equiv.apply_symm_apply]
        change (A.pointEquiv a').val * (B.pointEquiv b').val = z
        rw [A.pointEquiv.apply_symm_apply, B.pointEquiv.apply_symm_apply]
        exact hab
    have hUclosed : IsZariskiClosed G (U : Set (Variety.Point G)) := by
      rw [← Variety.isClosed_iff_isZariskiClosed]
      apply constructible_subgroup_isClosed G U
      rw [← hf_range]
      exact f.range_isConstructible
    let J : ClosedSubgroup G := ClosedSubgroup.ofSubgroup U hUclosed
    have hJnormal : J.toSubgroup.Normal := by
      change U.Normal
      infer_instance
    have hJconnected :
        _root_.IsConnected (J : Set (Variety.Point G)) := by
      have hAvar : Variety.IsConnected A.carrierVariety := by
        let e := Variety.closedSubvarietyPointHomeomorph A.isZariskiClosed
        let : ConnectedSpace
            {x : Variety.Point G // x ∈ (A : Set (Variety.Point G))} :=
          Subtype.connectedSpace hA.2.1
        let : ConnectedSpace (Variety.Point A.carrierVariety) :=
          e.connectedSpace_iff.mpr inferInstance
        exact connectedSpace_iff_univ.mp inferInstance
      have hBvar : Variety.IsConnected B.carrierVariety := by
        let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
        let : ConnectedSpace
            {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
          Subtype.connectedSpace hB.2.1
        let : ConnectedSpace (Variety.Point B.carrierVariety) :=
          e.connectedSpace_iff.mpr inferInstance
        exact connectedSpace_iff_univ.mp inferInstance
      have hsource : _root_.IsConnected
          (Set.univ : Set (Variety.Point
            (Variety.prod A.carrierVariety B.carrierVariety))) := by
        apply IsIrreducible.isConnected
        simpa [Variety.prodSet] using
          (prodSet_irreducible_of_irreducible
            (connectedAlgebraicGroup_irreducible A.carrierVariety hAvar)
            (connectedAlgebraicGroup_irreducible B.carrierVariety hBvar))
      have himage := hsource.image f.toFun f.continuous.continuousOn
      change _root_.IsConnected (U : Set (Variety.Point G))
      rw [← hf_range]
      simpa [Set.image_univ] using himage
    have hAsolvable : Group.IsSolvable A.toSubgroup := by
      let : Group.IsSolvable (Variety.Point A.carrierVariety) := hA.2.2
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv A.pointEquiv).toMonoidHom)
        A.pointEquiv.surjective
    have hBsolvable : Group.IsSolvable B.toSubgroup := by
      let : Group.IsSolvable (Variety.Point B.carrierVariety) := hB.2.2
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv B.pointEquiv).toMonoidHom)
        B.pointEquiv.surjective
    have hUsolvable : Group.IsSolvable U := by
      let : Group.IsSolvable A.toSubgroup := hAsolvable
      let : Group.IsSolvable B.toSubgroup := hBsolvable
      let q : U →* Variety.Point G ⧸ A.toSubgroup :=
        (QuotientGroup.mk' A.toSubgroup).comp U.subtype
      let q' : U →* q.range := q.rangeRestrict
      have hqrange : Group.IsSolvable q.range := by
        let bq : B.toSubgroup →* q.range :=
          q'.comp (Subgroup.inclusion (show B.toSubgroup ≤ U from le_sup_right))
        have hbq : Function.Surjective bq := by
          intro y
          rcases y.property with ⟨x, hx⟩
          rcases Subgroup.mem_sup_of_normal_right.mp x.property with
            ⟨a, ha, b, hb, hab⟩
          refine ⟨⟨b, hb⟩, ?_⟩
          apply Subtype.ext
          change q ⟨b, (show B.toSubgroup ≤ U from le_sup_right) hb⟩ = y.val
          rw [← hx]
          change (QuotientGroup.mk' A.toSubgroup) b =
            (QuotientGroup.mk' A.toSubgroup) x.val
          rw [← hab, map_mul]
          have haone : (QuotientGroup.mk' A.toSubgroup) a = 1 := by
            exact (QuotientGroup.eq_one_iff a).mpr ha
          rw [haone, one_mul]
        exact Group.isSolvable_of_surjective (f := bq) hbq
      let : Group.IsSolvable q.range := hqrange
      let iA : A.toSubgroup →* U :=
        Subgroup.inclusion (show A.toSubgroup ≤ U from le_sup_left)
      have hker : q'.ker ≤ iA.range := by
        intro x hx
        have hxq' : q' x = 1 := MonoidHom.mem_ker.mp hx
        have hxq : q x = 1 := congrArg Subtype.val hxq'
        have hxA : x.val ∈ A.toSubgroup := by
          change (QuotientGroup.mk' A.toSubgroup) x.val = 1 at hxq
          exact (QuotientGroup.eq_one_iff x.val).mp hxq
        exact ⟨⟨x.val, hxA⟩, rfl⟩
      exact Group.isSolvable_of_ker_le_range iA q' hker
    have hJsolvable :
        Group.IsSolvable (Variety.Point J.carrierVariety) := by
      let : Group.IsSolvable J.toSubgroup := by
        change Group.IsSolvable U
        exact hUsolvable
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Equiv.mulEquiv J.pointEquiv).toMonoidHom)
        J.pointEquiv.injective
    refine ⟨J, ⟨hJnormal, hJconnected, hJsolvable⟩, ?_, ?_⟩
    · intro x hx
      change x ∈ U
      exact (show A.toSubgroup ≤ U from le_sup_left) hx
    · intro x hx
      change x ∈ U
      exact (show B.toSubgroup ≤ U from le_sup_right) hx
  let dimNat : ClosedSubgroup G → ℕ := fun H =>
    Cardinal.toNat (Variety.dimension H.carrierVariety)
  let candidates : Set (ClosedSubgroup G) := {H | Good H}
  have hdim_le (H : ClosedSubgroup G) :
      dimNat H ≤ Cardinal.toNat (Variety.dimension G) := by
    apply (Cardinal.toNat_le_iff_le_of_lt_aleph0
      (variety_dimension_lt_aleph0 H.carrierVariety)
      (variety_dimension_lt_aleph0 G)).2
    exact closedSubvariety_dimension_le G H.isZariskiClosed
  have hdim_finite : (dimNat '' candidates).Finite := by
    apply (Set.finite_le_nat (Cardinal.toNat (Variety.dimension G))).subset
    rintro n ⟨H, _, rfl⟩
    exact hdim_le H
  obtain ⟨R, hRgood, hRmax⟩ :=
    Set.Finite.exists_maximalFor' dimNat candidates hdim_finite
      ⟨S, hSgood⟩
  have hmax (H : ClosedSubgroup G) (hHgood : Good H) :
      dimNat H ≤ dimNat R := by
    by_cases hle : dimNat R ≤ dimNat H
    · exact hRmax hHgood hle
    · exact le_of_not_ge hle
  have hcontains (N : ClosedSubgroup G) (hNnormal : N.toSubgroup.Normal)
      (hNconnected : _root_.IsConnected (N : Set (Variety.Point G)))
      (hNsolvable : Group.IsSolvable (Variety.Point N.carrierVariety)) :
      N ≤ R := by
    have hNgood : Good N := ⟨hNnormal, hNconnected, hNsolvable⟩
    obtain ⟨J, hJgood, hRJ, hNJ⟩ := join_good R N hRgood hNgood
    have hdimJR :
        Variety.dimension J.carrierVariety ≤
          Variety.dimension R.carrierVariety := by
      apply (Cardinal.toNat_le_iff_le_of_lt_aleph0
        (variety_dimension_lt_aleph0 J.carrierVariety)
        (variety_dimension_lt_aleph0 R.carrierVariety)).1
      exact hmax J hJgood
    have hRJ_eq : R = J := by
      by_contra hne
      have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
        R J hRJ hne hRgood.2.1 hJgood.2.1
      exact (not_lt_of_ge hdimJR) hlt
    rwa [← hRJ_eq] at hNJ
  refine ⟨R, hcontains S hSnormal hSconnected hSsolvable, ?_⟩
  exact ⟨hRgood.1, hRgood.2.1, hRgood.2.2, hcontains⟩

end Theory.AlgebraicGroup
