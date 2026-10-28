module
public import Theory.GroupTheory.ElementaryEightPlaneOrder24
public import Theory.GroupTheory.ElementaryEightNormalizerRecognition

/-!
# A full plane and a mover in an elementary-eight normalizer

Let U be elementary abelian of order eight. Suppose its actual conjugation
image contains a subgroup J of order twenty-four preserving a plane W, and
an element moving W. Then the normalizer of U is nonsolvable, and its
quotient by the actual centralizer is PSL₃(2). No self-centralization or
faithfulness of the ambient conjugation action is assumed.

The full plane stabilizer J is S₄. Its conjugate by the given mover preserves
the moved plane; uniqueness of the invariant plane of an order-twenty-four
image makes these two S₄ subgroups distinct. The existing elementary-eight
normalizer recognition supplies nonsolvability and the exact quotient kernel.

This source-independent finite-group step supports Stellmacher (8.6)(c4),
printed p.44, and the extraspecial-order27 exclusion before (10.1)(14),
printed p.63 of `refs/files/stellmacher-n-group.pdf`.
-/

private theorem two_symmetric_four_images_of_plane_mover
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (W : Subgroup U) (hW : Nat.card W = 4)
    (J : Subgroup (MulAut U)) (hJ : Nat.card J = 24)
    (hJR : J ≤ U.normalizerMonoidHom.range)
    (hstable : ∀ j : J, ∀ v : U, (j : MulAut U) v ∈ W ↔ v ∈ W)
    (e : MulAut U) (he : e ∈ U.normalizerMonoidHom.range)
    (hmoved : W.map e.toMonoidHom ≠ W) :
    ∃ X Y : Subgroup U.normalizerMonoidHom.range, X ≠ Y ∧
      Nonempty (X ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (Y ≃* Equiv.Perm (Fin 4)) := by
  classical
  let K := J.map (MulAut.conj e).toMonoidHom
  let C := W.map e.toMonoidHom
  have hC : Nat.card C = 4 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hW
  have hKC : ∀ k : K, ∀ v : U, (k : MulAut U) v ∈ C ↔ v ∈ C := by
    rintro ⟨k, j, hj, rfl⟩ v
    change ((MulAut.conj e) j) v ∈ W.map e.toMonoidHom ↔ v ∈ W.map e.toMonoidHom
    simp only [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact hstable ⟨j,hj⟩ _
  have hne : J ≠ K := by
    intro heq
    have hJC : ∀ j : J, ∀ v : U, (j : MulAut U) v ∈ C ↔ v ∈ C := by
      intro j v
      exact hKC ⟨j,heq ▸ j.property⟩ v
    exact hmoved (elementaryEight_plane_order24_unique hU W C hW hC J hJ hstable hJC).symm
  have hKR : K ≤ U.normalizerMonoidHom.range := by
    rintro k ⟨j,hj,rfl⟩
    exact U.normalizerMonoidHom.range.mul_mem
      (U.normalizerMonoidHom.range.mul_mem he (hJR hj))
      (U.normalizerMonoidHom.range.inv_mem he)
  let X := J.subgroupOf U.normalizerMonoidHom.range
  let Y := K.subgroupOf U.normalizerMonoidHom.range
  have hXY : X ≠ Y := by
    intro h
    have hh := congrArg (fun S : Subgroup U.normalizerMonoidHom.range =>
      S.map U.normalizerMonoidHom.range.subtype) h
    apply hne
    simpa only [X,Y,Subgroup.map_subgroupOf_eq_of_le hJR,
      Subgroup.map_subgroupOf_eq_of_le hKR] using hh
  have hX : Nonempty (X ≃* Equiv.Perm (Fin 4)) := by
    obtain ⟨model⟩ := elementaryEight_plane_order24_equiv_S4 hU W hW J hJ hstable
    exact ⟨(Subgroup.subgroupOfEquivOfLe hJR).trans model⟩
  have hY : Nonempty (Y ≃* Equiv.Perm (Fin 4)) := by
    obtain ⟨model⟩ := hX
    exact ⟨(Subgroup.subgroupOfEquivOfLe hKR).trans
      ((J.equivMapOfInjective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hJR).symm.trans model))⟩
  exact ⟨X,Y,hXY,hX,hY⟩

public theorem elementaryEight_normalizer_centralizer_quotient_of_full_plane_mover
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (W : Subgroup U) (hW : Nat.card W = 4)
    (J : Subgroup (MulAut U)) (hJ : Nat.card J = 24)
    (hJR : J ≤ U.normalizerMonoidHom.range)
    (hstable : ∀ j : J, ∀ v : U, (j : MulAut U) v ∈ W ↔ v ∈ W)
    (e : MulAut U) (he : e ∈ U.normalizerMonoidHom.range)
    (hmoved : W.map e.toMonoidHom ≠ W) :
    ∃ f : Subgroup.normalizer (U : Set G) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ f.ker = (Subgroup.centralizer (U : Set G)).subgroupOf
        (Subgroup.normalizer (U : Set G)) := by
  obtain ⟨X,Y,hXY,hX,hY⟩ := two_symmetric_four_images_of_plane_mover U hU W hW J hJ hJR hstable e he hmoved
  exact elementaryEight_normalizer_centralizer_quotient_PSL3 U hU X Y hXY hX hY

public theorem elementaryEight_normalizer_not_isSolvable_of_full_plane_mover
    {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (W : Subgroup U) (hW : Nat.card W = 4)
    (J : Subgroup (MulAut U)) (hJ : Nat.card J = 24)
    (hJR : J ≤ U.normalizerMonoidHom.range)
    (hstable : ∀ j : J, ∀ v : U, (j : MulAut U) v ∈ W ↔ v ∈ W)
    (e : MulAut U) (he : e ∈ U.normalizerMonoidHom.range)
    (hmoved : W.map e.toMonoidHom ≠ W) :
    ¬ Group.IsSolvable (Subgroup.normalizer (U : Set G)) := by
  obtain ⟨X,Y,hXY,hX,hY⟩ := two_symmetric_four_images_of_plane_mover U hU W hW J hJ hJR hstable e he hmoved
  exact elementaryEight_normalizer_not_isSolvable_of_two_symmetric_four_images U hU X Y hXY hX hY

