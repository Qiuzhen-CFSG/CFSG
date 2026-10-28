module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Normality and self-centralization for the intrinsic generalized Fitting subgroup

The generalized Fitting subgroup is normal by intrinsic conjugation of its
normal nilpotent and subnormal quasisimple generators.  We also record the
extraspecial finite 2-group specialization needed by the local quasithin
arguments: an extraspecial 2-group is nilpotent, so its Fitting subgroup and
therefore its generalized Fitting subgroup are the whole group.

The arbitrary finite-group self-centralization theorem requires the deeper
component/minimal-normal quotient theory developed in the source-facing
Gorenstein--Walter files.  This Theory module keeps the lower architectural
boundary and proves the specialization that has no such dependency.
-/

@[expose] public section

namespace Theory.GroupTheory

variable {G : Type*} [Group G]

private theorem isQuasisimple_conj_map
    {K : Subgroup G} (g : G) (hK : IsQuasisimple (↥K)) :
    IsQuasisimple (↥(K.map (MulAut.conj g).toMonoidHom)) := by
  let K' : Subgroup G := K.map (MulAut.conj g).toMonoidHom
  let e : (↥K) ≃* (↥K') := (MulAut.conj g).subgroupMap K
  have hcenter : (Subgroup.center (↥K)).map e.toMonoidHom =
      Subgroup.center (↥K') := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr e ⟨y, hy⟩).property
    · intro x hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property
      · exact e.apply_symm_apply x
  have hperfK : Group.IsPerfect (↥K) := @IsQuasisimple.toIsPerfect (↥K) _ hK
  have hperf : Group.IsPerfect (↥K') := by
    exact @Group.IsPerfect.ofSurjective (↥K) (↥K') _ _ e.toMonoidHom hperfK e.surjective
  have hsimple : IsSimpleGroup ((↥K') ⧸ Subgroup.center (↥K')) := by
    let q : (↥K) ⧸ Subgroup.center (↥K) ≃* (↥K') ⧸ Subgroup.center (↥K') :=
      QuotientGroup.congr (Subgroup.center (↥K)) (Subgroup.center (↥K')) e hcenter
    exact (MulEquiv.isSimpleGroup_congr q).mp (@IsQuasisimple.simple (↥K) _ hK)
  exact @IsQuasisimple.mk (↥K') _ hperf hsimple

private theorem isComponent_conj_map
    {K : Subgroup G} (g : G) (hK : IsComponent G K) :
    IsComponent G (K.map (MulAut.conj g).toMonoidHom) := by
  exact ⟨hK.1.map (MulAut.conj g).surjective, isQuasisimple_conj_map g hK.2⟩

/-- The intrinsic generalized Fitting subgroup is normal. -/
public instance generalizedFitting_normal [Finite G] :
    (generalizedFitting G).Normal := by
  let E : Subgroup G := componentLayer G
  have hE : E.Normal := by
    apply (Subgroup.normalizer_eq_top_iff).mp
    apply le_antisymm le_top
    rw [Subgroup.le_normalizer_iff]
    intro g _gE x hxE
    dsimp [E] at hxE
    rw [componentLayer, sSup_eq_iSup', Subgroup.iSup_eq_closure] at hxE
    have hgen : ∀ y : G,
        y ∈ ⋃ K : {K : Subgroup G // IsComponent G K}, (K.1 : Set G) →
          g * y * g⁻¹ ∈ E := by
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨K, hyK⟩
      let K' : Subgroup G := K.1.map (MulAut.conj g).toMonoidHom
      have hK' : IsComponent G K' := isComponent_conj_map g K.2
      have hmem : g * y * g⁻¹ ∈ K' := by
        exact Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
      exact Subgroup.mem_sSup_of_mem hK' hmem
    refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hxE
    · intro y hy
      simpa [mul_assoc] using E.inv_mem (hgen y hy)
    · simp [E]
    · intro a b _ha _hb hga hgb
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using E.mul_mem hga hgb
  have hsup : (fittingSubgroup G ⊔ componentLayer G).Normal := by infer_instance
  simpa [generalizedFitting] using hsup

/-- The generalized Fitting subgroup is self-centralizing whenever the
Fitting subgroup is the whole finite group (in particular for extraspecial
finite 2-groups). -/
public theorem centralizer_generalizedFitting_le_of_fitting_eq_top
    (G : Type*) [Group G] [Finite G]
    (hF : fittingSubgroup G = ⊤) :
    Subgroup.centralizer ((generalizedFitting G : Subgroup G) : Set G) ≤
      generalizedFitting G := by
  rw [generalizedFitting, hF, top_sup_eq]
  exact le_top

/-- An extraspecial finite 2-group has trivial generalized-Fitting quotient:
its intrinsic generalized Fitting subgroup is the whole group. -/
public theorem generalizedFitting_eq_top_of_isExtraspecial_two
    (G : Type*) [Group G] [Finite G] [IsExtraspecial 2 G] :
    generalizedFitting G = ⊤ := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hP : IsPGroup 2 G := IsExtraspecial.isPGroup 2 G
  have hnil : Group.IsNilpotent G := hP.isNilpotent
  have hF : fittingSubgroup G = ⊤ := fitting_eq_top_of_nilpotent G
  rw [generalizedFitting, hF, top_sup_eq]

/-- The generalized Fitting subgroup of an extraspecial finite 2-group is
self-centralizing. -/
public theorem centralizer_generalizedFitting_le_of_isExtraspecial_two
    (G : Type*) [Group G] [Finite G] [IsExtraspecial 2 G] :
    Subgroup.centralizer ((generalizedFitting G : Subgroup G) : Set G) ≤
      generalizedFitting G := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hP : IsPGroup 2 G := IsExtraspecial.isPGroup 2 G
  have hnil : Group.IsNilpotent G := hP.isNilpotent
  apply centralizer_generalizedFitting_le_of_fitting_eq_top G
  exact fitting_eq_top_of_nilpotent G

end Theory.GroupTheory

end
