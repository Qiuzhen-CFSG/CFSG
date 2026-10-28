module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSupplement
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSupplement
public import Theory.SpecificGroups.G2.OddSupplement
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Odd Sylow actors fix the actual natural flag residuals

The two maximal overgroups of the inner Sylow in each marked rank-two model
exhaust its proper overgroups. This pair lifts through the literal two-core
quotient of L; for SL₃ it first lifts through the scalar center, using
perfectness. The actual point and plane stabilizers are maximal, so each is
one of the pair. An odd subgroup normalizing both the original T and L
therefore fixes both stabilizers and their solvable residuals.

These statements use the supplied natural marking, the actual preimages Vᵢ,
and the literal N_L(Vᵢ). The consumer in JankoReduction.NormalizerEscape
applies them to K intersect A; no normalization of the original module by this
intersection is assumed.

Source: Aschbacher--Smith, 3.3.15--16, printed pp.590--591, with the
natural flag of 11.0.2 and opening section 11.1, pp.759--761.
The concrete model APIs retain their ATLAS attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private def TwoMaximalOvergroups {H : Type*} [Group H] (U : Subgroup H) : Prop :=
  ∃ P Q : Subgroup H, IsCoatom P ∧ IsCoatom Q ∧ U ≤ P ∧ U ≤ Q ∧
    ∀ J : Subgroup H, U ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q

private theorem lift_twoMaximal {H K : Type*} [Group H] [Group K]
    (q : H →* K) (hq : Function.Surjective q) (U : Subgroup H)
    (hproper : ∀ J : Subgroup H, U ≤ J → J ≠ ⊤ → J.map q ≠ ⊤)
    (h : TwoMaximalOvergroups (U.map q)) : TwoMaximalOvergroups U := by
  obtain ⟨P,Q,hP,hQ,hUP,hUQ,hcover⟩ := h
  refine ⟨P.comap q,Q.comap q,isCoatom_comap_of_surjective hq hP,
    isCoatom_comap_of_surjective hq hQ,map_le_iff_le_comap.mp hUP,
    map_le_iff_le_comap.mp hUQ,?_⟩
  intro J hUJ hJ
  rcases hcover (J.map q) (map_mono hUJ) (hproper J hUJ hJ) with hp | hq
  · exact .inl (map_le_iff_le_comap.mp hp)
  · exact .inr (map_le_iff_le_comap.mp hq)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field}

private theorem model_twoMaximal (c : Coordinates D S.field)
    (U : Sylow 2 c.ModelGroup) : TwoMaximalOvergroups (U : Subgroup c.ModelGroup) := by
  cases c with
  | sl3 m =>
    change Sylow 2 SL(3,S.field.Carrier) at U
    let F := S.field.Carrier
    let q : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (center SL(3,F))
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hz : q.ker ≤ center SL(3,F) := by rw [QuotientGroup.ker_mk']
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    apply lift_twoMaximal q hq (U : Subgroup SL(3,F))
    · intro J _ hJ he
      apply hJ
      apply top_unique
      apply perfect_le_of_map_le_of_central_kernel q hz (⊤ : Subgroup SL(3,F)) J
      rw [he]
      exact le_top
    · obtain ⟨P,Q,hP,hQ,hUP,hUQ,_,hcover⟩ :=
        Matrix.PSL3.LinearThree.OddSupplement.two_sylow_overgroups_of_equiv
          S.field.card_eq (by have := S.nonbinary; omega) (MulEquiv.refl (PSL(3,F)))
          (U.mapSurjective hq)
      exact ⟨P,Q,hP,hQ,hUP,hUQ,hcover⟩
  | sp4 m =>
    obtain ⟨P,Q,hP,hQ,hUP,hUQ,_,hcover⟩ :=
      Theory.SpecificGroups.SymplecticFour.two_sylow_overgroups_of_equiv
        S.field.card_eq (by have := S.nonbinary; omega)
        (MulEquiv.refl (Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)) U
    exact ⟨P,Q,hP,hQ,hUP,hUQ,hcover⟩
  | g2 m =>
    obtain ⟨P,Q,hP,hQ,hUP,hUQ,_,hcover⟩ :=
      Atlas.G2.two_sylow_overgroups_of_equiv (MulEquiv.refl (Atlas.G2.Model S.field.Carrier)) U
    exact ⟨P,Q,hP,hQ,hUP,hUQ,hcover⟩

private theorem component_twoMaximal (c : Coordinates D S.field) :
    TwoMaximalOvergroups ((T : Subgroup G).subgroupOf L) := by
  obtain ⟨U,hU⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  have hk : c.quotientMap.ker = pCore 2 L := by
    ext l
    change c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
    rw [map_eq_one_iff _ c.groupEquiv.injective]
    exact QuotientGroup.eq_one_iff l
  have hker : c.quotientMap.ker ≤ (T : Subgroup G).subgroupOf L := by
    rw [hk,←hU]
    exact pCore_isPGroup.le_sylow_of_normal U
  apply lift_twoMaximal c.quotientMap c.quotientMap_surjective
  · intro J hUJ hJ he
    apply hJ
    have hh := congrArg (Subgroup.comap c.quotientMap) he
    simpa only [comap_map_eq,comap_top,sup_eq_left.mpr (hker.trans hUJ)] using hh
  · have h := model_twoMaximal c (U.mapSurjective c.quotientMap_surjective)
    change TwoMaximalOvergroups ((U : Subgroup L).map c.quotientMap) at h
    rwa [hU] at h

private theorem flag_eq {c : Coordinates D S.field} (f g : InvariantFlag c)
    (hg : g.IsUnique) : f = g := by
  have hs : f.space = g.space := funext fun i => hg i (f.space i) (f.dimension i) (f.invariant i)
  cases f; cases g; cases hs; rfl

/-- Both actual marked flag stabilizers are maximal in the full model group. -/
theorem flag_modelStabilizer_isCoatom (f : InvariantFlag c) (i : Fin 2) :
    IsCoatom (c.modelStabilizer (f.space i.castSucc)) := by
  cases c with
  | sl3 m =>
    rw [flag_eq f (SL3.flag D S m) (SL3.flag_unique D S m)]
    have he : (Coordinates.sl3 m).modelStabilizer ((SL3.flag D S m).space i.castSucc) =
        (SL3.PlaneAction.parabolic i).comap
          (MulAut.conj (SL3.alignment D S m)⁻¹).toMonoidHom := by
      ext g
      exact SL3.PlaneAction.aligned_stabilizer _ _ i
    rw [he]
    apply isCoatom_comap_of_surjective (MulAut.conj _).surjective
    fin_cases i
    · exact Matrix.PSL3.LinearThree.pointParabolicSL_isCoatom _
    · exact Matrix.PSL3.LinearThree.lineParabolicSL_isCoatom _
  | sp4 m =>
    rw [flag_eq f (Sp4.flag m S) (Sp4.flag_unique m S)]
    change IsCoatom ((Coordinates.sp4 m).modelStabilizer (Sp4.space m i.castSucc.succ))
    rw [Sp4.modelStabilizer_space]
    apply ((MulAut.conj (Sp4.alignment m)).mapSubgroup.isCoatom_iff _).mpr
    fin_cases i
    · exact Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.pointParabolic_isCoatom
    · exact Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.planeParabolic_isCoatom
  | g2 m =>
    rw [flag_eq f (G2.flag S m) (G2.flag_unique S m)]
    rw [G2.ResidualIncidence.modelStabilizer_flag]
    apply ((MulAut.conj (G2.ResidualIncidence.alignment S m).val).mapSubgroup.isCoatom_iff _).mpr
    fin_cases i
    · exact Atlas.G2.HigherFieldResiduals.parabolic₂_isCoatom
    · exact Atlas.G2.HigherFieldResiduals.parabolic₁_isCoatom

/-- The literal N_L(V_i), regarded inside L, is a maximal subgroup of L. -/
theorem flag_normalizer_isCoatom (f : InvariantFlag c) (i : Fin 2) :
    IsCoatom ((normalizer (f.Vi i.castSucc : Set G)).subgroupOf L) := by
  have he : (normalizer (f.Vi i.castSucc : Set G)).subgroupOf L =
      (c.modelStabilizer (f.space i.castSucc)).comap c.quotientMap := by
    ext l
    exact c.mem_normalizer_preimage_iff (f.space i.castSucc) l
  rw [he]
  exact isCoatom_comap_of_surjective c.quotientMap_surjective
    (flag_modelStabilizer_isCoatom f i)

/-- An odd subgroup normalizing the original T and L fixes both full flag
parabolics. The proof uses the actual rank-two maximal-subgroup pair. -/
theorem odd_normalizes_flag_normalizer (f : InvariantFlag c) (B : Subgroup G)
    (ho : Odd (Nat.card B)) (hBT : B ≤ normalizer (T : Set G))
    (hBL : B ≤ normalizer (L : Set G)) (i : Fin 2) :
    B ≤ normalizer ((L ⊓ normalizer (f.Vi i.castSucc : Set G) : Subgroup G) : Set G) := by
  let U := (T : Subgroup G).subgroupOf L
  let R := (normalizer (f.Vi i.castSucc : Set G)).subgroupOf L
  let a : B →* MulAut L := L.normalizerMonoidHom.comp (inclusion hBL)
  have hR : IsCoatom R := flag_normalizer_isCoatom f i
  have hUR : U ≤ R := comap_mono (f.invariant i.castSucc)
  obtain ⟨P,Q,hP,hQ,hUP,hUQ,hcover⟩ := component_twoMaximal c
  have perm (b : B) (J : Subgroup L) (hJ : J = P ∨ J = Q) :
      J.map (a b).toMonoidHom = P ∨ J.map (a b).toMonoidHom = Q := by
    have hc : IsCoatom J := hJ.elim (fun he => he ▸ hP) (fun he => he ▸ hQ)
    have hUJ : U ≤ J := hJ.elim (fun he => he ▸ hUP) (fun he => he ▸ hUQ)
    have hm := ((a b).mapSubgroup.isCoatom_iff J).mpr hc
    have hu : U.map (a b).toMonoidHom = U := by
      apply le_antisymm
      · rintro _ ⟨u,hu,rfl⟩
        exact (hBT b.property u).mp hu
      · intro u hu
        refine ⟨(a b)⁻¹ u,?_,(a b).apply_symm_apply u⟩
        exact (hBT (B.inv_mem b.property) u).mp hu
    have huj : U ≤ J.map (a b).toMonoidHom := by
      rw [←hu]
      exact map_mono hUJ
    rcases hcover _ huj hm.ne_top with hp | hq
    · exact .inl ((hm.le_iff_eq hP.ne_top).mp hp).symm
    · exact .inr ((hm.le_iff_eq hQ.ne_top).mp hq).symm
  have hpair : R = P ∨ R = Q := by
    rcases hcover R hUR hR.ne_top with hp | hq
    · exact .inl ((hR.le_iff_eq hP.ne_top).mp hp).symm
    · exact .inr ((hR.le_iff_eq hQ.ne_top).mp hq).symm
  have hf := odd_preserves_pair a ho hpair perm
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he := congrArg (Subgroup.map L.subtype) (hf ⟨b,hb⟩)
  have hc : L.subtype.comp (a ⟨b,hb⟩).toMonoidHom =
      (MulAut.conj b).toMonoidHom.comp L.subtype := by ext l; rfl
  rw [map_map,hc,←map_map,subgroupOf_map_subtype,inf_comm] at he
  exact he

/-- Odd actors in N_G(T) ∩ N_G(L) normalize each original flag residual. -/
theorem odd_normalizes_flag_residual (f : InvariantFlag c) (B : Subgroup G)
    (ho : Odd (Nat.card B)) (hBT : B ≤ normalizer (T : Set G))
    (hBL : B ≤ normalizer (L : Set G)) (i : Fin 2) :
    B ≤ normalizer (f.Li i : Set G) :=
  (odd_normalizes_flag_normalizer f B ho hBT hBL i).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
