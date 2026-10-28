module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalLocalized
public import Theory.GroupTheory.NormalSupplementMaximal
public import Theory.Representation.BinaryFourPointStabilizers

/-!
# Reselecting a local opposite point in the retained row

The actual smaller-orbit point stabilizer is maximal in every remaining
action: natural four or five, orthogonal six, and exterior ten. In the
orthogonal case, maximality in the normal component lifts through the
point-Sylow supplement. The augmentation cover has already been excluded.

This maximal centralizer escapes M and supplies a new original constrained
context at the conjugate local point. The local opposite-point exclusions
then force the new smaller orbit to have full SL₅(2) action and dimension
five or ten. Its kernel still detects the full VI action kernel. Neither
D nor its full moved subgroup is replaced by the local three-space.
Source: Aschbacher--Smith, 10.2.9, printed pp.752--753.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open BinaryNaturalDual.VectorStabilizers
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Every nonzero local point-fixed seed has a maximal point centralizer
in the literal containing join. -/
theorem Context.local_seed_point_maximal_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    IsCoatom (((pointJoin T v I) ⊓ centralizer ({u} : Set G)).subgroupOf
      (pointJoin T v I)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let S := (pointSylow T v).subgroupOf H
  let R := conjugateSpanBy (zpowers u) I
  let U := R.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let q := actionMk U
  let A := K.map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have huR : u ∈ R := le_conjugateSpanBy _ _ (mem_zpowers u)
  have hRVI : R ≤ orbitModule D v I := conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl
  have hRH : R ≤ H := hRVI.trans c.orbit_le_join
  let w : Additive U := Additive.ofMul ⟨⟨u,hRH huR⟩,huR⟩
  have hw : w ≠ 0 := fun he => hne (congrArg (fun a : Additive U => ((a.toMul:H):G)) he)
  let B := representationStabilizer (action U) w
  have hfix (x : H) : q x ∈ B ↔ (x:G) ∈ centralizer ({u} : Set G) := by
    change action U (q x) w = w ↔ _
    constructor
    · intro hx
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun a : Additive U => ((a.toMul:H):G)) hx
      have ha := congrArg H.subtype (action_apply U x w)
      exact mul_inv_eq_iff_eq_mul.mp (ha.symm.trans he)
    · intro hx
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg H.subtype (action_apply U x w)
      exact ha.trans (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx))
  have hSB : S.map q ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hfix x).mpr (mem_centralizer_singleton_iff.mpr (hu.2 x hx))
  have hKS : K ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right),subgroupOf_self]
  have hAB : A ⊔ B = ⊤ := by
    apply top_unique
    have hh : A ⊔ S.map q = ⊤ := by
      rw [←Subgroup.map_sup,hKS,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [←hh]
    exact sup_le_sup_left hSB A
  obtain ⟨P,hP⟩ := c.join_sylow
  obtain ⟨S₀,hS₀⟩ := P.exists_subgroupOf_eq_of_normal K
  let Q := S₀.mapSurjective (q.subgroupMap_surjective K)
  have hQ (a : A) (ha : a ∈ (Q : Subgroup A)) : action U a.val w = w := by
    obtain ⟨x,hx,rfl⟩ := ha
    have hxP : (x:H) ∈ (P : Subgroup H) := by
      change x ∈ (P : Subgroup H).subgroupOf K
      rw [←hS₀]
      exact hx
    have hxS : ((x:H):G) ∈ pointSylow T v := hP ▸ mem_map_of_mem H.subtype hxP
    exact (hfix (x:H)).mpr (mem_centralizer_singleton_iff.mpr (hu.2 _ hxS))
  have hmax : IsCoatom (B.subgroupOf A) := by
    cases c.local_seed_single_action_of_four_natural_cover h hu hne with
    | natural d hd ht E =>
      change A = ⊤ at ht
      rcases hd with rfl | rfl
      · have hh := BinaryFourPointStabilizers.natural_isCoatom
          (E.linearEquiv w) (fun he => hw (E.linearEquiv.map_eq_zero_iff.mp he))
        apply (OrderIso.isCoatom_iff E.groupEquiv.mapSubgroup _).mp
        change IsCoatom ((representationStabilizer ((action U).comp A.subtype) w).map E.groupEquiv.toMonoidHom)
        rw [BinaryNaturalDual.Transport.stabilizer_map _ _ E.groupEquiv E.linearEquiv E.intertwines]
        exact hh
      · have hE := c.local_seed_irreducible_of_binary_five h hu hne E.groupEquiv
        have hma : IsCoatom B := by
          let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype
            (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) _).mp hE.2.1
          let e : ActionQuotient U ≃* SL(5,ZMod 2) :=
            (topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)).trans E.groupEquiv
          exact (BinaryFivePointStabilizers.natural_structure (action U) (action_faithful U) e
            (E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))) w hw).1
        have he : B.subgroupOf A = B.comap A.subtype := rfl
        rw [he]
        exact isCoatom_comap_of_surjective
          (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) hma
    | orthogonal _ model _ =>
      rcases model with hn | ha
      · let E := hn.some
        let Q' := Q.mapSurjective (f := E.groupEquiv.toMonoidHom) E.groupEquiv.surjective
        have hh := BinaryFourPointStabilizers.orthogonal_isCoatom Q' (E.linearEquiv w)
          (fun he => hw (E.linearEquiv.map_eq_zero_iff.mp he)) (by
            rintro _ ⟨a,ha,rfl⟩
            exact (E.intertwines a w).symm.trans (congrArg E.linearEquiv (hQ a ha)))
        apply (OrderIso.isCoatom_iff E.groupEquiv.mapSubgroup _).mp
        change IsCoatom ((representationStabilizer ((action U).comp A.subtype) w).map E.groupEquiv.toMonoidHom)
        rw [BinaryNaturalDual.Transport.stabilizer_map _ _ E.groupEquiv E.linearEquiv E.intertwines]
        exact hh
      · exact (c.no_augmentation_cover_of_local_seed hu hne ha.some).elim
    | exterior E ht hi hd =>
      change A = ⊤ at ht
      let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype
        (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) _).mp hi
      let e : ActionQuotient U ≃* SL(5,ZMod 2) :=
        (topEquiv.symm.trans (MulEquiv.subgroupCongr ht.symm)).trans E
      let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
      have hPB : (P' : Subgroup (ActionQuotient U)) ≤ B := by
        rintro _ ⟨x,hx,rfl⟩
        exact (hfix x).mpr (mem_centralizer_singleton_iff.mpr
          (hu.2 x (hP ▸ mem_map_of_mem H.subtype hx)))
      have hm := (BinaryFivePointStabilizers.exterior_structure (action U) e hd P' w hw hPB).1
      exact isCoatom_comap_of_surjective
        (by intro a; exact ⟨⟨a,ht.symm ▸ mem_top a⟩,rfl⟩) hm
  have hm : IsCoatom B := isCoatom_of_subgroupOf_normal_supplement A B hAB hmax
  have hc : (H ⊓ centralizer ({u} : Set G)).subgroupOf H = B.comap q := by
    ext x
    exact ⟨fun hx => (hfix x).mpr hx.2, fun hx => ⟨x.property,(hfix x).mp hx⟩⟩
  rw [hc]
  exact isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hm

/-- The local-point selection is available for every retained four-natural
cover, including the binary-four containing actions. -/
theorem Context.reselect_local_point_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, Context D t w J ∧
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  apply c.reselect_local_point_of_escaping_centralizer h hu hne
  intro hh
  have hmax := c.local_seed_point_maximal_of_four_natural_cover h hu hne
  apply c.local_seed_point_escapes_of_maximal hu.1 hne hmax
  intro x hx
  have hx' : (MulAut.conj t) x ∈ centralizer ({(MulAut.conj t) u} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp hx.2)
  exact (mem_normalizer_iff.mp
    (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T c.escaping.t_mem)) x).mpr
      (hh hx')

/-- The retained row supplies a new original constrained context at a
local opposite point, with an actual irreducible five- or ten-dimensional
smaller orbit. The same setup D and full moved subgroup are retained. -/
theorem Context.local_binary_five_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let w := (MulAut.conj t) u
    ∃ J : Subgroup G, ∃ c' : Context D t w J,
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom ∧
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) ∧
      ∃ hu' : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T w : Set G),
      let H := pointJoin T w J
      let U := (conjugateSpanBy (zpowers u) J).subgroupOf H
      letI := (c'.local_seed_orbit_reduced hu').normal
      letI := (c'.local_seed_orbit_reduced hu').elementary
      let A := (J.subgroupOf H).map (actionMk U)
      centralizer (U : Set H) = centralizer (internalModule D w J : Set H) ∧
      Nonempty (A ≃* SL(5,ZMod 2)) ∧ A = ⊤ ∧
      IsIrreducible ((action U).comp A.subtype) ∧
      (Module.finrank (ZMod 2) (Additive U) = 5 ∨
        Module.finrank (ZMod 2) (Additive U) = 10) := by
  obtain ⟨J,c',hw,hs⟩ := c.reselect_local_point_of_four_natural_cover h hu hne
  have hu' : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T ((MulAut.conj t) u) : Set G) := by
    rw [hs]
    exact ⟨hu.1,c.local_seed_fixed_by_halfSylow_of_four_natural_cover h hu⟩
  refine ⟨J,c',hw,hs,hu',?_⟩
  exact ⟨c'.local_seed_centralizer_eq_of_four_natural_cover h hu' hne,
    c'.local_seed_five_of_local_four_natural_point h hw hu' hne⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
