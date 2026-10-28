module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.FirstResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Orientation
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# The common second residual of the field-four triangle

A proper local subgroup normalized by the full Sylow subgroup is contained
in a point or plane parabolic of each marked rank-two model. Inner uniqueness
identifies its flag, and rank-one covering identifies the local subgroup with
the corresponding residual. Since the reselected first residual is K₀, the
original L₂ is the reselected second residual; their literal two-cores agree.

The common nonsolvable subgroup L₂ also forces either vertex normalizing the
other to lie in it. Maximality and K₀ ≰ L rule this out in both orientations.
This supplies escape without a triangle-generation or component-placement
hypothesis. The consumer in Forward/Exclusion applies both comparisons to the
original chosen geometry.
Source: Aschbacher–Smith, 11.1.2(3), pp.762–764, and 11.4.1(2), p.776.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) (S : D.NonbinaryNaturalInput)

private theorem local_eq_one_of_flag_residuals
    {c : Coordinates D S.field} (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (hcover : ∀ H : Subgroup c.ModelGroup, (c.modelSylow : Subgroup _) ≤ H → H ≠ ⊤ →
      ∃ (i : Fin 2) (W : Submodule S.field.Carrier c.Space),
        Module.finrank S.field.Carrier W = i.val + 1 ∧ H ≤ c.modelStabilizer W)
    (A : Subgroup G) (hA : A ∈ Chapter1.L G T) (hAI : A < I)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A = f.Li 0 ∨ A = f.Li 1 := by
  let B := A.subgroupOf I
  let P := (c.innerSylow : Subgroup I)
  let H := (B ⊔ P).map c.quotientMap
  have hPB : P ≤ normalizer (B : Set I) := by
    rw [← subgroupOf_normalizer_eq hAI.le]
    dsimp only [P]
    rw [c.innerSylow_coe]
    exact comap_mono hTA
  have hPH : (c.modelSylow : Subgroup c.ModelGroup) ≤ H := map_mono le_sup_right
  have hH : H ≠ ⊤ := by
    intro ht
    have hk : c.quotientMap.ker ≤ P := by
      rw [Coordinates.quotientMap,
        MonoidHom.ker_comp_of_injective _ _ c.groupEquiv.injective,
        QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal c.innerSylow
    have htop : B ⊔ P = ⊤ := by
      have he : (B ⊔ P).map c.quotientMap = ⊤ := ht
      rw [← comap_map_eq_self (hk.trans le_sup_right), he, comap_top]
    let : B.Normal := normalizer_eq_top_iff.mp
      (top_unique (htop ▸ sup_le B.le_normalizer hPB))
    let : Group.IsNilpotent (I ⧸ B) :=
      (isPGroup_quotient_of_sup_eq_top B P c.innerSylow.isPGroup' htop).isNilpotent
    let : Group.IsPerfect I := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
    have hB : B = ⊤ := top_unique (by
      simpa only [solvableResidual_eq_top] using solvableResidual_le_of_solvable_quotient B)
    exact hAI.ne (le_antisymm hAI.le (subgroupOf_eq_top.mp hB))
  obtain ⟨i, W, hd, hHW⟩ := hcover H hPH hH
  have hPW : (T : Subgroup G) ⊓ I ≤ normalizer (c.preimage W : Set G) := by
    intro x hx
    apply (c.mem_normalizer_preimage_iff W ⟨x, hx.2⟩).mpr
    apply hHW
    apply mem_map_of_mem
    apply mem_sup_right
    dsimp only [P]
    rw [c.innerSylow_coe]
    exact hx.1
  have he : W = f.space i.castSucc := hu i.castSucc W hd hPW
  have hAN : A ≤ normalizer (f.Vi i.castSucc : Set G) := by
    intro a ha
    change a ∈ normalizer (c.preimage (f.space i.castSucc) : Set G)
    rw [← he]
    apply (c.mem_normalizer_preimage_iff W ⟨a, hAI.le ha⟩).mpr
    exact hHW (mem_map_of_mem _ (mem_sup_left (show (⟨a,hAI.le ha⟩ : I) ∈ B from ha)))
  let : Group.IsPerfect A := Chapter1.mem_L_isPerfect hA
  have heq := local_eq_flag_residual D S f i A hA
    (le_map_solvableResidual_of_isPerfect A (I ⊓ normalizer (f.Vi i.castSucc : Set G))
      (le_inf hAI.le hAN))
  fin_cases i
  · exact Or.inl heq
  · exact Or.inr heq

private theorem symplectic_parabolic_cover
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S.field))
    (H : Subgroup (Coordinates.sp4 m).ModelGroup)
    (hPH : ((Coordinates.sp4 m).modelSylow : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    ∃ (i : Fin 2) (W : Submodule S.field.Carrier (Coordinates.sp4 m).Space),
      Module.finrank S.field.Carrier W = i.val + 1 ∧
      H ≤ (Coordinates.sp4 m).modelStabilizer W := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary)
  obtain ⟨g, hg⟩ := Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hq (Coordinates.sp4 m).modelSylow H hPH hH
  have lift (W : Submodule S.field.Carrier (Coordinates.sp4 m).Space)
      (hW : H.map (MulAut.conj g).toMonoidHom ≤
        Theory.SpecificGroups.SymplecticFour.stabilizer W) :
      H ≤ (Coordinates.sp4 m).modelStabilizer
        (W.map (Theory.SpecificGroups.SymplecticFour.toLinear g⁻¹).toLinearMap) := by
    rw [Sp4.modelStabilizer_eq, Sp4.stabilizer_map]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hW
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    simpa only [map_map, he, map_id] using hh
  rcases hg with hg | hg
  · refine ⟨0, (Theory.SpecificGroups.SymplecticFour.point S.field.Carrier).map
        (Theory.SpecificGroups.SymplecticFour.toLinear g⁻¹).toLinearMap, ?_, lift _ hg⟩
    exact ((Theory.SpecificGroups.SymplecticFour.toLinear g⁻¹).finrank_map_eq _).trans
      Theory.SpecificGroups.SymplecticFour.finrank_point
  · refine ⟨1, (Theory.SpecificGroups.SymplecticFour.plane S.field.Carrier).map
        (Theory.SpecificGroups.SymplecticFour.toLinear g⁻¹).toLinearMap, ?_, lift _ hg⟩
    exact ((Theory.SpecificGroups.SymplecticFour.toLinear g⁻¹).finrank_map_eq _).trans
      Theory.SpecificGroups.SymplecticFour.finrank_plane

/-- A proper full-Sylow local subgroup of the marked symplectic vertex is
one of its actual two flag residuals. -/
theorem symplectic_local_eq_flag_residual
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S.field))
    (f : InvariantFlag (Coordinates.sp4 m)) (hu : f.IsInnerUnique)
    (A : Subgroup G) (hA : A ∈ Chapter1.L G T) (hAI : A < I)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A = f.Li 0 ∨ A = f.Li 1 :=
  local_eq_one_of_flag_residuals D S f hu (symplectic_parabolic_cover D S m)
    A hA hAI hTA

omit D S in
private theorem g2_model_parabolic_cover
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (P : Sylow 2 (Atlas.G2.Model F)) (H : Subgroup (Atlas.G2.Model F))
    (hPH : (P : Subgroup _) ≤ H) (hH : H ≠ ⊤) :
    ∃ (i : Fin 2) (W : Submodule F (Atlas.G2.Natural.Space F)),
      Module.finrank F W = i.val + 1 ∧
      H ≤ G2.ResidualIncidence.stabilizer F W := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F)
    P (Atlas.G2.LieParabolicSetup.sylow (F := F))
  let a := MulAut.conj g
  have hP : (P : Subgroup (Atlas.G2.Model F)).map a.toMonoidHom =
      Atlas.G2.unipotent := by
    change ((g • P : Sylow 2 (Atlas.G2.Model F)) :
      Subgroup (Atlas.G2.Model F)) = _
    rw [hg]
    rfl
  have hn : H.map a.toMonoidHom ≠ ⊤ := by
    intro he
    apply hH
    exact map_injective a.injective
      (he.trans (map_top_of_surjective a.toMonoidHom a.surjective).symm)
  have hp := Atlas.G2.ProperSylowOvergroups.le_parabolic (H.map a.toMonoidHom)
    (hP ▸ map_mono hPH) (lt_top_iff_ne_top.mpr hn)
  have lift (W : Submodule F (Atlas.G2.Natural.Space F))
      (hW : H.map a.toMonoidHom ≤ G2.ResidualIncidence.stabilizer F W) :
      H ≤ (G2.ResidualIncidence.stabilizer F) (W.map ((Atlas.G2.Natural.action F) g⁻¹)) := by
    rw [G2.ResidualIncidence.stabilizer_map]
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hW
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp a.toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    simpa only [map_map, he, map_id] using hh
  rcases hp with hp | hp
  · refine ⟨1, (Atlas.G2.Natural.OrthogonalCover.naturalPlane F).map
        ((Atlas.G2.Natural.action F) g⁻¹), ?_, lift _ ?_⟩
    · exact (Atlas.G2.Natural.OrthogonalCover.SylowFlag.Transport.finrank_map
        (Atlas.G2.Natural.action F) g⁻¹ _).trans
        (Atlas.G2.Natural.OrthogonalCover.SylowFlag.naturalPlane_finrank F)
    · rwa [G2.ResidualIncidence.plane_stabilizer]
  · refine ⟨0, (Atlas.G2.Natural.OrthogonalCover.SylowFlag.N1 F).map
        ((Atlas.G2.Natural.action F) g⁻¹), ?_, lift _ ?_⟩
    · exact (Atlas.G2.Natural.OrthogonalCover.SylowFlag.Transport.finrank_map
        (Atlas.G2.Natural.action F) g⁻¹ _).trans
        (Atlas.G2.Natural.OrthogonalCover.SylowFlag.N1_finrank F)
    · rwa [G2.ResidualIncidence.point_stabilizer]

/-- A proper full-Sylow local subgroup of the marked G₂ vertex is one
of its original point and plane residuals. -/
theorem g2_local_eq_flag_residual
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S.field))
    (f : InvariantFlag (Coordinates.g2 m)) (hu : f.IsInnerUnique)
    (A : Subgroup G) (hA : A ∈ Chapter1.L G T) (hAI : A < I)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A = f.Li 0 ∨ A = f.Li 1 :=
  local_eq_one_of_flag_residuals D S f hu (g2_model_parabolic_cover (Coordinates.g2 m).modelSylow)
    A hA hAI hTA

/-- A flag residual belongs to the local family via its actual rank-one
quotient, obtained from the natural marking. -/
theorem flag_residual_mem_local {c : Coordinates D S.field} (f : InvariantFlag c)
    (i : Fin 2) : f.Li i ∈ Chapter1.L G T := by
  obtain ⟨f₀,hu,_,hq,_⟩ := exists_unique_marked_flag D S c
  have he : f.Li i = f₀.Li i := by
    change localResidual I (c.preimage (f.space i.castSucc)) = _
    rw [hu i.castSucc (f.space i.castSucc) (f.dimension i.castSucc) (f.invariant i.castSucc)]
    rfl
  have hq' : Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) := he.symm ▸ hq i
  exact Components.flag_mem_local_of_model D S f i
    ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq, hq'⟩

/-- A third local subgroup in the first point normalizer cannot lie in the
original component: rank-one covering would identify it with L₁. -/
theorem other_residual_not_le_original
    {c : Coordinates D S.field} (f : InvariantFlag c) {K K₀ : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0) :
    ¬ K₀ ≤ I := by
  intro hi
  let : Group.IsPerfect K₀ := Chapter1.mem_L_isPerfect hK₀
  exact hne (local_eq_flag_residual D S f 0 K₀ hK₀
    (le_map_solvableResidual_of_isPerfect K₀ (I ⊓ normalizer (f.Vi 0 : Set G))
      (le_inf hi (hK₀K.trans hK))))

omit D S in
private theorem local_le_of_normalizes_of_common_local
    {A B C : Subgroup G}
    (hA : A ∈ Chapter1.L G T) (hC : C ∈ Chapter1.L G T)
    (hCA : C ≤ A) (hCB : C ≤ B) (hAB : A ≤ normalizer (B : Set G)) : A ≤ B := by
  have ht : (⊤ : Subgroup A).IsCComponent := by
    simpa only [subgroupOf_self] using hA.1.subgroupOf_of_le le_rfl
      (show A ≤ A ⊔ (T : Subgroup G) from le_sup_left)
  let : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAB
  have hn : ¬ Group.IsSolvable (C.subgroupOf A) := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hC
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hCA).toMonoidHom)
        (subgroupOfEquivOfLe hCA).surjective)
  exact subgroupOf_eq_top.mp (top_unique
    (ht.le_normal_of_nonsolvable_subgroup hn le_top (comap_mono hCB)))

/-- Both original triangle vertices escape each other's normalizer. The
shared nonsolvable second residual and maximal-local membership suffice;
no generation identity for K or reselected component placement is assumed. -/
theorem triangle_vertices_escape
    {c : Coordinates D S.field} (f : InvariantFlag c) {K K₀ : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0)
    (hJ : (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T) :
    ¬ K₀ ⊔ f.Li 1 ≤ normalizer (I : Set G) ∧
    ¬ I ≤ normalizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) := by
  have hout := other_residual_not_le_original D S f hK hK₀ hK₀K hne
  have hC := flag_residual_mem_local D S f 1
  have hCI : f.Li 1 ≤ I := (localResidual_le _).trans inf_le_left
  constructor
  · intro hn
    exact hout (le_sup_left.trans
      (local_le_of_normalizes_of_common_local hJ hC le_sup_right hCI hn))
  · intro hn
    have hi := local_le_of_normalizes_of_common_local
      S.source.maximal_faithful.1.1 hC hCI le_sup_right hn
    have he := S.source.maximal_faithful.1.2 _ hJ hi
    exact hout (he ▸ (show K₀ ≤ K₀ ⊔ f.Li 1 from le_sup_left))

/-- In either orientation, a proper normalized local subgroup is an actual
flag residual; the linear-three row is excluded by the literal model order. -/
theorem triangle_local_eq_flag_residual
    {L : Subgroup G} (hd : S.field.degree = 2)
    (ho : Components.TriangleOrientation L I)
    {c : Coordinates D S.field} (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A : Subgroup G) (hA : A ∈ Chapter1.L G T) (hAI : A < I)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A = f.Li 0 ∨ A = f.Li 1 := by
  cases c with
  | sp4 m => exact symplectic_local_eq_flag_residual D S m f hu A hA hAI hTA
  | g2 m => exact g2_local_eq_flag_residual D S m f hu A hA hAI hTA
  | sl3 m =>
    have hc := Classification.orientation_order ho
    have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hF] at hc
    norm_num [Classification.FieldFourOrder] at hc

/-- Identifying K₀ with the new first residual forces L₂ to be the new
second residual, on the literal original groups in either orientation. -/
theorem reselected_second_eq
    {c : Coordinates D S.field} (f : InvariantFlag c) {K K₀ W : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0)
    (D_J : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) W)
    (S_J : D_J.NonbinaryNaturalInput)
    (hd : S_J.field.degree = 2) (ho : Components.TriangleOrientation I (K₀ ⊔ f.Li 1))
    {c_J : Coordinates D_J S_J.field} (f_J : InvariantFlag c_J)
    (hu : f_J.IsInnerUnique) (hfirst : f_J.Li 0 = K₀) : f_J.Li 1 = f.Li 1 := by
  have hout := other_residual_not_le_original D S f hK hK₀ hK₀K hne
  have hLI : f.Li 1 ≤ I := (localResidual_le _).trans inf_le_left
  have hlt : f.Li 1 < K₀ ⊔ f.Li 1 := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hout ((le_sup_left : K₀ ≤ K₀ ⊔ f.Li 1).trans (he.symm.le.trans hLI)))
  rcases triangle_local_eq_flag_residual D_J S_J hd ho f_J hu (f.Li 1)
    (flag_residual_mem_local D S f 1) hlt (f.sylow_normalizes_Li 1) with h | h
  · exact (hout (hfirst ▸ h.symm.le.trans hLI)).elim
  · exact h.symm

/-- Common second residuals preserve the exact original two-core of L₂T. -/
theorem reselected_second_radical_eq
    {c : Coordinates D S.field} (f : InvariantFlag c) {K K₀ W : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0)
    (D_J : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) W)
    (S_J : D_J.NonbinaryNaturalInput)
    (hd : S_J.field.degree = 2) (ho : Components.TriangleOrientation I (K₀ ⊔ f.Li 1))
    {c_J : Coordinates D_J S_J.field} (f_J : InvariantFlag c_J)
    (hu : f_J.IsInnerUnique) (hfirst : f_J.Li 0 = K₀) : f_J.Ri 1 = f.Ri 1 := by
  have he := reselected_second_eq D S f hK hK₀ hK₀K hne D_J S_J hd ho f_J hu hfirst
  change (f_J.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2 =
    (f.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2
  rw [he]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
