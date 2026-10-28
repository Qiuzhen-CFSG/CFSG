module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceImages
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveGeometry

/-!
# Source image geometry without whole-radical movement

The original secondary subgroup is included in the component and then mapped
onto its full two-core quotient. The kernel is a two-group, so its PSL₂ model
survives both projection and inner conjugation. The enlarged-core bound supplies
a kernel Sylow subgroup; Frattini lifts the radical normalizer. Every action
image uses the same normalQuotientAction as SourceImages.image.

These are the literal geometry inputs for the corrected sieve, with component
placement, the rank-one model, and the source enlarged-core bound explicit.
No legacy SecondaryData witness or radical movement is used.
Source: Aschbacher–Smith, original 4.3.12–16, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve.SourceImages
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (c : SourceConfiguration T L) (C : Subgroup (rootNormalizer c)) [C.Normal]
variable (hK : secondary c ≤ C.map (rootNormalizer c).subtype)

/-- The actual secondary inclusion, retaining both subtype maps. -/
def secondaryToComponent : secondary c →* C where
  toFun x := ⟨⟨x,(hK.trans (map_subtype_le _)) x.property⟩,by
    obtain ⟨a,ha,he⟩ := hK x.property
    exact (Subtype.ext he : a = ⟨x,_⟩) ▸ ha⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] [C.Normal] in
/-- The inclusion has no kernel before quotienting. -/
theorem secondaryToComponent_injective : Function.Injective (secondaryToComponent c C hK) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : C => ((z : rootNormalizer c) : G)) he)

/-- Projection to the full component quotient, without quotienting its center. -/
def secondaryProjection : secondary c →* (C ⧸ pCore 2 C) :=
  (QuotientGroup.mk' (pCore 2 C)).comp (secondaryToComponent c C hK)

omit [Finite G] in
/-- The specified action on the original secondary group is inner projection. -/
theorem action_secondary (x : secondary c) :
    normalQuotientAction C (pCore 2 C) ⟨x,(hK.trans (map_subtype_le _)) x.property⟩ =
      MulAut.conj (secondaryProjection c C hK x) :=
  normalQuotientAction_inner C (pCore 2 C) (secondaryToComponent c C hK x)

omit [Finite G] in
/-- The actual secondary image agrees with the inner image of its full projection. -/
theorem secondary_action_image : image c C (secondary c) =
    (secondaryProjection c C hK).range.map MulAut.conj := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨secondaryProjection c C hK ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,
      (action_secondary c C hK ⟨x,hx⟩).symm⟩
  · rintro ⟨q,⟨x,rfl⟩,rfl⟩
    exact ⟨⟨x,(hK.trans (map_subtype_le _)) x.property⟩,x.property,
      action_secondary c C hK x⟩

omit [C.Normal] in
/-- Perfectness survives the literal secondary projection. -/
theorem secondaryProjection_perfect : Group.IsPerfect (secondaryProjection c C hK).range := by
  let := EndgameSieve.secondary_perfect c
  exact Group.IsPerfect.range _

omit [Finite G] [C.Normal] in
/-- The projection kernel embeds in the component two-core. -/
theorem secondaryProjection_kernel_two : IsPGroup 2 (secondaryProjection c C hK).ker := by
  let f : (secondaryProjection c C hK).ker →* pCore 2 C :=
    ((secondaryToComponent c C hK).comp (secondaryProjection c C hK).ker.subtype).codRestrict _
      (fun x => (QuotientGroup.eq_one_iff (secondaryToComponent c C hK x.val)).mp x.property)
  apply (pCore_isPGroup (p := 2) (G := C)).of_injective f
  intro x y he
  apply Subtype.ext
  exact secondaryToComponent_injective c C hK (congrArg Subtype.val he)

/-- The secondary two-core quotient survives projection to the full quotient. -/
def secondaryProjectionCoreEquiv : secondary c ⧸ pCore 2 (secondary c) ≃*
    (secondaryProjection c C hK).range ⧸ pCore 2 (secondaryProjection c C hK).range :=
  (secondaryProjection c C hK).rangeRestrict.pCoreQuotientEquiv
    (secondaryProjection c C hK).rangeRestrict_surjective (by
      rw [MonoidHom.ker_rangeRestrict]
      exact secondaryProjection_kernel_two c C hK)

omit [C.Normal] in
/-- The source rank-one model on the literal projected secondary subgroup. -/
theorem secondaryProjection_model {n : ℕ}
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)) :
    ClassicalGroup.IsPSL ((secondaryProjection c C hK).range ⧸
      pCore 2 (secondaryProjection c C hK).range) 2 (2 ^ n) :=
  hm.of_mulEquiv (secondaryProjectionCoreEquiv c C hK).symm

omit [C.Normal] in
/-- The projected secondary quotient is centerless, even at the smallest field. -/
theorem secondaryProjection_center_eq_bot {n : ℕ}
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)) :
    center ((secondaryProjection c C hK).range ⧸
      pCore 2 (secondaryProjection c C hK).range) = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := secondaryProjection_model c C hK hm
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hx' : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hx'
  exact e.injective (hx'.trans (map_one e).symm)

include hK in
/-- The model also survives the possible central inner-action kernel. -/
theorem secondaryImage_model {n : ℕ}
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)) :
    ClassicalGroup.IsPSL (image c C (secondary c) ⧸ pCore 2 (image c C (secondary c)))
      2 (2 ^ n) := by
  rw [secondary_action_image c C hK]
  exact (secondaryProjection_model c C hK hm).of_mulEquiv
    (innerImageCoreEquiv _ (secondaryProjection_center_eq_bot c C hK hm)).symm

include hK in
/-- In particular the actual secondary action is nontrivial. -/
theorem secondaryImage_ne_bot {n : ℕ}
    (hm : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)) :
    image c C (secondary c) ≠ ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := secondaryImage_model c C hK hm
  let : Nontrivial (image c C (secondary c) ⧸ pCore 2 (image c C (secondary c))) :=
    e.surjective.nontrivial
  let : Nontrivial (image c C (secondary c)) :=
    (QuotientGroup.mk'_surjective (pCore 2 (image c C (secondary c)))).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

omit [Finite G] in
/-- Centrality of the projected two-core implies centrality of the original
secondary-core image under the same quotient action. -/
theorem coreImageCentral_of_projection_core_le_center
    (hc : pCore 2 (secondaryProjection c C hK).range ≤ center (secondaryProjection c C hK).range) :
    image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _) := by
  let f := secondaryProjection c C hK
  have hcore : (pCore 2 (secondary c)).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 (secondary c)).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  intro a ha
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨u,hu,heu⟩ := hx
  have hxa : x = ⟨u,(hK.trans (map_subtype_le _)) u.property⟩ := Subtype.ext heu.symm
  rw [hxa,action_secondary]
  rintro b ⟨y,hy,rfl⟩
  have hya : y = ⟨(⟨y,hy⟩ : secondary c),(hK.trans (map_subtype_le _)) hy⟩ := rfl
  rw [hya,action_secondary]
  have huC := hc (hcore (mem_map_of_mem f.rangeRestrict hu))
  have he := congrArg (fun z : f.range => (z : C ⧸ pCore 2 C))
    (mem_center_iff.mp huC (f.rangeRestrict ⟨y,hy⟩))
  change f ⟨y,hy⟩ * f u = f u * f ⟨y,hy⟩ at he
  simpa only [← map_mul] using congrArg (MulAut.conj : (C ⧸ pCore 2 C) →* MulAut _) he

/-- The source enlarged-core bound supplies a Sylow subgroup of the actual
quotient-action kernel inside the original radical. -/
theorem action_kernel_sylow_le (hperf : Group.IsPerfect C)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hbound : (C.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c) :
    ∃ P : Sylow 2 (normalQuotientAction C (pCore 2 C)).ker,
      (P : Subgroup _).map (normalQuotientAction C (pCore 2 C)).ker.subtype ≤
        (R₂ c).subgroupOf (rootNormalizer c) := by
  let := hperf
  let T' : Sylow 2 (rootNormalizer c) := T.subtype (root_normalized c D)
  obtain ⟨P,hP⟩ := ChapterA.Section04.sylow_normalQuotientAction_ker C T'
  refine ⟨P,?_⟩
  rw [hP]
  apply (map_le_iff_le_comap).mp
  rw [map_pCoreIn_of_injective 2 _ _ (rootNormalizer c).subtype_injective,
    Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le (root_normalized c D)]
  exact hbound

/-- Frattini lifts the image normalizer using the actual kernel Sylow.
The statement applies to the entire root-normalizer image. -/
theorem image_normalizer_control (hperf : Group.IsPerfect C)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hbound : (C.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hR : R₂ c ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G)) :
    (normalQuotientAction C (pCore 2 C)).range ⊓ normalizer (image c C (R₂ c) : Set _) ≤
      normalizer (image c C (secondary c) : Set _) := by
  obtain ⟨P,hP⟩ := action_kernel_sylow_le c C hperf D hbound
  have hlift := normalizer_image_of_kernel_sylow_le
    ((R₂ c).subgroupOf (rootNormalizer c))
    (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype
    (normalQuotientAction C (pCore 2 C)) P hP
  apply hlift.trans
  apply le_trans (map_mono ?_)
    (((secondary c).subgroupOf (rootNormalizer c)).le_normalizer_map _)
  intro x hx
  have hr : ((R₂ c).subgroupOf (rootNormalizer c)).map (rootNormalizer c).subtype = R₂ c :=
    map_subgroupOf_eq_of_le hR
  have hx' : (x : G) ∈ normalizer (R₂ c : Set G) := by
    rw [← hr]
    exact ((R₂ c).subgroupOf (rootNormalizer c)).le_normalizer_map
      (rootNormalizer c).subtype (mem_map_of_mem _ hx)
  apply mem_normalizer_iff.mpr
  intro y
  exact mem_normalizer_iff.mp (hN hx').2 (y : G)

/-- Quasisimplicity makes the actual two-local image normalizer proper. -/
theorem inner_not_le_radical_normalizer [IsQuasisimple (C ⧸ pCore 2 C)]
    (hrad : image c C (R₂ c) ≠ ⊥) :
    ¬ MulAut.innerSubgroup (C ⧸ pCore 2 C) ≤ normalizer (image c C (R₂ c) : Set _) :=
  inner_not_le_normalizer_twoGroup _
    (((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype).map _) hrad

omit [Finite G] in
/-- The full inner group lies in the image of this same quotient action. -/
theorem inner_le_action_range : MulAut.innerSubgroup (C ⧸ pCore 2 C) ≤
    (normalQuotientAction C (pCore 2 C)).range := by
  rintro a ⟨q,rfl⟩
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) q
  exact ⟨x,normalQuotientAction_inner C (pCore 2 C) x⟩

include hK in
/-- All three source local-image clauses on the literal G₀-star. The enlarged
core, original radical normalizer, rank-one model and nontrivial action suffice;
no movement of the radical by the torus is required. -/
theorem local_image_geometry [IsQuasisimple (C ⧸ pCore 2 C)] {n : ℕ}
    (hperf : Group.IsPerfect C) (D : Chapter12.Section02.ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n))
    (Y : Subgroup G)
    (hbound : (C.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hR : R₂ c ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hrad : image c C (R₂ c) ≠ ⊥) :
    ClassicalGroup.IsPSL (image c C (secondary c) ⧸ pCore 2 (image c C (secondary c))) 2 (2 ^ n) ∧
      (MulAut.innerSubgroup (C ⧸ pCore 2 C) ⊔ image c C (R₂ c) ⊔ image c C Y) ⊓
        normalizer (image c C (R₂ c) : Set _) ≤ normalizer (image c C (secondary c) : Set _) ∧
      ¬ MulAut.innerSubgroup (C ⧸ pCore 2 C) ≤ normalizer (image c C (R₂ c) : Set _) := by
  refine ⟨secondaryImage_model c C hK hmodel,?_,inner_not_le_radical_normalizer c C hrad⟩
  apply (inf_le_inf_right _ ?_).trans (image_normalizer_control c C hperf D hbound hR hN)
  exact sup_le (sup_le (inner_le_action_range c C) (map_le_range _ _)) (map_le_range _ _)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve.SourceImages
