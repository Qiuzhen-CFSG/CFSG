module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PlaneThompson
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.CompletionSylow
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Theory.GroupTheory.AbelianWeakClosureFusion
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
/-!
# Plane-radical fusion in a faithful U4(2) completion

The marked overlap Sylow maps exactly to a Sylow of the ambient group by
F.4.33. Its elementary Thompson subgroup is the image of the actual plane
radical, as shown by the Hermitian action calculation. Injective transport
therefore makes this radical weakly closed, and Burnside fusion gives a
normalizer conjugator for every ambient conjugacy between its elements.
Under source normalizer condition (a), that conjugator is the image of an
actual element of the second endpoint.

The final wrapper uses precisely the image of Z(O2(G2)) for the full concrete
plane parabolic. The binary equality of that parabolic with L2 identifies it
with the radical used in the calculation. All maps remain those of the given
faithful completion and its ambient embedding.

Source: Aschbacher--Smith F.4.35, printed p.292, plain U4(2) branch.
This proves fusion on the plane radical; complete involution placement,
short-centralizer recognition and the graph-extension case are separate.
-/

@[expose] public section
noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PlainFusion
open GreenBook.LieModels.UnitaryFour
local notation "L" => L2 1 (Nat.le_refl 1)
local notation "Q" => pCore 2 L
local notation "B" => overlap 1 (Nat.le_refl 1)

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (amalgam 1 (Nat.le_refl 1)) (G := G0))
    (i : G0 →* G)

def planeEmbedding : L →* G :=
  (i.comp c.right).comp (inclusion (L2_le_planeParabolic 1 (Nat.le_refl 1)))

theorem planeEmbedding_injective (hi : Function.Injective i) :
    Function.Injective (planeEmbedding c i) :=
  (hi.comp c.right_injective).comp (inclusion_injective _)

def planeImage : Subgroup G := (pCore 2 L).map (planeEmbedding c i)

theorem sylow_le_local : (projectiveSylow 1 (Nat.le_refl 1) : Subgroup _) ≤ L :=
  two_subgroup_le_L2 1 (Nat.le_refl 1) _ (projectiveSylow 1 (Nat.le_refl 1)).isPGroup'
    (projectiveSylow_le_parabolics 1 (Nat.le_refl 1)).2

def localSylow : Sylow 2 L :=
  (projectiveSylow 1 (Nat.le_refl 1)).subtype sylow_le_local

theorem middle_sylow_image :
    ((projectiveSylow 1 (Nat.le_refl 1)).subtype
        (upperProjective_le_overlap 1 (Nat.le_refl 1)) : Subgroup _).map (i.comp c.middle) =
      (localSylow : Subgroup L).map (planeEmbedding c i) := by
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    refine ⟨⟨a.val, sylow_le_local ha⟩, ha, ?_⟩
    change i (c.right ((amalgam 1 (Nat.le_refl 1)).right a)) = i (c.middle a)
    exact congrArg i (DFunLike.congr_fun c.compatible a).symm
  · rintro x ⟨a, ha, rfl⟩
    let b : B := ⟨a, upperProjective_le_overlap 1 (Nat.le_refl 1) ha⟩
    refine ⟨b, ha, ?_⟩
    exact congrArg i (DFunLike.congr_fun c.compatible b)

variable [Finite G]

theorem completion_thompson
    (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (localSylow : Subgroup L).map (planeEmbedding c i) ∧
      elementaryAbelianMaxJ (S : Subgroup G) = planeImage c i := by
  obtain ⟨S, hS⟩ := source_plain_sylow c i hi z hz hzroot hc
  rw [middle_sylow_image c i] at hS
  refine ⟨S, hS, ?_⟩
  rw [hS, elementaryAbelianMaxJ_map_injective _ (planeEmbedding_injective c i hi),
    PlaneThompson.plane_thompson]
  rfl

theorem completion_plane_fusion
    (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    {x y : G} (hx : x ∈ planeImage c i) (hy : y ∈ planeImage c i) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (planeImage c i : Set G), MulAut.conj n x = y := by
  obtain ⟨S, hS, hJ⟩ := completion_thompson c i hi z hz hzroot hc
  let : IsElementaryAbelian 2 (planeImage c i) := IsElementaryAbelian.map (planeEmbedding c i)
  have hVS : planeImage c i ≤ (S : Subgroup G) := by
    rw [← hJ]
    exact sSup_le fun A hA => hA.1
  apply S.normalizer_fuses_of_abelian_weakly_closed (planeImage c i) hVS _ hx hy hxy
  intro g hg
  change (planeImage c i).map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) at hg
  have he := elementaryAbelianMaxJ_map_eq_of_le (S : Subgroup G) (MulAut.conj g)
    (by rwa [hJ])
  change (planeImage c i).map (MulAut.conj g).toMonoidHom = planeImage c i
  simpa only [hJ] using he

theorem source_plain_plane_fusion
    (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hn : normalizer (planeImage c i : Set G) = (i.comp c.right).range)
    {x y : G} (hx : x ∈ planeImage c i) (hy : y ∈ planeImage c i) (hxy : IsConj x y) :
    ∃ a : planeParabolic 1 (Nat.le_refl 1),
      i (c.right a) * x * (i (c.right a))⁻¹ = y := by
  obtain ⟨n, hn', he⟩ := completion_plane_fusion c i hi z hz hzroot hc hx hy hxy
  obtain ⟨a, rfl⟩ := hn ▸ hn'
  exact ⟨a, he⟩

def sourcePlaneRootImage : Subgroup G :=
  (center (pCore 2 (planeParabolic 1 (Nat.le_refl 1)))).map
    ((i.comp c.right).comp (pCore 2 (planeParabolic 1 (Nat.le_refl 1))).subtype)

omit [Finite G] in
theorem sourcePlaneRootImage_eq : sourcePlaneRootImage c i = planeImage c i := by
  let e : L ≃* planeParabolic 1 (Nat.le_refl 1) :=
    MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local.symm
  have he : e.toMonoidHom = inclusion (L2_le_planeParabolic 1 (Nat.le_refl 1)) := by
    ext x
    rfl
  have hp : (pCore 2 L).map (inclusion (L2_le_planeParabolic 1 (Nat.le_refl 1))) =
      pCore 2 (planeParabolic 1 (Nat.le_refl 1)) := by
    rw [← he, pCore_map_iso]
  let hEA : IsElementaryAbelian 2 (pCore 2 (planeParabolic 1 (Nat.le_refl 1))) :=
    hp ▸ IsElementaryAbelian.map (inclusion (L2_le_planeParabolic 1 (Nat.le_refl 1)))
  have hz : center (pCore 2 (planeParabolic 1 (Nat.le_refl 1))) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact mem_center_iff.mpr fun y => hEA.toIsMulCommutative.is_comm.comm y x
  rw [sourcePlaneRootImage, hz, ← map_map, ← MonoidHom.range_eq_map, range_subtype, ← hp, map_map]
  rfl

theorem source_plain_plane_fusion_of_normalizer_condition
    (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hn : normalizer (sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    {x y : G} (hx : x ∈ sourcePlaneRootImage c i)
    (hy : y ∈ sourcePlaneRootImage c i) (hxy : IsConj x y) :
    ∃ a : planeParabolic 1 (Nat.le_refl 1),
      i (c.right a) * x * (i (c.right a))⁻¹ = y := by
  rw [sourcePlaneRootImage_eq] at hn hx hy
  exact source_plain_plane_fusion c i hi z hz hzroot hc hn hx hy hxy


theorem source_plain_plane_fusion_iff
    (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hn : normalizer (sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    {x y : G} (hx : x ∈ sourcePlaneRootImage c i)
    (hy : y ∈ sourcePlaneRootImage c i) :
    IsConj x y ↔ ∃ a : planeParabolic 1 (Nat.le_refl 1),
      i (c.right a) * x * (i (c.right a))⁻¹ = y := by
  constructor
  · exact source_plain_plane_fusion_of_normalizer_condition c i hi z hz hzroot hc hn hx hy
  · rintro ⟨a, ha⟩
    exact isConj_iff.mpr ⟨i (c.right a), ha⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo.PlainFusion
