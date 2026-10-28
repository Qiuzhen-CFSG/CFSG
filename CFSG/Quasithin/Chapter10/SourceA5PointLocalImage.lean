module
public import CFSG.Quasithin.Chapter10.SourceA5PointSmallImage
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# The literal local A5 section in the point action

Restrict the full point-centralizer Sylow to the normal containing component
and map that very Sylow through its solvable action kernel. The smaller image
is a proper local C-component with A5 quotient by its two-core. The quotient
actor, subgroup inclusions and Sylow maps are retained for the marked model
inspection in Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The actual full point Sylow restricts to the containing component,
retaining the original local-component condition and original intersection. -/
theorem source_a5_point_component_local_sylow
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    ∃ R : Sylow 2 I, (R : Subgroup I) = (T : Subgroup G).subgroupOf I ∧
      L.subgroupOf I ∈ localCComponents R := by
  have hSI := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs hIX hI.subnormal
  have he : ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I = (T : Subgroup G) ⊓ I := by
    rw [inf_assoc,inf_eq_right.mpr hIX]
  rw [he] at hSI
  obtain ⟨R,hR⟩ := hSI
  have hR' : (R : Subgroup I) = (T : Subgroup G).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hR,subgroupOf_map_subtype]
  exact ⟨R,hR',hR'.symm ▸ SourceEmbeddings.local_restrict D.maximal.1.1 hLI⟩

/-- The local smaller image is proper, retains its A5 two-core quotient,
and is local at the image of the literal full Sylow in the point component. -/
theorem source_a5_point_small_image_local_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
    letI := hr.normal
    let K := I.subgroupOf H
    let q := actionMk U
    let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
    B < ⊤ ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
    ∃ R : Sylow 2 K,
      (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K ∧
      B ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
  let := hr.normal
  let K := I.subgroupOf H
  let A := L.subgroupOf H
  let q := actionMk U
  let B := (A.map q).subgroupOf (K.map q)
  let f := q.subgroupMap K
  have hAK : A ≤ K := comap_mono hLI
  have hab : A.map q ≤ K.map q := map_mono hAK
  have hmark := (source_a5_point_action_marking D I hLI hout hCW hspan hr).2.2.2
  have hBproper : B < ⊤ := lt_top_iff_ne_top.mpr (fun he => by
    have hh := congrArg (Subgroup.map (K.map q).subtype) he
    rw [map_subgroupOf_eq_of_le hab,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hmark.ne hh)
  obtain ⟨_,⟨eA⟩⟩ := source_a5_point_small_image_twoCore D e I hLI hout hCW hspan hr
  let b : B ≃* A.map q := subgroupOfEquivOfLe hab
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eA
  refine ⟨hBproper,⟨eB⟩,?_⟩
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le hIX inf_le_right
  obtain ⟨P,hP⟩ := hs.restrict le_sup_right hHX
  have hP' : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hAlocal : A ∈ localCComponents P := by
    rw [hP']
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) (hLI.trans le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans hNI))
  obtain ⟨R,hR,hAR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hAlocal hAK
    (inferInstance : K.Normal).isSubnormal
  have hR' : (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K := by
    rw [hR,hP']
    ext x
    exact and_iff_left (hIX x.property)
  let : Group.IsSolvable f.ker := source_a5_point_component_action_kernel_solvable D
    I hLI hIX hI hout hCW hspan hr
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hAR f
  have himage : (A.subgroupOf K).map f = B := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map.mpr ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      exact ⟨⟨a,hAK ha⟩,ha,Subtype.ext hax⟩
  refine ⟨R,hR',?_⟩
  simpa only [himage,Sylow.coe_mapSurjective] using hlocal
end CFSG.Quasithin.Chapter10
