module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.BorelLift
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.SolvableNormalSup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction

/-!
# The actual Sylow marking and lifted Borel in 13.8.20

The Sylow of H maps to H/O₂(H) and restricts to the normal component K*.
Its embedded image is T*∩K*, also the image of T∩K because O₂(H)≤T.
The intrinsic Sylow normalizer defines B₀*, and its preimage is taken inside
K. Residual transport identifies B* with the embedded intrinsic residual.
Solvability lifts through the genuine two-group kernel. The universal
13.8.13 input then gives B≤M when the source normalization is available.
The restriction of 13.7.3(9) uses the actual order-three closure.

These are construction and transport lemmas, not a proof of the local
Borel identities: higher-field normalization and intrinsic solvability
remain premises of `borel_le_M_of_normalizes`.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971;
13.7.3(9), printed p.936; 13.8.13, printed p.950.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
variable {G : Type*} [Group G] [Finite G]

/-- Restrict the actual quotient Sylow to the normal component image. -/
theorem exists_sourceSylow (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) :
    ∃ S : Sylow 2 (Source.starImage H K),
      (S : Subgroup (Source.starImage H K)) = (Source.starImage H T).subgroupOf _ := by
  obtain ⟨P, hP⟩ := hT
  have hPH : T.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let P' := P.mapSurjective (f := QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)
  have hPS : (P' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    rw [Source.starImage, hPH]
    rfl
  obtain ⟨S, hS⟩ := P'.exists_subgroupOf_eq_of_normal (Source.starImage H K)
  exact ⟨S, hS.trans (congrArg (fun U => U.subgroupOf (Source.starImage H K)) hPS)⟩

noncomputable def sourceSylow (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) : Sylow 2 (Source.starImage H K) :=
  (exists_sourceSylow H K T hT).choose

theorem sourceSylow_eq (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) :
    (sourceSylow H K T hT : Subgroup (Source.starImage H K)) =
      (Source.starImage H T).subgroupOf _ :=
  (exists_sourceSylow H K T hT).choose_spec

theorem sourceSylow_image (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) :
    (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype = Source.starImage H T ⊓ Source.starImage H K := by
  rw [sourceSylow_eq, subgroupOf_map_subtype]

omit [Finite G] in
theorem star_intersection (H K T : Subgroup G) (hT : Chapter1.IsSylowIn 2 T H) :
    Source.starImage H (T ⊓ K) = Source.starImage H T ⊓ Source.starImage H K := by
  obtain ⟨P, hP⟩ := hT
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk', ← hP, ← comap_subtype,
      comap_map_eq_self_of_injective H.subtype_injective]
    exact pCore_isPGroup.le_sylow_of_normal P
  have he : (T ⊓ K).subgroupOf H = K.subgroupOf H ⊓ T.subgroupOf H := by
    ext x
    exact and_comm
  rw [Source.starImage, he, map_inf_of_ker_le _ _ _ hk]
  exact inf_comm _ _

/-- The Borel is the Sylow normalizer inside K*, embedded in H*. -/
noncomputable def borelStar (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) : Subgroup (Source.Hstar H) :=
  (normalizer (sourceSylow H K T hT : Set (Source.starImage H K))).map
    (Source.starImage H K).subtype

noncomputable def borel₀ (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) : Subgroup G :=
  borelLift H K hKH (borelStar H K T hT)

noncomputable def borel (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) : Subgroup G :=
  borelResidual (borel₀ H K T hKH hT)

theorem borel_le_component (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) : borel H K T hKH hT ≤ K :=
  (map_subtype_le _).trans (borelLift_le H K hKH _)

theorem borel₀_star (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) :
    Source.starImage H (borel₀ H K T hKH hT) = borelStar H K T hT :=
  starImage_borelLift H K hKH _ (map_subtype_le _)

theorem borel_star (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) :
    Source.starImage H (borel H K T hKH hT) =
      residualIn 2 (borelStar H K T hT) :=
  starImage_borelResidual H K hKH _ (map_subtype_le _)

omit [Finite G] in
/-- Restricting 13.7.3(9) uses the literal order-three closure. -/
theorem theta_restrict (H M L₁ J : Subgroup G)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hLJ : L₁ ≤ J) (hJ : J ≤ H ⊓ M) :
    L₁ = closure {x : G | x ∈ J ∧ orderOf x = 3} := by
  apply le_antisymm
  · rw [htheta]
    apply (closure_le _).mpr
    intro x hx
    have hxL : x ∈ L₁ := htheta.symm ▸ subset_closure hx
    exact subset_closure ⟨hLJ hxL, hx.2⟩
  · rw [htheta]
    exact closure_mono fun x hx => ⟨hJ hx.1, hx.2⟩

/-- The intrinsic residual used by the torus model is exactly the embedded star image. -/
theorem borel_star_intrinsic (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H) :
    Source.starImage H (borel H K T hKH hT) =
      (borelResidual (normalizer (sourceSylow H K T hT : Set (Source.starImage H K)))).map
        (Source.starImage H K).subtype := by
  rw [borel_star]
  exact (map_embedded_pResidual 2 _ _).symm

/-- Solvability of the intrinsic Borel lifts across the actual two-group kernel. -/
theorem borel₀_solvable (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hs : Group.IsSolvable (normalizer
      (sourceSylow H K T hT : Set (Source.starImage H K)))) :
    Group.IsSolvable (borel₀ H K T hKH hT) := by
  let := hs
  let e : normalizer (sourceSylow H K T hT : Set (Source.starImage H K)) ≃*
      borelStar H K T hT :=
    equivMapOfInjective _ (Source.starImage H K).subtype (Source.starImage H K).subtype_injective
  let : Group.IsSolvable (borelStar H K T hT) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let f : borel₀ H K T hKH hT →* borelStar H K T hT :=
    TorusModels.borelStarProjection H K hKH (borelStar H K T hT) (map_subtype_le _)
  have hk : IsPGroup 2 f.ker := TorusModels.borelStarProjection_ker_isTwoGroup H K hKH _ _
  let := hk.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

/-- The universal earlier 13.8.13 statement applies to B(L₁T), once the
intrinsic Borel's solvability and its source normalization have been proved. -/
theorem borel_le_M_of_normalizes (H K T L₁ G₁ M : Subgroup G)
    [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (hs : Group.IsSolvable (normalizer
      (sourceSylow H K T hT : Set (Source.starImage H K))))
    (hbase : Group.IsSolvable (L₁ ⊔ T : Subgroup G))
    (hn : L₁ ⊔ T ≤ normalizer (borel H K T hKH hT : Set G)) :
    borel H K T hKH hT ≤ M := by
  let := borel₀_solvable H K T hKH hT hs
  have hb : Group.IsSolvable (borel H K T hKH hT) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show borel H K T hKH hT ≤ borel₀ H K T hKH hT from map_subtype_le _))
      (inclusion_injective _)
  exact Components.Suzuki.borel_le_of_solvable_exclusion L₁ T G₁ M _ hex hb hbase hn
    ((borel_le_component H K T hKH hT).trans (hKH.trans hH.2.1)) (hH.1.2.trans hH.2.1)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel

end
