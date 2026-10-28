module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Omega
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses

/-!
# The full core quotient and moved section of a short group

For a short K and a two-subgroup R normalizing K, apply the omega-center
calculation inside the literal join KR. Its star kernel is O₂(KR), and
K/O₂(K) maps isomorphically onto K*. The displayed isomorphism uses the
original star projection, rather than a chosen abstract identification.

The final theorem transports a marked action on the actual star moved/fixed
section to a `BlockModuleModel` on K, retaining the conjugation equation.
This is the block-specific bridge used in the C.4.1 classification.
Source: Aschbacher--Smith C.1.7--11 and C.2.7, pp.123--124,145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.BlockOmega
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}

/-- Restrict a short subgroup to its radical supplement. -/
theorem block_in_join (hs : IsShort K) (hn : R ≤ normalizer (K : Set G)) :
    IsBlock (K.subgroupOf (K ⊔ R)) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  exact ⟨inferInstance,hs.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm,
    (inferInstance : (K.subgroupOf (K ⊔ R)).Normal).isSubnormal⟩

/-- The omega-center star kernel in the literal join is exactly its two-core. -/
theorem starKernel_eq_core (hs : IsShort K) (hp : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) :
    starKernel K R = pCore 2 (K ⊔ R : Subgroup G) := by
  let J := K ⊔ R
  let B := K.subgroupOf J
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hgen : B ⊔ R.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,← MonoidHom.range_eq_map,range_subtype]
  exact omega_centralizer (block_in_join hs hn)
    (isPGroup_quotient_of_sup_eq_top B (R.subgroupOf J) hp.comap_subtype hgen)

/-- The map from the original short subgroup loses precisely its two-core. -/
theorem toStarImage_ker_eq_core (hs : IsShort K) (hp : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) :
    (toStarImage K R).ker = pCore 2 K := by
  let f : K →* (K ⊔ R : Subgroup G) := inclusion le_sup_left
  have hk : (toStarImage K R).ker = (pCore 2 (K ⊔ R : Subgroup G)).comap f := by
    ext k
    change toStarImage K R k = 1 ↔ f k ∈ pCore 2 (K ⊔ R : Subgroup G)
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (starKernel K R) (f k) = 1 ↔ _
    exact (QuotientGroup.eq_one_iff (f k)).trans
      (by rw [starKernel_eq_core hs hp hn])
  apply le_antisymm _ (core_le_toStarImage_ker hn)
  rw [hk]
  exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective f (inclusion_injective _)⟩

/-- The full two-core quotient, with its original star projection. -/
@[expose] noncomputable def coreStarEquiv (hs : IsShort K) (hp : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) :
    (K ⧸ pCore 2 K) ≃* starImage K R K :=
  MulEquiv.ofBijective (coreToStar hn)
    ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr (toStarImage_ker_eq_core hs hp hn).symm,
      coreToStar_surjective hn⟩

/-- The quotient isomorphism commutes with the original projection. -/
@[simp] theorem coreStarEquiv_mk (hs : IsShort K) (hp : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) (k : K) :
    coreStarEquiv hs hp hn (QuotientGroup.mk' (pCore 2 K) k) =
      toStarImage K R k := rfl

open FullSieve.SourceInterface ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender
open scoped IsMulCommutative

/-- The star moved subgroup is the intrinsic layer in the join carrier. -/
theorem star_moved_eq (hs : IsShort K) (hn : R ≤ normalizer (K : Set G)) :
    ⁅starV K R, K.subgroupOf (K ⊔ R)⁆ =
      (blockU (K.subgroupOf (K ⊔ R))).map (K.subgroupOf (K ⊔ R)).subtype :=
  omega_commutator (block_in_join hs hn)

variable [(K.subgroupOf (K ⊔ R)).Normal]
local instance starImage_normal : (starImage K R K).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- A model of the actual star moved section gives the intrinsic block model. -/
theorem model_of_star_moving {A V : Type*} [Group A] [AddCommGroup V]
    [Module (ZMod 2) V] (hs : IsShort K) (hp : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) (σ : Representation (ZMod 2) A V)
    (E : ActionEquiv
      ((MovedSection.ofNormal (starRepresentation K R) (starImage K R K)).action.comp
        (starImage K R K).subtype) σ) : IsLinearBlockModel K σ := by
  let B := K.subgroupOf (K ⊔ R)
  let e : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let eq : (B ⧸ pCore 2 B) ≃* starImage K R K :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (coreStarEquiv hs hp hn)
  have hm := BlockMovingSection.model_of_moving (starV K R) B
    (QuotientGroup.mk' (starKernel K R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (star_moved_eq hs hn).symm eq (fun _ => rfl) σ E
  exact hm.of_mulEquiv e

end CFSG.Quasithin.ChapterC.BlockOmega
