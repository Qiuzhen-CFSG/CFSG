module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOmegaImage

/-!
# The literal Chapter 11 center-pair actor

Let L = <Z_alpha,Z_gamma> and H = L Q_beta. Restrict the intrinsic
beta core quotient to H. Its kernel is exactly Q_beta, and its range is
the join of the full omega-centers of two distinct beta Sylow subgroups.
The quotient isomorphism H/Q_beta retains this very inclusion and quotient
map. This is the actor L/(L intersect Q_beta) on the two-seed section;
it is distinct from the source's larger quotient H/(Q_alpha intersect Q_gamma).

No alpha row is selected. In the unitary rows the resulting omega-pair
subgroup must still be identified with its linear block; it is not silently
replaced by the whole beta quotient. PairCoprimeSplitting applies the map
to the linear and nondegenerate Suzuki rows.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(b), (11.3), printed pp.168--171.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual inclusion induces the center-pair map, with exact kernel,
both omega-center images, and distinct Sylows. -/
theorem source_pair_actor_map
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let K := d.localGroup b
    ∃ hHK : H ≤ K, let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
      ∃ R T : Sylow 2 (K ⧸ pCore 2 K), R ≠ T ∧
        f.ker = (Q (family P) b).subgroupOf H ∧
        ((Z (family P) a).subgroupOf H).map f = omegaCenterIn (R : Subgroup _) ∧
        ((Z (family P) c).subgroupOf H).map f = omegaCenterIn (T : Subgroup _) ∧
        f.range = omegaCenterIn (R : Subgroup _) ⊔ omegaCenterIn (T : Subgroup _) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let K := d.localGroup b
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let : Finite K := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z (family P) a ≤ K := pGroup_le_localGroup (family P) d b _
    (IsElementaryAbelian.isPGroup 2 _) ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))
  have hZc : Z (family P) c ≤ K := pGroup_le_localGroup (family P) d b _
    (IsElementaryAbelian.isPGroup 2 _) ((((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U h c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right))
  have hQ : Q (family P) b ≤ K := by
    rw [←localGroup_core_eq (family P) d b]
    exact map_subtype_le _
  have hHK : H ≤ K := sup_le (sup_le hZa hZc) hQ
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := q.comp (inclusion hHK)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hab.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hbc
  let R' := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hRT : R' ≠ T' := by
    intro he
    have he' := congrArg (fun X : Sylow 2 (K ⧸ pCore 2 K) => (X : Subgroup _).comap q) he
    change ((R : Subgroup K).map q).comap q = ((T : Subgroup K).map q).comap q at he'
    rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk',
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at he'
    apply hac
    symm
    apply source_edge_sylow_unique_neighbor h d hab.symm hbc Mb R hR
    rw [he',hT]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hk : f.ker = (Q (family P) b).subgroupOf H := by
    ext x
    change q (inclusion hHK x) = 1 ↔ x.val ∈ Q (family P) b
    rw [show q (inclusion hHK x) = 1 ↔ inclusion hHK x ∈ pCore 2 K from
      QuotientGroup.eq_one_iff _,←localGroup_core_eq (family P) d b]
    exact ⟨fun hx => mem_map_of_mem K.subtype hx,fun ⟨y,hy,he⟩ =>
      (Subtype.ext he : y = inclusion hHK x) ▸ hy⟩
  have hm (A : Subgroup G) (hAH : A ≤ H) :
      (A.subgroupOf H).map f = (A.subgroupOf K).map q := by
    rw [show f = q.comp (inclusion hHK) from rfl,←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      change x.val ∈ A
      exact (congrArg Subtype.val he) ▸ (show y.val ∈ A from hy)
    · exact fun hx => ⟨⟨x.val,hAH hx⟩,hx,Subtype.ext rfl⟩
  obtain ⟨g,hg,hga⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  have hgb : g • b = b := d.local_le b hg
  have hcc : IsCriticalPair (family P) c b := by
    simpa only [hga,hgb] using criticalPair_translate (family P) hc g
  have ha : ((Z (family P) a).subgroupOf H).map f = omegaCenterIn (R' : Subgroup _) := by
    rw [hm _ (le_sup_left.trans le_sup_left)]
    exact source_rankOne_center_image_omega h hB d hc hb Mb R hR
  have hc' : ((Z (family P) c).subgroupOf H).map f = omegaCenterIn (T' : Subgroup _) := by
    rw [hm _ (le_sup_right.trans le_sup_left)]
    exact source_rankOne_center_image_omega h hB d hcc hb Mb T hT
  refine ⟨hHK,R',T',hRT,hk,ha,hc',?_⟩
  have ht : (((Z (family P) a).subgroupOf H) ⊔ (Z (family P) c).subgroupOf H) ⊔
      (Q (family P) b).subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup (show Z (family P) a ≤ H from le_sup_left.trans le_sup_left)
      (show Z (family P) c ≤ H from le_sup_right.trans le_sup_left),
      ←subgroupOf_sup (show Z (family P) a ⊔ Z (family P) c ≤ H from le_sup_left) le_sup_right]
    exact subgroupOf_self H
  have hh := congrArg (map f) ht
  have hzero : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [Subgroup.map_sup,Subgroup.map_sup,←hk,hzero,sup_bot_eq,ha,hc',←MonoidHom.range_eq_map] at hh
  exact hh.symm

/-- The literal actor quotient is the join of two omega-centers in the beta
local quotient, with the original quotient map retained. -/
theorem source_pair_actor_equiv
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    [hN : ((Q (family P) b).subgroupOf
      ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).Normal] :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let K := d.localGroup b
    ∃ R T : Sylow 2 (K ⧸ pCore 2 K), R ≠ T ∧
      ∃ hHK : H ≤ K,
        ∃ e : (H ⧸ (Q (family P) b).subgroupOf H) ≃*
            (omegaCenterIn (R : Subgroup (K ⧸ pCore 2 K)) ⊔ omegaCenterIn (T : Subgroup (K ⧸ pCore 2 K)) : Subgroup (K ⧸ pCore 2 K)),
          ∀ x : H, (e (QuotientGroup.mk' ((Q (family P) b).subgroupOf H) x) : K ⧸ pCore 2 K) =
            QuotientGroup.mk' (pCore 2 K) (inclusion hHK x) := by
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let K := d.localGroup b
  obtain ⟨hHK,R,T,hRT,hk,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
  let W := omegaCenterIn (R : Subgroup (K ⧸ pCore 2 K)) ⊔ omegaCenterIn (T : Subgroup (K ⧸ pCore 2 K))
  let eR : (H ⧸ (Q (family P) b).subgroupOf H) ≃* f.range :=
    QuotientGroup.liftEquiv _ f.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hk.symm)
  let e := eR.trans (MulEquiv.subgroupCongr hr)
  have he (x : H) : (e (QuotientGroup.mk' ((Q (family P) b).subgroupOf H) x) : K ⧸ pCore 2 K) = f x := rfl
  exact ⟨R,T,hRT,hHK,e,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
