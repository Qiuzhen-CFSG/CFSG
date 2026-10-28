module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.MapInjectivity
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SolvableResidual

/-!
# The literal tensor subgroups and their quotient transport

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 14.4.10,
printed pp.1010–1011. We define X₁, X₂ and K₀ using the actual residuals,
cores and Sylow normalizer, with all subgroups embedded in the original G.

The kernel O₂(H) normalizes every member of X when it lies in T. Taking
the two-residual of the full preimage therefore recovers the member from
its image. Separately, a two-group kernel preserves intrinsic two-core
quotients. These two transports let concrete model calculations identify
the whole source family and its whole overlap quotient.

This module does not prove the tensor chief-factor or commutator calculations,
and does not exclude the A₅-module branch. They remain source obligations.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G]
/-- The literal image of an ambient subgroup in H/O₂(H). Containment in H is
required by the transport theorems below. -/
def star (H X : Subgroup G) : Subgroup (coreQuotient H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
/-- The full preimage of O₃(H/O₂(H)), embedded in the original ambient group. -/
def twoThreeCore (H : Subgroup G) : Subgroup G :=
  ((pCore 3 (coreQuotient H)).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype
/-- The first subgroup X₁ := O²(O₂,₃(H)) in 14.4.10. -/
def first (H : Subgroup G) : Subgroup G := twoResidual (twoThreeCore H)
/-- The embedded solvable residual K₀ := H∞. Its component properties require
the source hypotheses; they are not part of this definition. -/
def component (H : Subgroup G) : Subgroup G := (solvableResidual H).map H.subtype
/-- The actual normalizer N_{K₀}(T ∩ K₀) used for the source Borel. -/
def borel (H T : Subgroup G) : Subgroup G :=
  ChapterF.Source.borel (component H) T
/-- The second subgroup X₂ := O²(B) in 14.4.10. -/
def second (H T : Subgroup G) : Subgroup G := twoResidual (borel H T)

/-- An embedded two-residual equality means intrinsic two-perfectness. -/
theorem isPPerfect_of_residual_eq {X : Subgroup G} (h : twoResidual X = X) :
    IsPPerfect 2 X := by
  apply (pResidual_eq_top_iff 2 X).mp
  apply (map_injective X.subtype_injective)
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact h

/-- The quotient detects members of X because O₂(H) lies in T and therefore
normalizes both subgroups. Ambient normality of the members is not assumed. -/
theorem eq_of_star_eq {H T X Y : Subgroup G}
    (hcore : twoCore H ≤ T) (hX : X ∈ XFamily H T) (hY : Y ∈ XFamily H T)
    (he : star H X = star H Y) : X = Y := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn (A : Subgroup G) (hA : A ∈ XFamily H T) :
      q.ker ≤ normalizer (A.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hA.le_H]
    intro x hx
    apply hA.T_normalizes
    apply hcore
    exact mem_map.mpr ⟨x, by simpa only [q, QuotientGroup.ker_mk'] using hx, rfl⟩
  have hp (A : Subgroup G) (hA : A ∈ XFamily H T) : IsPPerfect 2 (A.subgroupOf H) :=
    (isPPerfect_of_residual_eq hA.residual_eq).of_surjective
      (subgroupOfEquivOfLe hA.le_H).symm.toMonoidHom
      (subgroupOfEquivOfLe hA.le_H).symm.surjective
  have hh := eq_of_map_eq_map_of_isPPerfect q (hp X hX) (hp Y hY) hq
    (hn X hX) (hn Y hY) he
  have hm := congrArg (fun A : Subgroup H => A.map H.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hX.le_H, map_subgroupOf_eq_of_le hY.le_H] using hm

/-- An exhaustive pair of image calculations gives equality of the actual
source family, with both residual subgroups recovered upstairs. -/
theorem family_eq_pair_of_star {H T X₁ X₂ : Subgroup G}
    (hcore : twoCore H ≤ T) (h₁ : X₁ ∈ XFamily H T) (h₂ : X₂ ∈ XFamily H T)
    (hex : ∀ X ∈ XFamily H T, star H X = star H X₁ ∨ star H X = star H X₂) :
    XFamily H T = {X₁, X₂} := by
  ext X
  constructor
  · intro hX
    rcases hex X hX with he | he
    · exact Set.mem_insert_iff.mpr (Or.inl (eq_of_star_eq hcore hX h₁ he))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (eq_of_star_eq hcore hX h₂ he))
  · intro hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact h₁
    · have he := Set.mem_singleton_iff.mp hX
      simpa only [he] using h₂

theorem first_le (H : Subgroup G) : first H ≤ H :=
  (map_subtype_le _).trans (map_subtype_le _)

theorem second_le (H T : Subgroup G) : second H T ≤ H :=
  ((map_subtype_le _).trans inf_le_left).trans (map_subtype_le _)

/-- The whole subgroup X₁X₂T appearing in clause (5). -/
def overlap (H T : Subgroup G) : Subgroup G := first H ⊔ second H T ⊔ T

theorem overlap_le {H T : Subgroup G} (hT : T ≤ H) : overlap H T ≤ H :=
  sup_le (sup_le (first_le H) (second_le H T)) hT

/-- X₁ is normal relative to H, using the normal preimage defining O₂,₃(H). -/
theorem first_normal (H : Subgroup G) : ((first H).subgroupOf H).Normal := by
  have he : (twoThreeCore H).subgroupOf H =
      (pCore 3 (coreQuotient H)).comap (QuotientGroup.mk' (pCore 2 H)) := by
    unfold twoThreeCore
    rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  have hn : ((twoThreeCore H).subgroupOf H).Normal := he ▸ inferInstance
  exact normal_embedded_pResidual_subgroupOf 2 (map_subtype_le _) hn

theorem first_T_normalized {H T : Subgroup G} (hT : T ≤ H) :
    T ≤ normalizer (first H : Set G) := by
  have := first_normal H
  exact hT.trans (le_normalizer_of_normal_subgroupOf (first_le H))

/-- Normalization of H∞ and T ∩ H∞ proves invariance of the actual Borel. -/
theorem borel_T_normalized {H T : Subgroup G} (hT : T ≤ H) :
    T ≤ normalizer (borel H T : Set G) := by
  have hK : T ≤ normalizer (component H : Set G) :=
    hT.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (solvableResidual H)))
  have hS : T ≤ normalizer (T ⊓ component H : Set G) :=
    (le_inf T.le_normalizer hK).trans inf_normalizer_le_normalizer_inf
  exact (le_inf hK (hS.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

theorem second_T_normalized {H T : Subgroup G} (hT : T ≤ H) :
    T ≤ normalizer (second H T : Set G) :=
  (borel_T_normalized hT).trans
    (normalizer_le_normalizer_characteristic_image (borel H T) (pResidual 2 (borel H T)))

variable [Finite G]
theorem twoResidual_idempotent (X : Subgroup G) :
    twoResidual (twoResidual X) = twoResidual X := by
  unfold twoResidual
  rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 X),
    ← MonoidHom.range_eq_map, range_subtype]

theorem twoResidual_subgroupOf {H X : Subgroup G} (hX : X ≤ H) :
    (twoResidual X).subgroupOf H = twoResidual (X.subgroupOf H) := by
  apply map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le (show twoResidual X ≤ H from (map_subtype_le _).trans hX)]
  change twoResidual X = ((pResidual 2 (X.subgroupOf H)).map
    (X.subgroupOf H).subtype).map H.subtype
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hX]
  rfl

theorem star_twoResidual {H X : Subgroup G} (hX : X ≤ H) :
    star H (twoResidual X) = twoResidual (star H X) := by
  rw [star, twoResidual_subgroupOf hX]
  exact map_embedded_pResidual 2 _ _

omit [Finite G] in
theorem star_twoThreeCore (H : Subgroup G) :
    star H (twoThreeCore H) = pCore 3 (coreQuotient H) := by
  unfold star twoThreeCore
  rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- The image of the literal first source subgroup is the whole three-core
of H/O₂(H), since a three-group equals its two-residual. -/
theorem star_first (H : Subgroup G) :
    star H (first H) = pCore 3 (coreQuotient H) := by
  rw [first, star_twoResidual (show twoThreeCore H ≤ H from map_subtype_le _), star_twoThreeCore]
  have hp : pResidual 2 (pCore 3 (coreQuotient H)) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact (pCore_isPGroup (p := 3) (G := coreQuotient H)).orderOf_coprime
      (by decide : Nat.Coprime 3 2) x |>.symm
  unfold twoResidual
  rw [hp, ← MonoidHom.range_eq_map, range_subtype]

/-- The homomorphism to the literal image, retaining the ambient quotient map. -/
def starHom {H J : Subgroup G} (hJ : J ≤ H) : J →* star H J :=
  ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (J.subgroupOf H)).comp
    (subgroupOfEquivOfLe hJ).symm.toMonoidHom

/-- Quotienting a contained subgroup by its intrinsic two-core commutes with
passing to its image in H/O₂(H). No containment of O₂(H) in that subgroup is assumed. -/
noncomputable def starCoreQuotientEquiv {H J : Subgroup G} (hJ : J ≤ H) :
    coreQuotient J ≃* (star H J ⧸ pCore 2 (star H J)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.subgroupMap (J.subgroupOf H)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap (J.subgroupOf H)).ker
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact hq.comap_subtype
  let e := subgroupOfEquivOfLe hJ
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    (f.pCoreQuotientEquiv (q.subgroupMap_surjective _) hk)

/-- The quotient equivalence commutes with the literal quotient homomorphisms. -/
theorem starCoreQuotientEquiv_mk {H J : Subgroup G} (hJ : J ≤ H) (x : J) :
    starCoreQuotientEquiv hJ (QuotientGroup.mk' (pCore 2 J) x) =
      QuotientGroup.mk' (pCore 2 (star H J)) (starHom hJ x) := rfl


omit [Finite G] in
theorem coreQuotient_card_eq_index (X : Subgroup G) :
    Nat.card (coreQuotient X) = (twoCore X).relIndex X := by
  change Nat.card (X ⧸ pCore 2 X) =
    (((pCore 2 X).map X.subtype).comap X.subtype).index
  rw [comap_map_eq_self_of_injective X.subtype_injective, index_eq_card]

/-- A source family member still has quotient order three in H/O₂(H). -/
theorem star_quotient_card_three {H T X : Subgroup G} (hX : X ∈ XFamily H T) :
    Nat.card (star H X ⧸ pCore 2 (star H X)) = 3 := by
  rw [← Nat.card_congr (starCoreQuotientEquiv hX.le_H).toEquiv,
    coreQuotient_card_eq_index]
  exact hX.index_three


/-- First source member, from the order of the actual quotient's three-core. -/
theorem first_mem_X_of_threeCore_card {H T : Subgroup G}
    (hT : T ≤ H) (hcard : Nat.card (pCore 3 (coreQuotient H)) = 3) :
    first H ∈ XFamily H T := by
  refine ⟨first_le H, first_T_normalized hT, twoResidual_idempotent _, ?_⟩
  have hs : Nat.card (star H (first H)) = 3 := by rw [star_first]; exact hcard
  have hc : pCore 2 (star H (first H)) = ⊥ := by
    rcases (pCore_isPGroup (p := 2) (G := star H (first H))).card_eq_or_dvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · have hd := dvd_trans h (pCore 2 (star H (first H))).card_subgroup_dvd_card
      rw [hs] at hd
      norm_num at hd
  rw [← coreQuotient_card_eq_index,
    Nat.card_congr (starCoreQuotientEquiv (first_le H)).toEquiv, hc,
    Nat.card_congr (QuotientGroup.quotientBot (G := star H (first H))).toEquiv, hs]


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
