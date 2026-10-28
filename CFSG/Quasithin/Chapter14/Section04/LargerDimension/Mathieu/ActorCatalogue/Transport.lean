module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.MapInjectivity
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PCoreImage

/-!
# Residual actors through the actual two-core projection

A two-perfect subgroup normalized by the projection kernel is recovered as
the two-residual of the full preimage of its image. Hence a surjection with
two-group kernel contained in T induces a bijection of the literal X-families.
The inverse is the residual preimage. Restricting the same map to a subgroup
identifies its intrinsic two-core quotient with that of its image.

The source applications retain H as a relative subgroup of the ambient group,
use an actual Sylow subgroup of H, and use the literal H/O₂(H) projection.
They identify the published first and Borel actors with these residual lifts.
The order-32 lemma uses relative normality, without assuming the centralizer
normal in the ambient group. The native Mathieu classification is not asserted
by these transport results.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012, and the
quotient convention in 14.4, printed p.1006 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

omit [Finite A] in
private theorem residual_eq_iff (X : Subgroup A) :
    twoResidual X = X ↔ IsPPerfect 2 X := by
  have hh := (map_injective X.subtype_injective).eq_iff (a := pResidual 2 X) (b := ⊤)
  simpa only [twoResidual, ← MonoidHom.range_eq_map, range_subtype] using
    hh.trans (pResidual_eq_top_iff 2 X)

omit [Finite A] in
private theorem core_index (X : Subgroup A) :
    (twoCore X).relIndex X = Nat.card (coreQuotient X) := by
  have hh := relIndex_map_map_of_injective (pCore 2 X) ⊤ X.subtype_injective
  simpa only [twoCore, ← MonoidHom.range_eq_map, range_subtype, relIndex_top_right,
    index_eq_card] using hh

/-- The residual of a full preimage, used to recover the source actors. -/
def residualLift (q : A →* B) (P : Subgroup B) : Subgroup A := twoResidual (P.comap q)

omit [Finite A] [Finite B] in
/-- Restriction of the actual projection retains a two-group kernel. -/
theorem restricted_kernel_two (q : A →* B) (hk : IsPGroup 2 q.ker) (J : Subgroup A) :
    IsPGroup 2 (q.subgroupMap J).ker := by
  rw [Subgroup.ker_subgroupMap]
  exact hk.comap_subtype

/-- Both intrinsic two-cores are removed by the actual restricted projection. -/
noncomputable def coreImageEquiv (q : A →* B) (hk : IsPGroup 2 q.ker)
    (J : Subgroup A) : coreQuotient J ≃* coreQuotient (J.map q) :=
  MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap J) (q.subgroupMap_surjective J)
    (restricted_kernel_two q hk J)

theorem coreImageEquiv_mk (q : A →* B) (hk : IsPGroup 2 q.ker)
    (J : Subgroup A) (x : J) :
    coreImageEquiv q hk J (QuotientGroup.mk' (pCore 2 J) x) =
      QuotientGroup.mk' (pCore 2 (J.map q)) (q.subgroupMap J x) :=
  MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ x

/-- The literal family conditions descend through a two-group kernel. -/
theorem threeExtension_map (q : A →* B) (hk : IsPGroup 2 q.ker)
    {H T X : Subgroup A} (hX : ThreeExtension H T X) :
    ThreeExtension (H.map q) (T.map q) (X.map q) := by
  refine ⟨map_mono hX.le_H, (map_mono hX.T_normalizes).trans (le_normalizer_map q), ?_, ?_⟩
  · have hh := congrArg (map q) hX.residual_eq
    rw [twoResidual, map_embedded_pResidual] at hh
    exact hh
  · rw [core_index, ← Nat.card_congr (coreImageEquiv q hk X).toEquiv, ← core_index]
    exact hX.index_three

omit [Finite B] in
theorem residualLift_map (q : A →* B) (hq : Function.Surjective q) (P : Subgroup B) :
    (residualLift q P).map q = twoResidual P := by
  change ((pResidual 2 (P.comap q)).map (P.comap q).subtype).map q = _
  rw [map_embedded_pResidual, map_comap_eq_self_of_surjective hq]
  rfl

omit [Finite A] [Finite B] in
/-- A source actor is recovered from its image because the kernel lies in T,
which normalizes that actor. Ambient normality of X is not needed. -/
theorem residualLift_image (q : A →* B) (hk : IsPGroup 2 q.ker)
    {H T X : Subgroup A} (hkT : q.ker ≤ T) (hX : ThreeExtension H T X) :
    residualLift q (X.map q) = X := by
  rw [residualLift, comap_map_eq]
  exact embedded_pResidual_sup_kernel q X ((residual_eq_iff X).mp hX.residual_eq)
    hk (hkT.trans hX.T_normalizes)

/-- A T-invariant quotient actor lifts canonically, with all four source
conditions proved. The kernel is allowed to be noncentral. -/
theorem residualLift_threeExtension (q : A →* B) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (P : Subgroup B)
    (hP : ThreeExtension ⊤ (T.map q) P) :
    ThreeExtension ⊤ T (residualLift q P) := by
  have hn : T ≤ normalizer (P.comap q : Set A) :=
    (map_le_iff_le_comap.mp hP.T_normalizes).trans (le_normalizer_comap q)
  refine ⟨le_top, hn.trans (normalizer_le_normalizer_characteristic_image
    (P.comap q) (pResidual 2 (P.comap q))),
    (residual_eq_iff _).mpr (isPPerfect_embedded_pResidual 2 (P.comap q)), ?_⟩
  rw [core_index, Nat.card_congr (coreImageEquiv q hk (residualLift q P)).toEquiv,
    residualLift_map q hq, hP.residual_eq, ← core_index]
  exact hP.index_three

/-- Projection gives an actual bijection of source actor families. This does
not classify the family in B; the native Mathieu calculation remains needed. -/
theorem XFamily_transport (q : A →* B) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (T : Subgroup A) (hkT : q.ker ≤ T) :
    XFamily ⊤ T = residualLift q '' XFamily ⊤ (T.map q) := by
  ext X
  constructor
  · intro hX
    have hm := threeExtension_map q hk hX
    rw [map_top_of_surjective q hq] at hm
    exact ⟨X.map q, hm, residualLift_image q hk hkT hX⟩
  · rintro ⟨P, hP, rfl⟩
    exact residualLift_threeExtension q hq hk T P hP

omit [Finite B] in
/-- Distinct quotient actors have distinct residual lifts. -/
theorem residualLift_ne (q : A →* B) (hq : Function.Surjective q)
    {P R : Subgroup B} (hP : twoResidual P = P) (hR : twoResidual R = R)
    (hne : P ≠ R) : residualLift q P ≠ residualLift q R := by
  intro he
  have hh := congrArg (map q) he
  rw [residualLift_map q hq, residualLift_map q hq, hP, hR] at hh
  exact hne hh

/-- Restriction to H preserves the source's relative normality convention. -/
theorem threeExtension_subgroupOf {H T X : Subgroup A} (hX : ThreeExtension H T X) :
    ThreeExtension ⊤ (T.subgroupOf H) (X.subgroupOf H) := by
  refine ⟨le_top, ?_, ?_, ?_⟩
  · apply le_normalizer_iff.mpr
    intro t ht x hx
    exact (le_normalizer_iff.mp hX.T_normalizes) t ht x hx
  · apply map_injective H.subtype_injective
    rw [twoResidual, map_embedded_pResidual, map_subgroupOf_eq_of_le hX.le_H]
    exact hX.residual_eq
  · have hi := relIndex_map_map_of_injective (twoCore (X.subgroupOf H))
      (X.subgroupOf H) H.subtype_injective
    have hc : (twoCore (X.subgroupOf H)).map H.subtype = twoCore X := by
      change ((X.subgroupOf H).pCoreIn 2).map H.subtype = X.pCoreIn 2
      rw [map_pCoreIn_of_ker_isPGroup H.subtype
        ((MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective ▸ IsPGroup.of_bot),
        map_subgroupOf_eq_of_le hX.le_H]
    rw [hc, map_subgroupOf_eq_of_le hX.le_H] at hi
    exact hi.symm.trans hX.index_three

/-- The actual H/O₂(H) map followed by an honest carrier isomorphism. -/
def starProjection (H : Subgroup A) (e : coreQuotient H ≃* B) : H →* B :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))

omit [Finite A] [Finite B] in
theorem starProjection_surjective (H : Subgroup A) (e : coreQuotient H ≃* B) :
    Function.Surjective (starProjection H e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite A] [Finite B] in
theorem starProjection_ker (H : Subgroup A) (e : coreQuotient H ≃* B) :
    (starProjection H e).ker = pCore 2 H := by
  rw [starProjection, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

omit [Finite B] in
/-- The first lifted actor is precisely the already published O²(O₂,₃(H)),
including its original ambient embedding. -/
theorem firstActor_eq_residualLift (H : Subgroup A) (e : coreQuotient H ≃* B) :
    firstActor H = (residualLift (starProjection H e) (pCore 3 B)).map H.subtype := by
  have he : (pCore 3 B).comap e.toMonoidHom = pCore 3 (coreQuotient H) := by
    rw [← pCore_map_iso 3 e, comap_map_eq_self_of_injective e.injective]
  have hc : (pCore 3 B).comap (starProjection H e) =
      (pCore 3 (coreQuotient H)).comap (QuotientGroup.mk' (pCore 2 H)) := by
    rw [starProjection, ← comap_comap, he]
  rw [residualLift, twoResidual, map_embedded_pResidual, hc]
  rfl

omit [Finite B] in
/-- The Borel preimage uses the same residual and embedding as the source. -/
theorem borelActor_eq_residualLift (H : Subgroup A) (q : H →* B) (P : Subgroup B) :
    borelActor ((P.comap q).map H.subtype) = (residualLift q P).map H.subtype := by
  rw [residualLift, twoResidual, map_embedded_pResidual]
  rfl

/-- The first sentence of 14.4.12: normality and order 32 identify Wg* with
the actual centralizer's two-core once its native order has been proved. -/
theorem eq_twoCore_of_normal_order32 (C W : Subgroup A)
    (hWC : W ≤ C) (hn : C ≤ normalizer (W : Set A))
    (hW : IsPGroup 2 W) (hcard : Nat.card W = 32)
    (hcore : Nat.card (pCore 2 C) = 32) : W = twoCore C := by
  apply eq_of_le_of_card_ge (le_pCoreIn_of_normalizes hW hWC hn)
  change Nat.card ((pCore 2 C).map C.subtype) ≤ Nat.card W
  rw [card_map_of_injective C.subtype_injective, hcard, hcore]

/-- Application of the family bijection to the literal quotient of H and the
actual Sylow T. It preserves the original ambient carrier of every actor. -/
theorem source_XFamily_transport (H : Subgroup A) (S : Sylow 2 H)
    (e : coreQuotient H ≃* B) :
    XFamily H ((S : Subgroup H).map H.subtype) =
      (fun P => (residualLift (starProjection H e) P).map H.subtype) ''
        XFamily ⊤ ((S : Subgroup H).map (starProjection H e)) := by
  let q := starProjection H e
  have hk : IsPGroup 2 q.ker := by
    rw [starProjection_ker]
    exact pCore_isPGroup
  have hs : q.ker ≤ S := hk.le_sylow_of_normal S
  have hsubker : IsPGroup 2 H.subtype.ker := by
    rw [(MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective]
    exact IsPGroup.of_bot
  ext X
  constructor
  · intro hX
    have hi := threeExtension_subgroupOf hX
    have hS : ((S : Subgroup H).map H.subtype).subgroupOf H = (S : Subgroup H) :=
      comap_map_eq_self_of_injective H.subtype_injective _
    rw [hS] at hi
    have hf := XFamily_transport q (starProjection_surjective H e) hk S hs
    have hi' : X.subgroupOf H ∈ XFamily ⊤ S := hi
    rw [hf] at hi'
    obtain ⟨P, hP, he⟩ := hi'
    refine ⟨P, hP, ?_⟩
    exact (congrArg (map H.subtype) he).trans (map_subgroupOf_eq_of_le hX.le_H)
  · rintro ⟨P, hP, rfl⟩
    have hi := residualLift_threeExtension q (starProjection_surjective H e) hk S P hP
    have hm := threeExtension_map H.subtype hsubker hi
    rw [← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm

/-- The map on an ambient subgroup's core quotient induced by the actual
H/O₂(H) projection. In the source application J is X₁ ⊔ X₂ ⊔ T. -/
noncomputable def sourceCoreImageEquiv (H J : Subgroup A) (hJH : J ≤ H)
    (e : coreQuotient H ≃* B) :
    coreQuotient J ≃* coreQuotient ((J.subgroupOf H).map (starProjection H e)) := by
  let j := (subgroupOfEquivOfLe hJH).symm
  exact (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans
    (coreImageEquiv (starProjection H e)
      (by rw [starProjection_ker]; exact pCore_isPGroup) (J.subgroupOf H))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
