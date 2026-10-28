module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Cubic
public import Theory.GroupTheory.PResidual.SylowIndexThree

/-!
# Residual actors of native index-three Sylow overgroups

Every overgroup of the prescribed Sylow subgroup with relative index three
has a two-residual in the literal X-family. Its intrinsic residual quotient
has order three by the three-coset action calculation. Characteristicity
supplies normalization, and residual idempotence supplies two-perfectness.
Adjoining the Sylow subgroup recovers the original overgroup.

For the actual Borel in 14.4.12, containment in the binary point centralizer
then proves that its residual fixes the point and differs from the cubic
actor. These deductions use exactly the supplied Borel containments and
relative index; no centralizer classification or desired quotient is assumed.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012. The
construction of the remaining native overgroup and exhaustion of all actors
remain separate obligations.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics

theorem residual_threeExtension_of_index_three (S : Sylow 2 Model)
    (P : Subgroup Model) (hSP : (S : Subgroup Model) ≤ P)
    (hi : (S : Subgroup Model).relIndex P = 3) :
    ThreeExtension ⊤ (S : Subgroup Model) (twoResidual P) := by
  refine ⟨le_top, hSP.trans (le_normalizer_embedded_pResidual 2 P), ?_, ?_⟩
  · change (pResidual 2 (twoResidual P)).map (twoResidual P).subtype = twoResidual P
    rw [(pResidual_eq_top_iff 2 (twoResidual P)).mpr (isPPerfect_embedded_pResidual 2 P),
      ← MonoidHom.range_eq_map, range_subtype]
  · change (((pCore 2 (twoResidual P)).map (twoResidual P).subtype).comap
      (twoResidual P).subtype).index = 3
    rw [comap_map_eq_self_of_injective (twoResidual P).subtype_injective, index_eq_card]
    let e : pResidual 2 P ≃* twoResidual P :=
      (pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective
    let eQ : (pResidual 2 P ⧸ pCore 2 (pResidual 2 P)) ≃*
        (twoResidual P ⧸ pCore 2 (twoResidual P)) :=
      QuotientGroup.congr (pCore 2 (pResidual 2 P)) (pCore 2 (twoResidual P))
        e (pCore_map_iso 2 e)
    rw [← Nat.card_congr eQ.toEquiv]
    exact residual_core_quotient_card_of_sylow_index_three (S.subtype hSP) hi

theorem residual_sup_sylow (S : Sylow 2 Model)
    (P : Subgroup Model) (hSP : (S : Subgroup Model) ≤ P) :
    twoResidual P ⊔ (S : Subgroup Model) = P := by
  have h := congrArg (Subgroup.map P.subtype)
    (pResidual_sup_sylow_eq_top (S.subtype hSP))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
  change twoResidual P ⊔ ((S : Subgroup Model).subgroupOf P).map P.subtype = P at h
  rwa [map_subgroupOf_eq_of_le hSP] at h

theorem borelResidual_calculation (S : Sylow 2 Model) {v : Space}
    (hv : v ≠ 0) (B : Subgroup Model)
    (hSB : (S : Subgroup Model) ≤ B) (hB : B ≤ pointCentralizer v)
    (hi : (S : Subgroup Model).relIndex B = 3) :
    ThreeExtension ⊤ (S : Subgroup Model) (twoResidual B) ∧
      twoResidual B ≤ pointCentralizer v ∧
      twoResidual (pCore 3 Model) ≠ twoResidual B ∧
      twoResidual B ⊔ (S : Subgroup Model) = B :=
  ⟨residual_threeExtension_of_index_three S B hSB hi,
    borelResidual_le_pointCentralizer B hB,
    firstActor_ne_borelResidual B hv hB, residual_sup_sylow S B hSB⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
