module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.ComponentAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The full covered residual inside a concrete parabolic

Restrict the actual source Sylow subgroup to the normal component in H*,
then transport L₀* and that Sylow intersection through the given K* ≃ SL₃(2).
The intrinsic recognition theorem identifies the full L₀* with the embedded
two-residual of its normalizer. A single conjugation marks the parabolic,
its residual and its Sylow subgroup at a standard point or line parabolic.

The comparison keeps the possible surviving two-core of L₀*. The intrinsic
cubic quotient supplies an order hypothesis, not a replacement subgroup.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
covered paragraph of 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G]

private theorem star_normalizes (H A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine ⟨a * b * a⁻¹, le_normalizer_iff.mp hAB a.val ha b.val hb, ?_⟩
  simp only [map_mul, map_inv]

/-- The full source residual, its parabolic and its source Sylow intersection
are transported by one concrete inner automorphism of SL₃(2). -/
structure ParabolicPlacement (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) where
  sylow : Sylow 2 (Source.starImage H K)
  sylow_eq : (sylow : Subgroup (Source.starImage H K)) =
    (Source.starImage H T).subgroupOf (Source.starImage H K)
  parabolic : Subgroup (Source.starImage H K)
  normalizer_eq : parabolic = normalizer
    ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K) : Set (Source.starImage H K))
  contains_sylow : (sylow : Subgroup (Source.starImage H K)) ≤ parabolic
  maximal : IsCoatom parabolic
  card : Nat.card parabolic = 24
  residual_eq : (Source.starImage H (zero L)).subgroupOf (Source.starImage H K) = residual parabolic
  residual_ambient : Source.starImage H (zero L) = (residual parabolic).map (Source.starImage H K).subtype
  conjugator : Matrix.PSL3Two.SL
  standard : Subgroup Matrix.PSL3Two.SL
  standard_eq : standard = Matrix.PSL3Two.pointParabolicSL ∨ standard = Matrix.PSL3Two.lineParabolicSL
  parabolic_mark : (parabolic.map eK.toMonoidHom).map (MulAut.conj conjugator).toMonoidHom = standard
  residual_mark : (((Source.starImage H (zero L)).subgroupOf (Source.starImage H K)).map
    eK.toMonoidHom).map (MulAut.conj conjugator).toMonoidHom = residual standard
  sylow_mark : ((sylow : Subgroup (Source.starImage H K)).map eK.toMonoidHom).map
    (MulAut.conj conjugator).toMonoidHom = Matrix.PSL3Two.borelSL
  borel_le : Matrix.PSL3Two.borelSL ≤ standard

variable [Finite G]

theorem exists_zero_parabolic (H K L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    [(K.subgroupOf H).Normal] (hKH : K ≤ H) (hTH : T ≤ H)
    (hzero : zero L ≤ K)
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group) :
    Nonempty (ParabolicPlacement H K L T eK) := by
  let Ks := Source.starImage H K
  let Zs := Source.starImage H (zero L)
  let Z := Zs.subgroupOf Ks
  let A := Z.map eK.toMonoidHom
  let P := normalizer (Z : Set Ks)
  have hZK : Zs ≤ Ks := star_le_of_le H hzero
  have hZH : zero L ≤ H := hzero.trans hKH
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTH]
  let Ss := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hSs : (Ss : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    change (S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = _
    rw [hS']
    rfl
  obtain ⟨SK, hSK⟩ := Ss.exists_subgroupOf_eq_of_normal Ks
  rw [hSs] at hSK
  have hTZ : Source.starImage H T ≤ normalizer (Zs : Set (Source.Hstar H)) :=
    star_normalizes H T (zero L) (d.normalizes_L.trans (normalizer_le_zero_normalizer L))
  have hSKP : (SK : Subgroup Ks) ≤ P := by
    rw [hSK]
    change (Source.starImage H T).subgroupOf Ks ≤ normalizer (Zs.subgroupOf Ks : Set Ks)
    rw [← subgroupOf_normalizer_eq hZK]
    exact subgroupOf_mono Ks hTZ
  let SM := SK.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hSMA : (SM : Subgroup Matrix.PSL3Two.SL) ≤ normalizer (A : Set Matrix.PSL3Two.SL) :=
    (map_mono hSKP).trans (le_normalizer_map eK.toMonoidHom)
  let eA : Zs ≃* A := (subgroupOfEquivOfLe hZK).symm.trans (eK.subgroupMap Z)
  have hp : IsPPerfect 2 A :=
    ((residual_isPPerfect (centralPreimage L)).of_surjective (starMap H (zero L) hZH)
      (starMap_surjective H (zero L) hZH)).of_surjective eA.toMonoidHom eA.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    let eq := (starCoreQuotientEquiv H (zero L) hZH).trans
      (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA))
    exact (Nat.card_congr eq.toEquiv).symm.trans d.zero_core_card
  obtain ⟨hmax, hcard, _, hres, g, P₀, hP₀, hP, hA, hSM, hB⟩ :=
    Matrix.PSL3Two.ResidualRecognition.recognize A SM hp hc hSMA
  have hPN : P.map eK.toMonoidHom = normalizer (A : Set Matrix.PSL3Two.SL) :=
    map_normalizer_eq_of_bijective Z eK.bijective
  have hr : Z = residual P := by
    apply map_injective (f := eK.toMonoidHom) eK.injective
    calc
      Z.map eK.toMonoidHom = A := rfl
      _ = residual (normalizer (A : Set Matrix.PSL3Two.SL)) := hres
      _ = (residual P).map eK.toMonoidHom := by
        rw [← hPN]
        exact (map_embedded_pResidual 2 P eK.toMonoidHom).symm
  have hmaxP : IsCoatom P := by
    apply (eK.mapSubgroup.isCoatom_iff P).mp
    change IsCoatom (P.map eK.toMonoidHom)
    rwa [hPN]
  have hcardP : Nat.card P = 24 := by
    rw [Nat.card_congr (eK.subgroupMap P).toEquiv]
    change Nat.card (P.map eK.toMonoidHom) = 24
    rwa [hPN]
  refine ⟨⟨SK, hSK, P, rfl, hSKP, hmaxP, hcardP, hr, ?_, g, P₀, hP₀, ?_, hA, hSM, hB⟩⟩
  · rw [← hr]
    exact (map_subgroupOf_eq_of_le hZK).symm
  · rwa [hPN]
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
