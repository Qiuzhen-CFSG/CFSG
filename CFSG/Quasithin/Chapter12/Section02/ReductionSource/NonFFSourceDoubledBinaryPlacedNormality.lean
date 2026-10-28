module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNormality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedHeld
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureExclusion

/-!
# Literal two-local placement of the original binary doubled orbit

The original odd fixed residual embeds in the selected component's full
central quotient: the centralizer identity makes the full center odd,
whereas the kernel on the residual is a two-group. Its image and the image
of the entire order-64 orbit have the same normalizer. This is a maximal
two-local, its full preimage is the original K intersect N_G(L), and both
images are normal relative to every two-local containing the residual.

The final application retains the original H-star subgroup and prime-order
odd actor. The checked pure-line contradiction removes the w <= 1 outcome;
the surviving alternatives are the unchanged maximal pushing-up pair or
the placed J4/Ru component with the new literal local geometry. Every
component satisfying the existing placement fields receives this geometry,
so it applies to the same component selected in the original alternative.

This does not exclude those alternatives or prove w <= 1. It does not
assume a full Sylow subgroup in the selected local, erase the component
center, or replace the marked six-space by one of its three-space seeds.
Source: Aschbacher--Smith 4.4.6--7 and 4.4.3, printed pp.620--623,
used by 7.3.4 and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Placement through the actual component quotient and original inclusions.
The module map has domain the whole source orbit. -/
@[expose] def BinaryPlacedLocalGeometry (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) : Prop :=
    let K₀ := K.map (normalizer (A : Set G)).subtype
    let a : K₀ ≃* K := (K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm
    let q := (QuotientGroup.mk' (center K)).comp a.toMonoidHom
    let r := q.comp (inclusion hr)
    Function.Injective r ∧
    UniqueMaximalOvergroup r.range (normalizer (r.range : Set (K ⧸ center K))) ∧
    (normalizer (r.range : Set (K ⧸ center K))).comap q =
      (normalizer (L : Set G)).subgroupOf K₀ ∧
    ∃ hWK : D.sourceOrbit ≤ K₀,
      let w := q.comp (inclusion hWK)
      Function.Injective w ∧ Nat.card w.range = 64 ∧
      normalizer (w.range : Set (K ⧸ center K)) =
        normalizer (r.range : Set (K ⧸ center K)) ∧
      (∀ B : Subgroup (K ⧸ center K), IsTwoLocal B → r.range ≤ B →
        (r.range.subgroupOf B).Normal ∧ w.range ≤ B ∧ (w.range.subgroupOf B).Normal)

/-- The original chosen-module hypotheses prove all local placement data
for the same residual and component, without an additional placement premise. -/
theorem sourceOrbit_binary_oddNormalizer_local_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G))) : D.BinaryPlacedLocalGeometry A K hr := by
  unfold BinaryPlacedLocalGeometry
  intro K₀ a q r
  let R := oddActorResidual L A
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let i : R →* K := a.toMonoidHom.comp (inclusion hr)
  obtain ⟨_,hm,hWR,t,ht,hnt,qL,hqL,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  have hKN : K₀ ≤ N := map_subtype_le _
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hr)
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  have hir : Function.Injective r :=
    DoubledBinaryPlacedNormality.central_quotient_injective e i hi hoZ
  have hcentermap : (center K₀).map a.toMonoidHom = center K := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr a ⟨z,hz⟩).property
    · intro z hz
      exact ⟨a.symm z,(centerCongr a.symm ⟨z,hz⟩).property,a.apply_symm_apply z⟩
  let eK := QuotientGroup.congr (center K₀) (center K) a hcentermap
  have hne : W ≠ ⊥ := D.sourceOrbit_weakClosure_setup.nontrivial
  have huQ : UniqueMaximalOvergroup r.range (normalizer (r.range : Set (K ⧸ center K))) :=
    DoubledBinaryPlacedNormality.residual_image_unique_local hKN hr hu hWR hne hm eK
  have hp : (normalizer (r.range : Set (K ⧸ center K))).comap q =
      (normalizer (L : Set G)).subgroupOf K₀ :=
    DoubledBinaryPlacedNormality.residual_normalizer_preimage hKN hr hu hWR hne hm eK
  have hWR' : W ≤ R := hWR.trans (pCoreIn_le 2 R)
  have hWK : W ≤ K₀ := hWR'.trans hr
  let w := q.comp (inclusion hWK)
  have hiw : Function.Injective w := hir.comp (inclusion_injective hWR')
  have hcard : Nat.card W = 64 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,
      D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have hcW : Nat.card w.range = 64 :=
    (Nat.card_congr (MonoidHom.ofInjective hiw).toEquiv).symm.trans hcard
  have hnormal (B : Subgroup (K ⧸ center K)) (hB : IsTwoLocal B) (hRB : r.range ≤ B) :
      (r.range.subgroupOf B).Normal ∧ w.range ≤ B ∧ (w.range.subgroupOf B).Normal := by
    have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp a.surjective
    have hc : q.ker ≤ center K₀ := by
      intro z hz
      have hzK := (QuotientGroup.eq_one_iff (a z)).mp hz
      apply mem_center_iff.mpr
      intro y
      apply a.injective
      simpa only [map_mul] using mem_center_iff.mp hzK (a y)
    exact ⟨(DoubledBinaryPlacedNormality.local_preimage_and_normality
      hKN hr hu q hq hc B hB hRB).2,
      DoubledBinaryPlacedNormality.whole_module_normal_in_local hKN hr hu hWR'
        (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge q hq hc B hB hRB⟩
  have hWN := hnormal (normalizer (r.range : Set (K ⧸ center K)))
    huQ.1.1 r.range.le_normalizer
  have hNRW : normalizer (r.range : Set (K ⧸ center K)) ≤
      normalizer (w.range : Set (K ⧸ center K)) :=
    (normal_subgroupOf_iff_le_normalizer hWN.2.1).mp hWN.2.2
  have hWne : w.range ≠ ⊥ := by
    intro heq
    rw [heq,card_bot] at hcW
    omega
  have hpw : IsPGroup 2 w.range := (IsElementaryAbelian.isPGroup 2 W).of_surjective
    w.rangeRestrict w.rangeRestrict_surjective
  have hNWlocal : IsTwoLocal (normalizer (w.range : Set (K ⧸ center K))) :=
    ⟨w.range,hWne,hpw,rfl⟩
  have hRW := r.range.le_normalizer.trans hNRW
  have hNWR := (normal_subgroupOf_iff_le_normalizer hRW).mp
    (hnormal (normalizer (w.range : Set (K ⧸ center K))) hNWlocal hRW).1
  exact ⟨hir,huQ,hp,hWK,hiw,hcW,le_antisymm hNWR hNRW,hnormal⟩

/-- Any surviving original binary non-FF case has the actual H-star odd
actor and one of the two remaining source alternatives. The placed alternative
retains all earlier fields and the proved geometry of its literal quotient. -/
theorem sourceOrbit_binary_placed_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        (D.BinaryPlacedJankoRudvalisCase A ∧
          ∀ (K : Subgroup (normalizer (A : Set G)))
            (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype),
            centralizer (K : Set (normalizer (A : Set G))) =
              pPrimeCore 2 (normalizer (A : Set G)) → D.BinaryPlacedLocalGeometry A K hr)) := by
  rcases D.sourceOrbit_binary_globalW_or_placed_jankoRudvalis_oddLocal
    h hd hmany hnon F hF hmodel with hw | hx
  · exact (D.sourceOrbit_binary_false_of_globalW_le_one h hd F hF hmodel hnon hw).elim
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcases⟩ := hx
  refine ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  rcases hcases with hpush | hplaced
  · exact Or.inl hpush
  · refine Or.inr ⟨hplaced,?_⟩
    intro K hr hcent
    exact D.sourceOrbit_binary_oddNormalizer_local_placement h hd F hF hmodel A hAC
      (hcard.symm ▸ hpo) hplaced.1 K hr hcent

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
