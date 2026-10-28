module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondRadical
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Equality and unique noncentrality at the second normalizer

The canonical signalizer of the remaining odd-radical row lies in the
T-orbit of a component of the first flag normalizer. That component differs
from the relatively normal component containing L₁: a swapped component is
not T-invariant, and the odd linear-three covers are excluded by the literal
ternary embedding argument, including the case of equality with L₁.

Distinct components commute modulo the actual local two-core. The
signalizer's two-residual identity therefore makes the first containing
component normalize it. The two original residuals generate L, and
nonsolvable uniqueness puts the second containing component in N_G(L),
forcing it to equal L₂. This finishes the second-normalizer exclusion at
every field degree. The final consumer retains He membership and proves
unique noncentrality on the whole original V₂, including C_V(L).

Only preceding flag, Cartan, natural-action and radical-action inputs are
explicit; their producers are qt-d-1222-natural-flag-cartan and
qt-d-1222-natural-preliminary-source, with final discharge by
qt-d-1222-natural-local-geometry. The relative-components owner still owes
both field-four triangle orientations at the first normalizer before the
complete 11.1.1--11.1.3 source-family assembly.
Source: Aschbacher--Smith, 11.1.2--11.1.3, printed p.765, combined manuscript
of 1 March 2004, using 1.2.1(2), 1.3.2(5), and the corrected 1.3.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem linear_three_five_order {A : Type*} [Group A] [Finite A]
    (hm : XiEmbedding.LinearThreeModel 5 A) : 372000 ∣ Nat.card A := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    have he : Nat.card PSL(3,F) = 372000 := by omega
    rw [Nat.card_congr e.toEquiv]
    rw [←he]
    exact card_quotient_dvd_card (center SL(3,F))
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    have he : Nat.card PSL(3,F) = 372000 := by omega
    rw [Nat.card_congr e.toEquiv,he]

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The first containing component cannot be either linear-three cover
from the signalizer embedding theorem, even when it equals the first residual. -/
theorem first_not_signalizer_linear_three
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) {r : ℕ} (hr : r.Prime) (ho : Odd r) :
    ¬ XiEmbedding.LinearThreeModel r (XiQuotient K) := by
  intro hlin
  have hs : LocalModels.IsPSLSign (K ⧸ pCore 2 K) false 3 r ∨
      LocalModels.IsSLSign (K ⧸ pCore 2 K) false 3 r := hlin.elim Or.inr Or.inl
  obtain ⟨hn,rfl⟩ := Embedding.flag_odd_ternary_parameters D S f 0 hm hK hLK hr ho false hs
  by_cases he : f.Li 0 = K
  · have hc : Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) = 60 := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
      rw [hF,hn] at hcard
      norm_num [Fin.prod_univ_succ] at hcard
      rw [Nat.card_congr e.toEquiv]
      omega
    have hd := linear_three_five_order hlin
    rw [←he,hc] at hd
    norm_num at hd
  · exact first_component_not_ternary D S f hm hn hfix hK
      (lt_of_le_of_ne hLK he) false hs

/-- A relatively normal component normalizes a signalizer lying in the
orbit of a distinct component. Commutation is taken modulo the actual
ambient two-core, and the two-residual identity lifts normalization. -/
theorem normal_component_normalizes_signalizer_of_distinct_orbit
    {H B J Y : Subgroup G}
    (hQ : IsSQTK CFSG.KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (hB : Source.NormalComponentIn H B) (hJ : Source.ComponentIn H J)
    (hT : IsSylowIn 2 (T : Subgroup G) H)
    (hY : Y ∈ Xi G (T : Subgroup G)) (hYJ : Y ≤ componentOrbit J (T : Subgroup G))
    (hne : J ≠ B) : B ≤ normalizer (Y : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := (isSylowIn_iff.mp hT).2.1
  have hNB : H ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hB.1.1).mp hB.2
  have hNQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hconj : ∀ t : T, J.conjBy (t : G) ∈ cComponentsIn H :=
    fun t => XiEmbedding.SwappedFactorsProof.conjugate_component hJ (hTH t.property)
  have hcomm : ∀ t : T, ⁅J.conjBy (t : G), B⁆ ≤ H.pCoreIn 2 := by
    intro t
    have ht := hconj t
    have hne' : (J.conjBy (t : G)).subgroupOf H ≠ B.subgroupOf H := by
      intro he
      have he' : J.conjBy (t : G) = B := by
        simpa only [map_subgroupOf_eq_of_le ht.1,map_subgroupOf_eq_of_le hB.1.1] using
          congrArg (map H.subtype) he
      have hn := mem_normalizer_iff_map_conj_eq.mp (hNB (hTH t.property))
      exact hne (map_injective (MulAut.conj (t : G)).injective (he'.trans hn.symm))
    have hh := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
      hQ ht.2 hB.1.2 hne'
    have hh' := map_mono (f := H.subtype) (hh.1.trans hh.2)
    simpa only [pCoreIn,map_commutator,map_subgroupOf_eq_of_le ht.1,
      map_subgroupOf_eq_of_le hB.1.1] using hh'
  have horbit : ⁅componentOrbit J (T : Subgroup G),B⁆ ≤ H.pCoreIn 2 :=
    commutator_iSup_le_of_relative_normal H B (H.pCoreIn 2)
      (fun t : T => J.conjBy (t : G)) hNQ (fun t => (hconj t).1) hcomm
  have hYH : Y ≤ H := hYJ.trans (iSup_le fun t => (hconj t).1)
  have hYcomm : ⁅Y,B⁆ ≤ H.pCoreIn 2 := (commutator_mono hYJ le_rfl).trans horbit
  have hnorm : B ≤ normalizer ((H.pCoreIn 2 ⊔ Y : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_sup_le_of_relative_normal H (H.pCoreIn 2) Y B (H.pCoreIn 2)
      hNQ (pCoreIn_le 2 H) hYH
      (le_normalizer_iff_commutator_le_left.mp (hB.1.1.trans hNQ)) hYcomm).trans le_sup_left
  have hres := lemma_1_3_2_5_local hY hT
  have hh := hnorm.trans (normalizer_le_normalizer_characteristic_image
    (H.pCoreIn 2 ⊔ Y) (pResidual 2 (H.pCoreIn 2 ⊔ Y : Subgroup G)))
  rwa [hres] at hh

/-- The actual first containing component normalizes the signalizer
detected in the second-normalizer nilpotent row. -/
theorem first_normalizes_second_signalizer
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {B J Y P : Subgroup G} {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hB : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) B)
    (hLB : f.Li 0 ≤ B)
    (hJ : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) J)
    (hY : Y ∈ Xi G (T : Subgroup G)) (hYJ : Y ≤ componentOrbit J (T : Subgroup G))
    (hmodels : XiEmbedding.SwappedFactors (T : Subgroup G) P J ∧
        XiEmbedding.SwappedModel r (XiQuotient J) ∨
      (T : Subgroup G) ≤ normalizer J ∧ XiEmbedding.LinearThreeModel r (XiQuotient J)) :
    B ≤ normalizer (Y : Set G) := by
  have hTH : (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) := f.invariant 0
  have hT : IsSylowIn 2 (T : Subgroup G) (normalizer (f.Vi 0 : Set G)) :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  apply normal_component_normalizes_signalizer_of_distinct_orbit
    (uniqueness_local_quotient_sqtk S.source.simpleQTKE
      (mem_H_of_isTwoLocal (f.normalizer_twoLocal 0))) hB hJ hT hY hYJ
  intro he
  subst J
  rcases hmodels with ⟨hs,_⟩ | ⟨_,hl⟩
  · exact hs.1 (hTH.trans ((normal_subgroupOf_iff_le_normalizer hB.1.1).mp hB.2))
  · exact first_not_signalizer_linear_three D S f hm hfix hB.1 hLB hr ho hl

/-- The odd-radical row is impossible at the second normalizer, using
the actual first-normalizer component and nonsolvable uniqueness. -/
theorem second_equal_from_cartan
    (hu : f.IsInnerUnique) (hjoin : L = f.Li 0 ⊔ f.Li 1)
    (hm : ∀ i : Fin 2, ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i))
      2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K) (hLK : f.Li 1 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2^S.field.degree-1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) : f.Li 1 = K := by
  rcases second_equal_or_signalizer_comparison_from_cartan D S f hu hjoin (hm 1)
    hX hK hLK hXcard hfaith hcore π hπ p hp hact hk with he | h
  · exact he
  · obtain ⟨r,hr,ho,_,hY,hnorm,_,P,J,hJ,_,hYJ,hmodels⟩ := h
    obtain ⟨B,hB,hLB,_,_⟩ := flag_exists_unique_normal_component_of_model D S f 0 (hm 0)
    exact second_eq_of_normalized_signalizer D S f hjoin (hm 1) hK.1 hLK hY hnorm
      (hLB.trans (first_normalizes_second_signalizer D S f (hm 0) hfix hr ho
        hB hLB hJ hY hYJ hmodels))

/-- The second residual is the relatively normal containing component at
all field degrees, with He membership and unique noncentrality on full V₂.
The original preceding flag, Cartan and radical-action premises remain explicit. -/
theorem second_component_and_unique_from_cartan
    (hu : f.IsInnerUnique) (hjoin : L = f.Li 0 ⊔ f.Li 1)
    (hm : ∀ i : Fin 2, ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i))
      2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2^S.field.degree-1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1) ∧
      f.Li 1 ∈ Chapter1.He G ∧
      Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  have hc : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G) := by
    apply le_trans (pCoreIn_mono_of_normalizes
      (show f.Li 1 ≤ f.Li 1 ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le (f.Li 1).le_normalizer (f.sylow_normalizes_Li 1))) hR
  obtain ⟨K,hK,hLK,hHe,_⟩ := flag_exists_unique_normal_component_of_model D S f 1 (hm 1)
  have heq := second_equal_from_cartan D S f hu hjoin hm hfix hX hK hLK
    hXcard hfaith hc π hπ p hp hact hk
  have hK' : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1) := heq.symm ▸ hK
  exact ⟨hK',heq.symm ▸ hHe,uniqueNoncentral_second_of_radical_and_natural_action
    S f hK'.1 (hm 1) hR π hπ p hp hact⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
