module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondRadicalAction

/-!
# The remaining second component supplies a first-normalizer signalizer

The surviving odd nilpotent SL₂(5) row supplies a canonical member of Ξ.
Its small binary action is trivial on all of V₂, so it lies with T inside
N_G(V₁). The genuine embedding theorem 1.3.4 leaves only a swapped rank-one
component or an odd linear-three component: its noncyclic radical automizer
excludes the symplectic alternative, and its prime is greater than three.
If the first residual normalizes this signalizer, nonsolvable uniqueness
forces equality of the second component. This also eliminates the normal
branch of 1.3.4 from the surviving comparison.

The final consumer discharges the extension and field-four premises using
the already proved second-normalizer sieve. SecondEquality discharges the comparison with the first
containing component. Both field-four triangle orientations remain with
the relative-components assembly owner. The preceding flag, Cartan and
natural-action inputs are discharged by the natural-local-geometry owner.
Source: Aschbacher--Smith, 11.1.2, printed p.765, combined manuscript of
1 March 2004; the corrected 1.3.4 includes the Held alternative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem second_containing_local {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K) :
    K ∈ Chapter1.L G T := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi 1 : Set G) := f.invariant 1
  exact mem_L_of_cComponent (mem_H_of_isTwoLocal (f.normalizer_twoLocal 1))
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩ hK.1 hK.2

/-- The surviving extension row supplies the canonical source signalizer:
it is characteristic in K, fixes full V₂, and lies with T in N_G(V₁). -/
theorem second_nilpotent_signalizer
    {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hfour : S.field.degree = 2)
    (hm : LocalModels.HasExtension (K ⧸ pCore 2 K)
      (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
      (fun Q _ => Source.IsSL Q 2 5))
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      r ∣ Nat.card (fittingSubgroup (XiQuotient K)) ∧
      XiP r K ∈ Xi G (T : Subgroup G) ∧
      XiP r K ≤ K ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) ∧
      XiP r K ≤ centralizer (f.Vi 1 : Set G) ∧
      XiP r K ⊔ (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) := by
  have hlocal := second_containing_local D S f hK.1
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hn := SecondRadicalAction.not_quasisimple_of_nilpotent_extension
    (pCore_quotient_pCore_eq_bot 2) hm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    have ht := hK.1.2.subgroupOf le_rfl
    rw [subgroupOf_self] at ht
    let e := subgroupOfEquivOfLe hK.1.1
    have he := ht.map_equiv e
    rwa [map_top_of_surjective e.toMonoidHom e.surjective] at he
  let := pCore_isNilpotent (p := 2) (G := K)
  have hquot : (⊤ : Subgroup (K ⧸ pCore 2 K)).IsCComponent := by
    have h := htop.map_quotient (pCore 2 K)
    rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  obtain ⟨r,hr,ho,hd⟩ := SecondRadicalAction.exists_odd_fitting_prime hquot
    (pCore_quotient_pCore_eq_bot 2) hn
  let : Fact r.Prime := ⟨hr⟩
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have hA38 : ∀ (Y : Type _) [Group Y] [Finite Y],
      IsSQTK CFSG.KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ B : Subgroup Y, B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hY hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hY hO hB
  have hQall : ∀ J ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK CFSG.KnownSimple.IsKnownSimple ((J ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)) :=
    fun _ hJ => uniqueness_local_quotient_sqtk S.source.simpleQTKE hJ.2.2
  have hXi : XiP r K ∈ Xi G (T : Subgroup G) :=
    lemma_1_3_3 hA36 hA38 hQall ⟨K,hlocal,hn,r,hr,ho,hd,rfl⟩
  have hr3 := (XiP_oddQuotient_of_A36 hA36 hlocal (hQall K hlocal) hn ho hd).1
  have hnorm : K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) :=
    sup_le (XiP_invariant r K.le_normalizer) (XiP_invariant r hTK)
  have hdim : Module.finrank (ZMod 2) (Additive (f.Vi 1)) ≤ 6 := by
    simpa only [hfour] using second_cover_finrank_le D S f p hp hk
  let ρ := (flagAction f 1).comp (inclusion hK.1.1)
  have hfix := SecondRadicalAction.xiP_small_action S.source.simpleQTKE T hlocal hTK hn hm
    ρ hdim ho hd
  have hcentral : XiP r K ≤ centralizer (f.Vi 1 : Set G) := by
    intro x hx v hv
    have he := LinearMap.congr_fun (hfix ⟨x,XiP_le r K hx⟩ hx)
      (Additive.ofMul (⟨v,hv⟩ : f.Vi 1))
    have hh := congrArg (fun z : Additive (f.Vi 1) => (z.toMul : G)) he
    change x * v * x⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hline : f.Vi 0 ≤ f.Vi 1 := (c.preimage_le_iff _ _).mpr (f.nested (by decide))
  exact ⟨r,hr,ho,hr3,hd,hXi,XiP_le r K,hnorm,hcentral,
    sup_le ((hcentral.trans (centralizer_le hline)).trans
      (Subgroup.centralizer_le_normalizer _)) (f.invariant 0)⟩

/-- Applying the genuine 1.3.4 theorem to this same signalizer leaves
only normality, a swapped rank-one component, or an odd linear-three
component. The noncyclic radical automizer excludes the symplectic row. -/
theorem second_nilpotent_first_embedding
    {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hfour : S.field.degree = 2)
    (hm : LocalModels.HasExtension (K ⧸ pCore 2 K)
      (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
      (fun Q _ => Source.IsSL Q 2 5))
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      XiP r K ∈ Xi G (T : Subgroup G) ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) ∧
      XiP r K ≤ centralizer (f.Vi 1 : Set G) ∧
      ((XiP r K).subgroupOf (normalizer (f.Vi 0 : Set G))).Normal) ∨
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      XiP r K ∈ Xi G (T : Subgroup G) ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) ∧
      XiP r K ≤ centralizer (f.Vi 1 : Set G) ∧
      ∃ (P : Sylow r (XiP r K)) (J : Subgroup G),
        J ∈ cComponentsIn (normalizer (f.Vi 0 : Set G)) ∧
        IsQuasisimple (XiQuotient J) ∧
        XiP r K ≤ componentOrbit J (T : Subgroup G) ∧
        (XiEmbedding.SwappedFactors (T : Subgroup G)
            ((P : Subgroup (XiP r K)).map (XiP r K).subtype) J ∧
          XiEmbedding.SwappedModel r (XiQuotient J) ∨
        (T : Subgroup G) ≤ normalizer J ∧
          XiEmbedding.LinearThreeModel r (XiQuotient J)) := by
  obtain ⟨r,hr,ho,hr3,hd,hXi,hYK,hnorm,hfix,hplace⟩ :=
    second_nilpotent_signalizer D S f hK hfour hm p hp hk
  let : Fact r.Prime := ⟨hr⟩
  let P : Sylow r (XiP r K) := Classical.arbitrary _
  have hlocal := second_containing_local D S f hK.1
  have hn := SecondRadicalAction.not_quasisimple_of_nilpotent_extension
    (pCore_quotient_pCore_eq_bot 2) hm
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have hQ := uniqueness_local_quotient_sqtk S.source.simpleQTKE hlocal.2.2
  have hodd := (XiP_oddQuotient_of_A36 hA36 hlocal hQ hn ho hd).2
  have hcyc := RadicalActions.XiP_automizer_not_isCyclic_of_A36
    hA36 hlocal hQ hn ho hd P
  have hT0 : (T : Subgroup G) ≤ normalizer (f.Vi 0 : Set G) := f.invariant 0
  have hT : IsSylowIn 2 (T : Subgroup G) (normalizer (f.Vi 0 : Set G)) :=
    ⟨T.subtype hT0,by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT0]⟩
  have hin := XiEmbedding.localInput_of_mem_Xi hXi hT hplace ho hodd P
  rcases hin.adequate_knownSimple
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)) hT with h | h
  · exact .inl ⟨r,hr,ho,hr3,hXi,hnorm,hfix,h⟩
  · obtain ⟨J,hJ,hq,hYJ,hmodels⟩ := h
    refine .inr ⟨r,hr,ho,hr3,hXi,hnorm,hfix,P,J,hJ,hq,hYJ,?_⟩
    rcases hmodels with ⟨_,hswap | ⟨hTJ,hlin | ⟨_,hcycle⟩ | ⟨he,_⟩⟩⟩ | ⟨he,_⟩
    · exact .inl hswap
    · exact .inr ⟨hTJ,hlin⟩
    · exact (hcyc hcycle).elim
    · omega
    · omega


/-- A signalizer normalized by both residuals puts the containing component
inside the original unique maximal local normalizer, forcing equality. -/
theorem second_eq_of_normalized_signalizer
    (hjoin : L = f.Li 0 ⊔ f.Li 1)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    {K Y : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 ≤ K) (hY : Y ∈ Xi G (T : Subgroup G))
    (hKY : K ⊔ (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfirst : f.Li 0 ≤ normalizer (Y : Set G)) : f.Li 1 = K := by
  have hu := nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      L ⊔ (T : Subgroup G) ≤ M → M = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  have hcore := hY.pCoreIn_ne_bot
    (fun M hM N hN hNM hnorm => lemma_1_1_3_1 hM hN hNM hnorm)
    (lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T))
  have hLY : L ⊔ (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    rw [hjoin]
    exact sup_le (sup_le hfirst (hLK.trans (le_sup_left.trans hKY)))
      (le_sup_right.trans hKY)
  have hnorm := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  have hbound := normalizer_le_of_unique_maximalTwoLocal hunique
    (isPGroup_pCoreIn 2 Y) hcore (hLY.trans hnorm)
  exact flag_component_eq_of_le_component_normalizer D S f 1 hm hK hLK
    ((le_sup_left.trans hKY).trans (hnorm.trans hbound))

/-- The normal branch of the genuine first-normalizer embedding theorem
is impossible for a strict second component. Thus the remaining signalizer
comparison has only the two specified component models. -/
theorem second_strict_nilpotent_first_embedding
    (hjoin : L = f.Li 0 ⊔ f.Li 1)
    (hLmodel : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hLK : f.Li 1 < K) (hfour : S.field.degree = 2)
    (hm : LocalModels.HasExtension (K ⧸ pCore 2 K)
      (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
      (fun Q _ => Source.IsSL Q 2 5))
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      XiP r K ∈ Xi G (T : Subgroup G) ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) ∧
      XiP r K ≤ centralizer (f.Vi 1 : Set G) ∧
      ∃ (P : Sylow r (XiP r K)) (J : Subgroup G),
        J ∈ cComponentsIn (normalizer (f.Vi 0 : Set G)) ∧
        IsQuasisimple (XiQuotient J) ∧
        XiP r K ≤ componentOrbit J (T : Subgroup G) ∧
        (XiEmbedding.SwappedFactors (T : Subgroup G)
            ((P : Subgroup (XiP r K)).map (XiP r K).subtype) J ∧
          XiEmbedding.SwappedModel r (XiQuotient J) ∨
        (T : Subgroup G) ≤ normalizer J ∧
          XiEmbedding.LinearThreeModel r (XiQuotient J)) := by
  rcases second_nilpotent_first_embedding D S f hK hfour hm p hp hk with h | h
  · obtain ⟨r,hr,ho,hr3,hXi,hnorm,hfix,hn⟩ := h
    have hline : f.Vi 0 ≤ f.Vi 1 := (c.preimage_le_iff _ _).mpr (f.nested (by decide))
    have hYH : XiP r K ≤ normalizer (f.Vi 0 : Set G) :=
      (hfix.trans (centralizer_le hline)).trans (Subgroup.centralizer_le_normalizer _)
    have hfirst : f.Li 0 ≤ normalizer (XiP r K : Set G) :=
      ((localResidual_le _).trans inf_le_right).trans
        ((normal_subgroupOf_iff_le_normalizer hYH).mp hn)
    exact (hLK.ne (second_eq_of_normalized_signalizer D S f hjoin hLmodel hK.1
      hLK.le hXi hnorm hfirst)).elim
  · exact h

/-- The complete second catalogue now gives equality or a literal
signalizer comparison at the first normalizer. The extension model and
field-four restriction are supplied by the proved sieve, not assumed. -/
theorem second_equal_or_signalizer_comparison_from_cartan
    (hu : f.IsInnerUnique) (hjoin : L = f.Li 0 ⊔ f.Li 1)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
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
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    f.Li 1 = K ∨ (
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      XiP r K ∈ Xi G (T : Subgroup G) ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (XiP r K : Set G) ∧
      XiP r K ≤ centralizer (f.Vi 1 : Set G) ∧
      ∃ (P : Sylow r (XiP r K)) (J : Subgroup G),
        J ∈ cComponentsIn (normalizer (f.Vi 0 : Set G)) ∧
        IsQuasisimple (XiQuotient J) ∧
        XiP r K ≤ componentOrbit J (T : Subgroup G) ∧
        (XiEmbedding.SwappedFactors (T : Subgroup G)
            ((P : Subgroup (XiP r K)).map (XiP r K).subtype) J ∧
          XiEmbedding.SwappedModel r (XiQuotient J) ∨
        (T : Subgroup G) ≤ normalizer J ∧
          XiEmbedding.LinearThreeModel r (XiQuotient J))) := by
  by_cases he : f.Li 1 = K
  · exact .inl he
  rcases second_equal_or_nilpotent_from_cartan D S f hu hm hX hK hLK
    hXcard hfaith hcore π hπ p hp hact hk with h | ⟨hn,hmodel⟩
  · exact .inl h
  · exact .inr (second_strict_nilpotent_first_embedding D S f hjoin hm hK
      (lt_of_le_of_ne hLK he) hn hmodel p hp hk)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
