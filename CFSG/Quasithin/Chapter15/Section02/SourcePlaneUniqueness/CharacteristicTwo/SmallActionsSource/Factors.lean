module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Wreath
public import Theory.GroupTheory.PResidual.NormalCubicLines
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.GroupTheory.IndexTwoConjugateSpan

/-!
# Conjugate residual factors for the reducible small action

The actual wreath quotient of H proves that T acts irreducibly on
K/O₂(K), with K = O²(H). If S has index two and acts reducibly, an
invariant cubic line lifts to a normal two-perfect subgroup of K.
Its conjugate under any specified t in T − S is the other factor;
their join is K. Their normality proves the commutator containment
needed in 15.2.22. Reducibility also forces O₂(H) into S.

These are actual residual factors with order-three core quotients.
Identification of the earlier marked H₁,H₂ is a separate source step;
the record does not rename arbitrary overgroups as those parabolics.
The local normalizer and binary-component applications are in
SmallActionsSource.PairApplications.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.21(1), printed p.1114; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_of_core_le {K L : Subgroup G}
    [IsMulCommutative (K ⧸ pCore 2 K)]
    (hQL : K.pCoreIn 2 ≤ L) (hLK : L ≤ K) :
    K ≤ normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hker : q.ker ≤ L.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hQL (mem_map_of_mem K.subtype hx)
  have hn : (L.subgroupOf K).Normal := by
    rw [← comap_map_eq_self hker]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer hLK).mp hn

private theorem sylow_isCoatom (H : Subgroup G) (S : Sylow 2 H)
    (e : (H ⧸ pCore 2 H) ≃* ChosenGeometry.Wreath) : IsCoatom (S : Subgroup H) := by
  let f := (e.trans ChosenGeometry.matrixWreathEquiv).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := (e.trans ChosenGeometry.matrixWreathEquiv).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change (e.trans ChosenGeometry.matrixWreathEquiv) (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ _
    rw [← (e.trans ChosenGeometry.matrixWreathEquiv).map_one,
      (e.trans ChosenGeometry.matrixWreathEquiv).injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hm := isCoatom_comap_of_surjective hf
    (wreath_two_sylow_isCoatom (S.mapSurjective hf))
  change IsCoatom (((S : Subgroup H).map f).comap f) at hm
  rwa [comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal S)] at hm

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- The original Sylow action is irreducible, using the actual wreath quotient of H. -/
theorem sylow_irreducible :
    IsSmallActionIrreducible (T : Subgroup G) (smallActionK H) := by
  let K := smallActionK H
  let e := ChosenGeometry.residualQuotientEquiv H d.geometry.quotient.some
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hKH : K ≤ H := map_subtype_le _
  have hTH : (T : Subgroup G) ≤ H := d.geometry.outside.1.1.2
  have hHK : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  refine ⟨hTH.trans hHK, ?_⟩
  intro L hQL hLK hTL
  have hKL : K ≤ normalizer (L : Set G) := normalizes_of_core_le hQL hLK
  have hHL : H ≤ normalizer (L : Set G) := by
    rw [← d.residual_sup_sylow]
    exact sup_le hKL hTL
  have hLH : L ≤ H := hLK.trans hKH
  let A := L.subgroupOf H
  let P := T.subtype hTH
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHL
  by_cases hLP : L ≤ (T : Subgroup G)
  · left
    apply le_antisymm ?_ hQL
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hLP) hLK hKL
  · right
    have hgen : A ⊔ (P : Subgroup H) = ⊤ := by
      rcases (sylow_isCoatom H P d.geometry.quotient.some).le_iff.mp
        (show (P : Subgroup H) ≤ A ⊔ (P : Subgroup H) from le_sup_right) with he | he
      · exact he
      · exfalso
        apply hLP
        intro x hx
        have hm : (⟨x,hLH hx⟩ : H) ∈ (P : Subgroup H) := he ▸
          (show (⟨x,hLH hx⟩ : H) ∈ A ⊔ (P : Subgroup H) from
            (show A ≤ A ⊔ (P : Subgroup H) from le_sup_left)
              (show (⟨x,hLH hx⟩ : H) ∈ A from hx))
        exact hm
    have hKA : pResidual 2 H ≤ A := sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top A (P : Subgroup H) P.isPGroup' hgen⟩
    exact le_antisymm hLK (by
      rintro _ ⟨x,hx,rfl⟩
      exact hKA hx)

include d in
/-- Reducibility forces the entire original two-core into S, the core
containment used in the first paragraph of the proof of 15.2.21. -/
theorem core_le_planeSylow_of_reducible (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    H.pCoreIn 2 ≤ smallActionS T ZS := by
  let K := smallActionK H
  let S := smallActionS T ZS
  let Q := H.pCoreIn 2
  have hirr := sylow_irreducible d
  have hTH : (T : Subgroup G) ≤ H := d.geometry.outside.1.1.2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hHK : H ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 H).le_normalizer_map H.subtype
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKQ : K ≤ normalizer (Q : Set G) := (map_subtype_le _).trans hHQ
  have hQK : Q ≤ normalizer (K : Set G) := (pCoreIn_le 2 H).trans hHK
  have hcomm : ⁅Q,K⁆ ≤ K.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 H).to_le (le_normalizer_iff_commutator_le_left.mp hKQ))
    (le_normalizer_iff_commutator_le_right.mp hQK)
    (normalizer_commutator_ge_right Q K)
  intro t ht
  by_contra htS
  change t ∉ S at htS
  apply hnot
  refine ⟨inf_le_left.trans hirr.1, ?_⟩
  intro L hQL hLK hSL
  have hQLn : Q ≤ normalizer (L : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl hLK).trans hcomm).trans hQL)
  apply hirr.2 L hQL hLK
  intro x hx
  by_cases hxS : x ∈ S
  · exact hSL hxS
  · have hxt : x*t⁻¹ ∈ S := by
      apply ((S.subgroupOf (T : Subgroup G)).mul_mem_iff_of_index_two
        (d.escape_index hI).2 (a := ⟨x,hx⟩)
        (b := ⟨t⁻¹,(T : Subgroup G).inv_mem (hQT ht)⟩)).mpr
      change x ∈ S ↔ t⁻¹ ∈ S
      simp only [hxS, inv_mem_iff, htS]
    simpa only [inv_mul_cancel_right] using
      (normalizer (L : Set G)).mul_mem (hSL hxt) (hQLn ht)

private theorem line_card {K L : Subgroup G}
    (hK : Nat.card (K ⧸ pCore 2 K) = 9)
    (hQL : K.pCoreIn 2 ≤ L) (hLK : L ≤ K)
    (hLQ : L ≠ K.pCoreIn 2) (hLKne : L ≠ K) :
    Nat.card ((L.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let A := (L.subgroupOf K).map q
  have hker : q.ker ≤ L.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hQL (mem_map_of_mem K.subtype hx)
  have hne : A ≠ ⊥ := by
    intro he
    apply hLQ
    apply le_antisymm ?_ hQL
    have hA := (map_eq_bot_iff (L.subgroupOf K)).mp he
    rw [QuotientGroup.ker_mk'] at hA
    intro x hx
    exact mem_map_of_mem K.subtype (hA (show (⟨x,hLK hx⟩ : K) ∈ L.subgroupOf K from hx))
  have hnt : A ≠ ⊤ := by
    intro he
    apply hLKne
    have hc := congrArg (comap q) he
    rw [comap_map_eq_self hker, comap_top] at hc
    exact le_antisymm hLK (by
      intro x hx
      exact show (⟨x,hx⟩ : K) ∈ L.subgroupOf K from hc.symm ▸ mem_top _)
  have hd : Nat.card A ∣ 3 ^ 2 := by simpa only [hK, show (3:ℕ)^2=9 from rfl] using A.card_subgroup_dvd_card
  obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  interval_cases n
  · exact (hne (card_eq_one.mp hc)).elim
  · exact hc
  · exact (hnt (eq_top_of_card_eq A (hc.trans hK.symm))).elim

/-- The actual two-perfect normal factors, with cubic quotients and the
original ambient conjugation. This does not name the earlier H₁,H₂. -/
structure ResidualPair (T S K : Subgroup G) (t : G) where
  K₁ : Subgroup G
  K₂ : Subgroup G
  t_mem : t ∈ T
  t_not_mem : t ∉ S
  first : K₁ ∈ normalCubicResiduals K
  second : K₂ ∈ normalCubicResiduals K
  span : K₁ ⊔ K₂ = K
  conjugate : K₁.map (MulAut.conj t).toMonoidHom = K₂
  normalized : S ≤ normalizer (K₁ : Set G)

include d in
/-- Construct both normal cubic residuals for any specified element of T − S. -/
theorem exists_residualPair (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    Nonempty (ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t) := by
  classical
  let K := smallActionK H
  let S := smallActionS T ZS
  let e := ChosenGeometry.residualQuotientEquiv H d.geometry.quotient.some
  let : IsElementaryAbelian 3 (K ⧸ pCore 2 K) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hKcard : Nat.card (K ⧸ pCore 2 K) = 9 :=
    (Nat.card_congr e.toEquiv).trans
      Chapter13.Section08.Components.Swapped.LinearThree.WreathModel.cubicBase_card
  have hirr := sylow_irreducible d
  have hSK : S ≤ normalizer (K : Set G) := inf_le_left.trans hirr.1
  obtain ⟨L,hQL,hLK,hSL,hLQ,hLKne⟩ : ∃ L : Subgroup G,
      K.pCoreIn 2 ≤ L ∧ L ≤ K ∧ S ≤ normalizer (L : Set G) ∧
      L ≠ K.pCoreIn 2 ∧ L ≠ K := by
    have hn : ¬ ∀ L : Subgroup G, K.pCoreIn 2 ≤ L → L ≤ K →
        S ≤ normalizer (L : Set G) → L = K.pCoreIn 2 ∨ L = K :=
      fun hh => hnot ⟨hSK,hh⟩
    push Not at hn
    exact hn
  have hi : S.relIndex (T : Subgroup G) = 2 := (d.escape_index hI).2
  let f := (MulAut.conj t).toMonoidHom
  let L₂ := L.map f
  have htK : K.map f = K := mem_normalizer_iff_map_conj_eq.mp (hirr.1 ht)
  have hL₂K : L₂ ≤ K := (map_mono hLK).trans_eq htK
  have hTLspan : (T : Subgroup G) ≤ normalizer ((L ⊔ L₂ : Subgroup G) : Set G) := by
    simpa only [inv_inv] using index_two_normalizes_pair S (T : Subgroup G) L
      inf_le_left hi t⁻¹ ((T : Subgroup G).inv_mem ht)
      (by simpa only [inv_mem_iff] using htS) hSL
  have hspan : L ⊔ L₂ = K := by
    rcases hirr.2 (L ⊔ L₂) (hQL.trans le_sup_left) (sup_le hLK hL₂K) hTLspan with he | he
    · exact (hLQ (le_antisymm (le_sup_left.trans_eq he) hQL)).elim
    · exact he
  let K₁ := (pResidual 2 L).map L.subtype
  let K₂ := K₁.map f
  have hconj : K₂ = (pResidual 2 L₂).map L₂.subtype := map_embedded_pResidual 2 L f
  have hKn : K ≤ normalizer (L : Set G) := normalizes_of_core_le hQL hLK
  have hK₂n : K ≤ normalizer (L₂ : Set G) := by
    rw [← htK]
    exact (map_mono hKn).trans (le_normalizer_map _)
  let : (L.subgroupOf (L ⊔ L₂)).Normal := normal_subgroupOf_of_le_normalizer (hspan ▸ hKn)
  let : (L₂.subgroupOf (L ⊔ L₂)).Normal := normal_subgroupOf_of_le_normalizer (hspan ▸ hK₂n)
  have hKspan : K₁ ⊔ K₂ = K := by
    rw [hconj, embedded_pResidual_sup_of_relative_normal, hspan,
      (pResidual_eq_top_iff 2 K).mpr (isPPerfect_embedded_pResidual 2 H),
      ← MonoidHom.range_eq_map, range_subtype]
  have hfirst : K₁ ∈ normalCubicResiduals K := by
    let A := (L.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
    have hA : Nat.card A = 3 := line_card hKcard hQL hLK hLQ hLKne
    have hLift := normalCubicResiduals_map_subtype K (NormalCubicLines.lift A)
      (NormalCubicLines.lift_mem hKcard A hA)
    have hker : (QuotientGroup.mk' (pCore 2 K)).ker ≤ L.subgroupOf K := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact hQL (mem_map_of_mem K.subtype hx)
    have hpre : A.comap (QuotientGroup.mk' (pCore 2 K)) = L.subgroupOf K :=
      comap_map_eq_self hker
    dsimp only [NormalCubicLines.lift] at hLift
    rw [hpre, map_embedded_pResidual, map_subgroupOf_eq_of_le hLK] at hLift
    exact hLift
  exact ⟨⟨K₁,K₂,ht,htS,hfirst,
    normalCubicResiduals_conjugate K K₁ t (hirr.1 ht) hfirst,
    hKspan,rfl,hSL.trans (normalizer_le_normalizer_characteristic_image L (pResidual 2 L))⟩⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
