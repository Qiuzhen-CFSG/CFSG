module
public import CFSG.Quasithin.Chapter14.Section06.SourceOddCoreReduction
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.PGroup.CharacteristicKernel
/-!
# The primitive odd residual in the original plane branch

For a minimal outside subgroup J, any nontrivial normal odd subgroup B of
J/O₂(J) is its two-residual. The two-residual of the preimage of B gives
an outside subgroup after adjoining T by 14.6.1(4); minimality makes that
join all of J. Its image shows that the quotient by B is a two-group.
Choosing B elementary and minimal normal therefore makes the literal
residual elementary. Since the residual is abelian and supplements the
mapped Sylow subgroup, minimal normality is exactly irreducibility of
that Sylow action.

The final theorem applies this to an actual odd-core counterexample.
It supplies the original primitive input of 14.6.12 without replacing
J/O₂(J) by the further minimal-parabolic star quotient.

Source: Aschbacher--Smith, 14.6.11--12, printed pp.1030--1031.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab


private theorem source_minimal_normal_odd_residual
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (B : Subgroup (J ⧸ pCore 2 J)) [B.Normal]
    (hne : B ≠ ⊥) (ho : Odd (Nat.card B)) :
    pResidual 2 (J ⧸ pCore 2 J) = B := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := B.comap q
  let X₀ := (pResidual 2 A).map A.subtype
  let X := X₀.map J.subtype
  have hXJ : X ≤ J := map_subtype_le _
  have hJX : J ≤ normalizer (X : Set G) := by
    have hh := X₀.le_normalizer_map J.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hXp : IsPPerfect 2 X :=
    (isPPerfect_embedded_pResidual 2 A).of_surjective
      (equivMapOfInjective X₀ J.subtype J.subtype_injective).toMonoidHom
      (equivMapOfInjective X₀ J.subtype J.subtype_injective).surjective
  have hXne : X ≠ ⊥ := by
    intro hz
    have hX₀ : X₀ = ⊥ := (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz
    have hr : pResidual 2 A = ⊥ := (map_eq_bot_iff_of_injective _ A.subtype_injective).mp hX₀
    have hAp : IsPGroup 2 A := (isPGroup_quotient_pResidual (G := A) 2).of_injective
      (QuotientGroup.mk' (pResidual 2 A)) (by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk',hr])
    have hBp : IsPGroup 2 B := by
      have hh := hAp.map q
      change IsPGroup 2 ((B.comap q).map q) at hh
      rwa [map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
        top_inf_eq] at hh
    rcases hBp.card_eq_or_dvd with hc | hc
    · exact hne ((eq_bot_iff_card B).mpr hc)
    · exact ho.not_two_dvd_nat hc
  have hout := source_lemma_14_6_1_4 hG T hempty hM hu hmany hcard e hab
    J hJ.1 X hXJ hJX hXp hXne
  have hgen : X ⊔ (T : Subgroup G) = J :=
    le_antisymm (sup_le hXJ hJ.1.1.2) (hJ.2 hout (sup_le hXJ hJ.1.1.2))
  have hgen₀ : X₀ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJ.1.1.2, ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hBgen : B ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤ := by
    apply top_unique
    rw [← MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pCore 2 J)),
      MonoidHom.range_eq_map, ← hgen₀, Subgroup.map_sup]
    apply sup_le_sup_right
    exact map_le_iff_le_comap.mpr (map_subtype_le _)
  have hquot : IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (((T : Subgroup G).subgroupOf J).map q)
      (T.isPGroup'.comap_subtype.map q) hBgen
  apply le_antisymm ((pResidual_le_iff_isPGroup_quotient 2 B).mpr hquot)
  intro b hb
  exact mem_pResidual_of_orderOf_coprime
    ((Nat.coprime_two_left.mpr ho).coprime_dvd_right
      (by simpa using orderOf_dvd_natCard (⟨b,hb⟩ : B)))

theorem source_solvable_minimal_elementary_residual
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J) :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
      IsElementaryAbelian p (pResidual 2 (J ⧸ pCore 2 J)) ∧
      primeRank p (J ⧸ pCore 2 J) ≤ 2 ∧
      pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ ∧
      ∀ B : Subgroup (J ⧸ pCore 2 J), B.Normal →
        B ≤ pResidual 2 (J ⧸ pCore 2 J) →
        B = ⊥ ∨ B = pResidual 2 (J ⧸ pCore 2 J) := by
  obtain ⟨p,hp,hr,_hq,hbound⟩ := source_solvable_minimal_prime
    hG T hempty hM hu hmany hcard e hab J hJ hs
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have hne : pCore p (J ⧸ pCore 2 J) ≠ ⊥ := by
    intro hz
    have ht : IsPGroup 2 (J ⧸ pCore 2 J) :=
      (isPGroup_quotient_pResidual (G := J ⧸ pCore 2 J) 2).of_injective
        (QuotientGroup.mk' (pResidual 2 (J ⧸ pCore 2 J))) (by
          apply (MonoidHom.ker_eq_bot_iff _).mp
          rw [QuotientGroup.ker_mk', hr, hz])
    have hJp : IsPGroup 2 J := by
      have hh := (ht.to_subgroup ⊤).comap_of_ker_isPGroup
        (QuotientGroup.mk' (pCore 2 J))
        (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      rw [comap_top] at hh
      exact hh.of_equiv topEquiv
    have he : J = (T : Subgroup G) := (T.is_maximal' hJp hJ.1.1.2)
    exact hJ.1.2 (he ▸ hM.1.2)
  obtain ⟨B,hBn,hBne,hBP,hBE,hmin⟩ := exists_minimal_normal_le_pCore hne
  let := hBn
  let := hBE
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p B).exists_card_eq
    rw [hn]
    exact ho.pow
  have he := source_minimal_normal_odd_residual hG T hempty hM hu hmany hcard e hab
    J hJ B hBne hodd
  refine ⟨p,hp,he.symm ▸ hBE,hbound,he.symm ▸ hBne,?_⟩
  intro W hW hWR
  rw [he] at hWR ⊢
  exact hmin W hW hWR

theorem source_solvable_minimal_irreducible_residual
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J) :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
      IsElementaryAbelian p (pResidual 2 (J ⧸ pCore 2 J)) ∧
      primeRank p (J ⧸ pCore 2 J) ≤ 2 ∧
      Stellmacher.IsIrreducibleSection
        (((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ⊥
        (pResidual 2 (J ⧸ pCore 2 J)) := by
  obtain ⟨p,hp,hE,hbound,hne,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let R := pResidual 2 (J ⧸ pCore 2 J)
  let S := ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
  let := hE
  have hgen : R ⊔ S = ⊤ := pResidual_sup_sylow_eq_top
    ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
  refine ⟨p,hp,hE,hbound,bot_le,Ne.symm hne,?_⟩
  intro W _ hWR hi
  have hSW : S ≤ normalizer (W : Set (J ⧸ pCore 2 J)) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro w
    constructor
    · exact hi ⟨t,ht⟩ w
    · intro hw
      have hh := hi ⟨t⁻¹,S.inv_mem ht⟩ (t*w*t⁻¹) hw
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  have hRW : R ≤ normalizer (W : Set (J ⧸ pCore 2 J)) :=
    ((le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative R)).trans (centralizer_le hWR)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hWn : W.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hRW hSW))
  exact hmin W hWn hWR

theorem source_oddCore_counterexample_primitive
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
        IsElementaryAbelian p (pResidual 2 (J ⧸ pCore 2 J)) ∧
        primeRank p (J ⧸ pCore 2 J) ≤ 2 ∧
        Stellmacher.IsIrreducibleSection
          (((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ⊥
          (pResidual 2 (J ⧸ pCore 2 J)) := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  exact ⟨J,hJ,hJH,hs,source_solvable_minimal_irreducible_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs⟩


end CFSG.Quasithin.Chapter14.Section06
