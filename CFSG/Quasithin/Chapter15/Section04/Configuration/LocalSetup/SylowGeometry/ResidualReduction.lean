module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingInput
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Reduction to the three-prime-to residual with Sylow maximality retained

A two-perfect factor whose two-core quotient is a three-group lies in
`O^{3′}(H)` inside every overgroup `H`: its Sylow three-subgroup is contained
in that residual, and its image modulo the residual is a two-group. Thus
both local factors lie in the actual prime-to-three residual.

Replacing the contrary overgroup by `O^{3′}(H)U` preserves the generated
amalgam, membership in `H`, and the actual Sylow image `U`. The global
maximal Sylow-order bound over the original amalgam also survives this
replacement. It proves that `U` remains Sylow in every new eligible
overgroup, including the normalizer of the new intrinsic two-core.

Identifying the component product with this residual remains a separate
use of A.3.18 or exact 1.2.2(a). This module does not assume that identity,
and does not replace a residual by a core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.2(a),
printed p.504, and the reduction in 15.4.20, printed pp.1163–1164.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect group with three-group two-core quotient lies in the
prime-to-three residual of every overgroup. -/
theorem twoPerfect_three_quotient_le_primeToResidual {L H : Subgroup G}
    (hLH : L ≤ H) (hL : IsPPerfect 2 L)
    (hq : IsPGroup 3 (L ⧸ pCore 2 L)) :
    L ≤ (primeToResidual 3 H).map H.subtype := by
  let f : L →* H := inclusion hLH
  let D := (primeToResidual 3 H).comap f
  let P : Sylow 3 L := Classical.choice Sylow.nonempty
  let q := QuotientGroup.mk' (pCore 2 L)
  have htop : (P : Subgroup L).map q = ⊤ :=
    top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hgen : pCore 2 L ⊔ (P : Subgroup L) = ⊤ := by
    have hh := congrArg (fun A : Subgroup (L ⧸ pCore 2 L) => A.comap q) htop
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using hh
  have hPD : (P : Subgroup L) ≤ D := by
    intro x hx
    obtain ⟨n,hn⟩ := P.isPGroup' (⟨x,hx⟩ : P)
    apply mem_primeToResidual_of_pow (n := n)
    exact (map_pow f x (3^n)).symm.trans
      ((congrArg f (congrArg Subtype.val hn)).trans (map_one f))
  have hD : D = ⊤ := by
    apply hL D inferInstance
    apply isPGroup_quotient_of_sup_eq_top D (pCore 2 L) pCore_isPGroup
    apply top_unique
    rw [← hgen]
    exact sup_le le_sup_right (hPD.trans le_sup_left)
  intro x hx
  exact ⟨f ⟨x,hx⟩, (show (⟨x,hx⟩ : L) ∈ D from hD ▸ mem_top _), rfl⟩


/-- Both factors of the amalgam lie in the actual prime-to-three residual. -/
theorem generated_factors_le_primeToResidual_join {L₁ L₂ U H : Subgroup G}
    (hL₁ : L₁ ≤ H) (hL₂ : L₂ ≤ H)
    (hperfect₁ : IsPPerfect 2 L₁) (hperfect₂ : IsPPerfect 2 L₂)
    (hq₁ : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hq₂ : Nat.card (L₂ ⧸ pCore 2 L₂) = 3) :
    (L₁ ⊔ U) ⊔ (L₂ ⊔ U) ≤ (primeToResidual 3 H).map H.subtype ⊔ U := by
  have ha := twoPerfect_three_quotient_le_primeToResidual hL₁ hperfect₁
    (IsPGroup.of_card (by simpa only [pow_one] using hq₁ : Nat.card (L₁ ⧸ pCore 2 L₁) = 3^1))
  have hb := twoPerfect_three_quotient_le_primeToResidual hL₂ hperfect₂
    (IsPGroup.of_card (by simpa only [pow_one] using hq₂ : Nat.card (L₂ ⧸ pCore 2 L₂) = 3^1))
  exact sup_le (sup_le_sup_right ha U) (sup_le_sup_right hb U)


omit [Finite G] in
/-- An intermediate subgroup containing a Sylow image retains a nontrivial
two-core and has that same Sylow image. -/
theorem HOver_and_sylow_of_intermediate {I H U D : Subgroup G}
    (hH : H ∈ Chapter1.H G) (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = U)
    (hUD : U ≤ D) (hDH : D ≤ H) (hID : I ≤ D) :
    D ∈ Chapter1.HOver G (I : Set G) ∧
      ∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype = U := by
  have hcoreD : H.pCoreIn 2 ≤ D :=
    ((pCoreIn_le_sylow H P).trans_eq hP).trans hUD
  have hc : H.pCoreIn 2 ≤ D.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hcoreD
      (hDH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  refine ⟨⟨?_, hID⟩, restrictSylow P hDH (hP ▸ hUD), ?_⟩
  · exact fun he => hH (le_bot_iff.mp (he ▸ hc))
  · rw [restrictSylow_image,hP]


/-- A global Sylow-order bound applies after replacement by any overgroup
of the original amalgam containing the chosen two-subgroup. -/
theorem HOver_sylow_of_maximal_order {I U D : Subgroup G}
    (hU : IsPGroup 2 U) (hUD : U ≤ D) (hID : I ≤ D)
    (hmax : ∀ H ∈ Chapter1.HOver G (I : Set G), ∀ P : Sylow 2 H,
      Nat.card ((P : Subgroup H).map H.subtype) ≤ Nat.card U) :
    ∀ H ∈ Chapter1.HOver G (D : Set G),
      ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U := by
  intro H hH
  have hUH : U ≤ H := hUD.trans hH.2
  obtain ⟨P,hUP⟩ := (hU.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  have hUP' : U ≤ (P : Subgroup H).map H.subtype := by
    intro u hu
    exact ⟨⟨u,hUH hu⟩,hUP hu,rfl⟩
  exact ⟨P,(eq_of_le_of_card_ge hUP' (hmax H ⟨hH.1,hID.trans hH.2⟩ P)).symm⟩


/-- Construct the residual replacement and retain all overgroup Sylow
assertions, including the corrected core-normalizer assertion for `U`. -/
theorem threeResidual_sylow_replacement {L₁ L₂ T₀ U H : Subgroup G}
    (hH : H ∈ Chapter1.H G) (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = U) (hT₀U : T₀ ≤ U)
    (hL₁H : L₁ ≤ H) (hL₂H : L₂ ≤ H)
    (hperfect₁ : IsPPerfect 2 L₁) (hperfect₂ : IsPPerfect 2 L₂)
    (hq₁ : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hq₂ : Nat.card (L₂ ⧸ pCore 2 L₂) = 3)
    (hmax : ∀ J ∈ Chapter1.HOver G (((L₁ ⊔ T₀) ⊔ (L₂ ⊔ T₀) : Subgroup G) : Set G),
      ∀ Q : Sylow 2 J, Nat.card ((Q : Subgroup J).map J.subtype) ≤ Nat.card U) :
    let I := (L₁ ⊔ T₀) ⊔ (L₂ ⊔ T₀)
    let D := (primeToResidual 3 H).map H.subtype ⊔ U
    D ∈ Chapter1.HOver G (I : Set G) ∧
      (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype = U) ∧
      (∀ J ∈ Chapter1.HOver G (D : Set G),
        ∃ Q : Sylow 2 J, (Q : Subgroup J).map J.subtype = U) ∧
      (∃ Q : Sylow 2 (normalizer (D.pCoreIn 2 : Set G)),
        (Q : Subgroup (normalizer (D.pCoreIn 2 : Set G))).map
          (normalizer (D.pCoreIn 2 : Set G)).subtype = U) := by
  let I := (L₁ ⊔ T₀) ⊔ (L₂ ⊔ T₀)
  let D := (primeToResidual 3 H).map H.subtype ⊔ U
  have hUH : U ≤ H := hP ▸ map_subtype_le _
  have hDH : D ≤ H := sup_le (map_subtype_le _) hUH
  have hID : I ≤ D :=
    (generated_factors_le_primeToResidual_join hL₁H hL₂H hperfect₁ hperfect₂ hq₁ hq₂).trans
      (sup_le_sup_left hT₀U _)
  have hd := HOver_and_sylow_of_intermediate hH P hP (show U ≤ D from le_sup_right) hDH hID
  have hstable := HOver_sylow_of_maximal_order (hP ▸ P.isPGroup'.map H.subtype)
    (show U ≤ D from le_sup_right) hID hmax
  exact ⟨hd.1,hd.2,hstable,hstable _ (core_normalizer_mem_HOver hd.1.1)⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
