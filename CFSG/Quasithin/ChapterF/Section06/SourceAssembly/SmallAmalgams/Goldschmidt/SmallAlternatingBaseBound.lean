module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalAlternatingCore
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualAction
public import Theory.GroupTheory.Amalgam.ParabolicRecognition
public import Theory.SpecificGroups.SymmetricFour.BinaryPairBound

/-!
# Bounding the original overlap from two alternating-four residuals

The original overlap acts faithfully on the pair of local two-residuals:
an element in both kernels centralizes the ambient residual and therefore
vanishes by the common-core condition. For A4 residuals these actions take
values in S4. A crossing involution in the first residual four-group maps to
a transposition under the second action. The first kernel centralizes it,
and the finite two-action bound gives order at most 32.

This is the large-overlap consequence of Goldschmidt (1980), (4.2), retaining
the original overlap. The crossing premise is supplied by
`SmallResidualCrossing`; it is discharged in `SmallAlternatingBase`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

private theorem core_preimage_le {A : Type*} [Group A] [Finite A]
    (φ : A →* Four) (hi : Function.Injective (φ.comp (pResidual 2 A).subtype)) :
    core.comap φ ≤ pCore 2 A := by
  have hk : IsPGroup 2 φ.ker := by
    let q := (QuotientGroup.mk' (pResidual 2 A)).comp φ.ker.subtype
    apply (isPGroup_quotient_pResidual (G := A) 2).of_injective q
    apply q.ker_eq_bot_iff.mp
    apply bot_unique
    intro k hk
    have hkR : (k : A) ∈ pResidual 2 A := (QuotientGroup.eq_one_iff _).mp hk
    have he := hi (a₁ := ⟨k, hkR⟩) (a₂ := 1) (by
      change φ (k : A) = φ 1
      simpa only [map_one] using (MonoidHom.mem_ker.mp k.property))
    exact Subtype.ext (congrArg (fun r : pResidual 2 A => (r : A)) he)
  exact le_sSup ⟨inferInstance,
    (IsElementaryAbelian.isPGroup 2 core).comap_of_ker_isPGroup φ hk⟩

variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem pair_action_injective (h : CubicTreeAction F)
    (φ₀ : F false →* Four) (φ₁ : F true →* Four)
    (hk₀ : φ₀.ker = centralizer ((pResidual 2 (F false) : Subgroup (F false)) : Set _))
    (hk₁ : φ₁.ker = centralizer ((pResidual 2 (F true) : Subgroup (F true)) : Set _)) :
    Function.Injective
      ((φ₀.comp (inclusion (show F false ⊓ F true ≤ F false from inf_le_left))).prod
        (φ₁.comp (inclusion (show F false ⊓ F true ≤ F true from inf_le_right)))) := by
  let T := F false ⊓ F true
  let l : T →* F false := inclusion inf_le_left
  let r : T →* F true := inclusion inf_le_right
  let ρ := (φ₀.comp l).prod (φ₁.comp r)
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro t ht
  have ht₀ : l t ∈ centralizer
      ((pResidual 2 (F false) : Subgroup (F false)) : Set _) := by
    rw [← hk₀]
    exact congrArg Prod.fst ht
  have ht₁ : r t ∈ centralizer
      ((pResidual 2 (F true) : Subgroup (F true)) : Set _) := by
    rw [← hk₁]
    exact congrArg Prod.snd ht
  have hn : pResidual 2 G ≤ centralizer ({(t : G)} : Set G) := by
    rw [h.residual_source.1]
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg (fun z : F false => (z : G)) (ht₀ x hx))
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg (fun z : F true => (z : G)) (ht₁ x hx))
  have htC : (t : G) ∈ centralizer ((pResidual 2 G : Subgroup G) : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hn hx)
  have he := (centralizer_inf_eq_bot_of_normal_supplement (pResidual 2 G) T
    h.residual_source.2.2 h.common_core_eq_bot).le ⟨htC, t.property⟩
  exact Subtype.ext he

private theorem crossing_element (h : CubicTreeAction F)
    (e₀ : pResidual 2 (F false) ≃* alternatingGroup (Fin 4))
    (φ₀ : F false →* Four) (φ₁ : F true →* Four)
    (hk₀ : φ₀.ker = centralizer ((pResidual 2 (F false) : Subgroup (F false)) : Set _))
    (hi₁ : Function.Injective (φ₁.comp (pResidual 2 (F true)).subtype))
    (hcross : ¬ ((pResidual 2 (F false)).pCoreIn 2).map (F false).subtype ≤
      (F true).pCoreIn 2) :
    let l : (F false ⊓ F true : Subgroup G) →* F false := inclusion inf_le_left
    let r : (F false ⊓ F true : Subgroup G) →* F true := inclusion inf_le_right
    ∃ t : (F false ⊓ F true : Subgroup G), t ^ 2 = 1 ∧
      φ₁ (r t) ∉ core ∧ (φ₀.comp l).ker ≤ centralizer ({t} : Set _) := by
  let : Finite (F true) := h.finite true
  let V := (pResidual 2 (F false)).pCoreIn 2
  have hVp : IsPGroup 2 V := isPGroup_pCoreIn 2 _
  have hVN : V.Normal := by dsimp [V, pCoreIn]; infer_instance
  let := hVN
  have hVQ : V ≤ pCore 2 (F false) := le_sSup ⟨hVN, hVp⟩
  obtain ⟨P, hP⟩ := h.primitive.sylow.left_sylow
  have hVP : V ≤ (inclusionAmalgam (F false) (F true)).left.range :=
    hP ▸ hVQ.trans (pCore_isPGroup.le_sylow_of_normal P)
  obtain ⟨v, hv, hvout⟩ := Set.not_subset.mp hcross
  obtain ⟨v, hvV, rfl⟩ := hv
  obtain ⟨t, ht⟩ := hVP hvV
  have hvt : (t : G) = (v : G) := congrArg (fun x : F false => (x : G)) ht
  have hVe := (alternating_residual_core_split e₀).2.2.1
  let := hVe
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [coe_pow, hvt]
    exact congrArg (fun x : F false => (x : G))
      (elemPow_eq_one_of_isElementaryAbelian v hvV)
  refine ⟨t, ht2, ?_, ?_⟩
  · intro hmem
    have hqt := core_preimage_le φ₁ hi₁ hmem
    apply hvout
    exact ⟨⟨t, t.property.2⟩, hqt, hvt⟩
  · intro k hk
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hkC : (inclusion (show F false ⊓ F true ≤ F false from inf_le_left)) k ∈
        centralizer ((pResidual 2 (F false) : Subgroup (F false)) : Set _) :=
      hk₀ ▸ hk
    have hvR := pCoreIn_le 2 (pResidual 2 (F false)) hvV
    have hc := congrArg (fun x : F false => (x : G)) (hkC v hvR)
    change (v : G) * (k : G) = (k : G) * (v : G) at hc
    simpa only [coe_mul, hvt] using hc.symm

/-- The literal crossing four-group bounds the original edge stabilizer. -/
theorem CubicTreeAction.overlap_card_le_thirtyTwo_of_alternating_crossing
    (h : CubicTreeAction F)
    (e₀ : pResidual 2 (F false) ≃* alternatingGroup (Fin 4))
    (e₁ : pResidual 2 (F true) ≃* alternatingGroup (Fin 4))
    (hcross : ¬ ((pResidual 2 (F false)).pCoreIn 2).map (F false).subtype ≤
      (F true).pCoreIn 2) :
    Nat.card (F false ⊓ F true : Subgroup G) ≤ 32 := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  let : Finite (F false ⊓ F true : Subgroup G) :=
    Finite.of_injective (inclusion (show F false ⊓ F true ≤ F false from inf_le_left))
      (inclusion_injective inf_le_left)
  obtain ⟨φ₀, _, hk₀, _, _⟩ := alternating_residual_action e₀
  obtain ⟨φ₁, _, hk₁, _, hi₁⟩ := alternating_residual_action e₁
  obtain ⟨t, ht, ho, hc⟩ := crossing_element h e₀ φ₀ φ₁ hk₀ hi₁ hcross
  exact Theory.SpecificGroups.SymmetricFour.BinaryPairBound.card_le_thirtyTwo h.primitive.sylow.isPGroup
    (φ₀.comp (inclusion inf_le_left)) (φ₁.comp (inclusion inf_le_right))
    (pair_action_injective h φ₀ φ₁ hk₀ hk₁) t ht ho hc

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
