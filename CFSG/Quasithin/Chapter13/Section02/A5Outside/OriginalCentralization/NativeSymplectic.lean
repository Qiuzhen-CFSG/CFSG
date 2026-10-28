module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalF11
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairNativeSymplecticCores

/-!
# Excluding the actual native symplectic comparison in the commuting pair

Native restoration makes both whole original join-cores elementary.
Commutation places each natural module in the opposite core. Since both
cores are abelian, their Sylow-centralizer descriptions give mutual
containment. The resulting nontrivial common core is normalized by both
original local groups, contradicting the original unique two-local bound.

No quotient action is supplied, no core order is bounded, and no Borel is
assumed to normalize the Sylow. The input comparison is the actual native
symplectic amalgam, with its whole overlap and endpoint inclusions.
Source: Aschbacher--Smith 13.2.8(1), p.880, 1.2.7, pp.506--507,
and F.1.12(I)(2), pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The literal original commuting pair cannot have a native symplectic
reduced comparison, in either point/plane orientation. -/
theorem original_pair_not_reduced_symplectic
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hVW : V ≤ centralizer (W : Set G))
    (h : HypothesisF11 ![L,K] (T : Subgroup G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (point : Bool)
    (c : Iso (reducedAmalgam ![L,K] (T : Subgroup G))
      (SymplecticNative.amalgam F point)) : False := by
  have a : ∀ i, Nonempty ((![L,K] i ⧸ pCore 2 (![L,K] i)) ≃*
      alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact ⟨d.quotient⟩
    · exact ⟨e.quotient⟩
  obtain ⟨_,hEA⟩ := A5PairCatalogue.NativeSymplecticCores.join_cores_and_elementary
    F h a hF hn point c
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := H.pCoreIn 2
  let : IsElementaryAbelian 2 Q := hEA 0
  let : IsElementaryAbelian 2 P := by
    have hh := hEA 1
    change IsElementaryAbelian 2 ((K ⊔ (T : Subgroup G)).pCoreIn 2) at hh
    rwa [hjoin] at hh
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hPT : P ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hVP : V ≤ P := by
    change V ≤ H.pCoreIn 2
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf d.chosen.le_sylow hVW
  have hWQ : W ≤ Q := by
    change W ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←d.sylow_centralizer d.normalizes_L]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  have hQP : Q ≤ P := by
    change Q ≤ H.pCoreIn 2
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf hQT ((le_centralizer Q).trans (centralizer_le hWQ))
  have hPQ : P ≤ Q := by
    change P ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←d.sylow_centralizer d.normalizes_L]
    exact le_inf hPT ((le_centralizer P).trans (centralizer_le hVP))
  have heq : Q = P := le_antisymm hQP hPQ
  have hQne : Q ≠ ⊥ := fun hz =>
    d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans_eq hz))
  have hQN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) hQne hQN
  have hHN : H ≤ normalizer (Q : Set G) := by
    rw [heq]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  exact hH.1.2 (hHN.trans hN)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
