module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairNativeLinearCores

/-!
# Excluding the native linear row for an original commuting pair

The actual reduced linear comparison makes the full original first join
core elementary. A commuting opposite chosen module lies in that core,
so the core centralizes it and lies in the opposite core. This contradicts
the proved incomparability of the two original cores. No normalized Borel,
field bound, residual lift, or additional marking callback is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The literal native linear comparison is impossible for an original
commuting pair, in either orientation and every positive binary degree. -/
theorem original_commuting_pair_not_native_linear
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (hVW : V ≤ centralizer (W : Set G))
    (h : HypothesisF11 ![L,K] (T : Subgroup G))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (c : Iso (reducedAmalgam ![L,K] (T : Subgroup G)) (LinearNative.amalgam F b)) :
    False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have a : ∀ i, Nonempty ((![L,K] i ⧸ pCore 2 (![L,K] i)) ≃*
      alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact ⟨d.quotient⟩
    · exact ⟨e.quotient⟩
  let : IsElementaryAbelian 2 Q :=
    A5PairNativeLinear.linear_join_cores_elementary h a F hF hn b c 0
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  have hQC : Q ≤ centralizer (W : Set G) :=
    (le_centralizer Q).trans (centralizer_le hWQ)
  apply (original_pair_cores_incomparable d hH hd q hq hk).2
  rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
  exact le_inf ((d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left) hQC

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
