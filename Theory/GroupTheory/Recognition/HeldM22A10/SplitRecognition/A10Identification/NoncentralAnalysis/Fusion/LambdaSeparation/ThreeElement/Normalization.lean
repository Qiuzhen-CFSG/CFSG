module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.Core

/-!
# Order-three normalizers preserve Held's S

The elementary-sixteen catalogue leaves only S and L₁ inside W. An
order-three conjugation cannot exchange just two subgroups, so every element
of order three normalizing W also normalizes S. Together with the unique
nonidentity square of W this supplies both required properties of the
order-three witness once its existence is established.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226. This uses the catalogue
to obtain exactly the normalization needed for the odd-order witness.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- An order-three normalizer of W preserves S, because W has only two elementary sixteens. -/
public theorem lambdaCore_three_normalizes_S (x : G) (hx : orderOf x = 3)
    (hn : x ∈ normalizer (lambdaCore D e : Set G)) : x ∈ sNormalizer D e := by
  let a := MulAut.conj x
  let F (A : Subgroup G) := A.map a.toMonoidHom
  have hi : Function.Injective F := map_injective a.injective
  have ha3 : a ^ 3 = 1 := by
    dsimp [a]
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hF3 (A : Subgroup G) : F (F (F A)) = A := by
    dsimp only [F]
    rw [map_map, map_map]
    have hc : (a.toMonoidHom.comp a.toMonoidHom).comp a.toMonoidHom = MonoidHom.id G := by
      ext g
      change a (a (a g)) = g
      have hh := congrArg (fun b : MulAut G => b g) ha3
      simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using hh
    rw [hc, map_id]
  have hW : F (lambdaCore D e) = lambdaCore D e :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hFle {A : Subgroup G} (hA : A ≤ lambdaCore D e) : F A ≤ lambdaCore D e :=
    (map_mono hA).trans hW.le
  let S := ambientElementary D e 1
  let B := F S
  have hS : IsElementaryAbelian 2 S := ambientElementary_isElementaryAbelian D e 1
  let := hS
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map a.toMonoidHom
  have hcB : Nat.card B = 16 := by
    rw [card_map_of_injective a.injective, ambientElementary_card]
  have hBW : B ≤ lambdaCore D e := hFle (ambientS_le_lambdaCore D e)
  have hBS : B = S := by
    rcases lambdaCore_elementary_sixteen D e B hBW hB hcB with h1 | h1
    · exact h1
    · have hFB : IsElementaryAbelian 2 (F B) := by
        let := hB
        exact IsElementaryAbelian.map a.toMonoidHom
      have hcFB : Nat.card (F B) = 16 := by
        rw [card_map_of_injective a.injective, hcB]
      rcases lambdaCore_elementary_sixteen D e (F B) (hFle hBW) hFB hcFB with h2 | h2
      · have ht := hF3 S
        change F (F B) = S at ht
        change F B = S at h2
        rwa [h2] at ht
      · exact hi (h2.trans h1.symm)
  exact mem_normalizer_iff_map_conj_eq.mpr hBS

/-- Transfer an order-three W-normalizer to precisely the witness used by NormalizerAction. -/
public theorem lambda_three_element_of_core_three
    (h : ∃ x : normalizer (lambdaCore D e : Set G), orderOf x = 3) :
    ∃ x : sNormalizer D e, orderOf x = 3 ∧
      Commute (x : G) (D.a10ModelEmbedding e (pi * mu)) := by
  obtain ⟨x, hx⟩ := h
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  exact ⟨⟨x, lambdaCore_three_normalizes_S D e x hxG x.property⟩,
    (orderOf_coe _).symm.trans hxG,
    mem_centralizer_singleton_iff.mp (lambdaCore_normalizer_le_centralizer D e x.property)⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
