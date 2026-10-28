module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InnerCase

/-!
# The inner/inner action case

An element of the pair normalizer whose actions on both factors are inner
acts on KKˣ exactly as a product of the two inner representatives. The
proved faithfulness of the full pair action identifies the original element
with that product. The diagonal nonfusion calculation then puts each such
conjugate of t into one of the two factors. All action maps are the literal
normalizer conjugation homomorphisms.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.566.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

/-- A pair normalizer element with inner actions on both factors belongs
to the actual product, by faithfulness of conjugation on that product. -/
theorem inner_actions_mem_pair (d : Incoming κ G p) {i : G}
    (hiM : i ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G))
    (hiK : i ∈ normalizer (d.K : Set G))
    (hiL : i ∈ normalizer (conjugate d.K d.x : Set G))
    (hinnerK : d.K.normalizerMonoidHom ⟨i, hiK⟩ ∈ (MulAut.conj : d.K →* MulAut d.K).range)
    (hinnerL : (conjugate d.K d.x).normalizerMonoidHom ⟨i, hiL⟩ ∈
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range) :
    i ∈ d.K ⊔ conjugate d.K d.x := by
  let L := conjugate d.K d.x
  let P := d.K ⊔ L
  obtain ⟨k, hk⟩ := hinnerK
  obtain ⟨l, hl⟩ := hinnerL
  let f := (MulAut.conj i).toMonoidHom
  let f' := (MulAut.conj ((k : G) * (l : G))).toMonoidHom
  have hKL : P ≤ f.eqLocus f' := by
    apply sup_le
    · intro a ha
      have hki := congrArg (fun aK : MulAut d.K => (aK ⟨a, ha⟩ : G)) hk
      change (k : G) * a * (k : G)⁻¹ = i * a * i⁻¹ at hki
      have hla : Commute (l : G) a :=
        commutator_eq_bot_iff_le_centralizer.mp d.commuting ha l l.property
      change i * a * i⁻¹ = ((k : G) * (l : G)) * a * ((k : G) * (l : G))⁻¹
      calc
        _ = (k : G) * a * (k : G)⁻¹ := hki.symm
        _ = (k : G) * ((l : G) * a * (l : G)⁻¹) * (k : G)⁻¹ := by
          rw [hla.eq, mul_inv_cancel_right]
        _ = _ := by group
    · intro a ha
      have hli := congrArg (fun aL : MulAut L => (aL ⟨a, ha⟩ : G)) hl
      change (l : G) * a * (l : G)⁻¹ = i * a * i⁻¹ at hli
      have hka : Commute (k : G) a :=
        (commutator_eq_bot_iff_le_centralizer.mp d.commuting k.property a ha).symm
      have hkl : Commute (k : G) (l : G) :=
        (commutator_eq_bot_iff_le_centralizer.mp d.commuting k.property l l.property).symm
      change i * a * i⁻¹ = ((k : G) * (l : G)) * a * ((k : G) * (l : G))⁻¹
      calc
        _ = (l : G) * a * (l : G)⁻¹ := hli.symm
        _ = (l : G) * ((k : G) * a * (k : G)⁻¹) * (l : G)⁻¹ := by
          rw [hka.eq, mul_inv_cancel_right]
        _ = ((l : G) * (k : G)) * a * ((l : G) * (k : G))⁻¹ := by group
        _ = _ := by rw [hkl.eq]
  have hklP : (k : G) * (l : G) ∈ P := mul_mem_sup k.property l.property
  have he : P.normalizerMonoidHom ⟨i, hiM⟩ =
      P.normalizerMonoidHom ⟨(k : G) * (l : G), P.le_normalizer hklP⟩ := by
    ext a
    exact hKL a.property
  have hi := d.normalizer_action_injective he
  have hi' : i = (k : G) * (l : G) := congrArg Subtype.val hi
  exact hi' ▸ hklP

/-- This closes the inner/inner part of the marked-conjugate case split. -/
theorem class_exclusion_of_inner_actions (d : Incoming κ G p) {i : G}
    (hi : IsConj d.t i)
    (hiM : i ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G))
    (hiK : i ∈ normalizer (d.K : Set G))
    (hiL : i ∈ normalizer (conjugate d.K d.x : Set G))
    (hinnerK : d.K.normalizerMonoidHom ⟨i, hiK⟩ ∈ (MulAut.conj : d.K →* MulAut d.K).range)
    (hinnerL : (conjugate d.K d.x).normalizerMonoidHom ⟨i, hiL⟩ ∈
      (MulAut.conj : conjugate d.K d.x →* MulAut (conjugate d.K d.x)).range) :
    i ∈ (d.K : Set G) ∪ conjugate d.K d.x :=
  d.class_exclusion_in_pair hi (d.inner_actions_mem_pair hiM hiK hiL hinnerK hinnerL)

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
