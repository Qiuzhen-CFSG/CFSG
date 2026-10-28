module

public import Glauberman.DicksonClassification
public import Theory.SpecificGroups.PSL2.SylowIntersections
public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Binary rank-one subgroup recognition

A subgroup of binary PSL₂ with trivial two-core and a Sylow subgroup of order
at least four is SL₂ over a binary field of degree k > 1 dividing the ambient
degree. Dickson's self-normalizing Sylow case excludes a small normalizer;
the large-normalizer theorem then leaves the subfield models. The affine case
has trivial normal elementary subgroup and would be cyclic. In characteristic
two, SL₂, PSL₂ and PGL₂ have the same matrix model up to the canonical maps.

Source: Huppert II.8.23 and II.8.26, applied in Aschbacher–Smith E.2.7,
combined manuscript (1 March 2004), printed p.218.
-/

@[expose] public section

open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.TwoConjugateWitness

noncomputable def slEquivPSL (F : Type*) [Field F] [CharP F 2] :
    SL(2,F) ≃* PSL(2,F) :=
  MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩

noncomputable def pslEquivPGL (F : Type*) [Field F] [Finite F] [CharP F 2] :
    PSL(2,F) ≃* Matrix.ProjGenLinGroup (Fin 2) F :=
  MulEquiv.ofBijective ProjectiveSpecialLinearGroup.toPGL
    ⟨ProjectiveSpecialLinearGroup.toPGL_injective,
      ProjectiveSpecialLinearGroup.toPGL_surj_of_roots (by
        intro a
        obtain ⟨b,hb⟩ := isSquare_of_charTwo' (a : F)
        have hb0 : b ≠ 0 := by intro h; simp [h] at hb
        refine ⟨Units.mk0 b hb0, ?_⟩
        apply Units.ext
        simpa [pow_two] using hb.symm)⟩

theorem psl_subgroup_recognition {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2^n) (H : Subgroup PSL(2,F))
    (hc : pCore 2 H = ⊥) (P : Sylow 2 H) (hP : 4 ≤ Nat.card P) :
    ∃ k : ℕ, 1 < k ∧ k ∣ n ∧ Nonempty (H ≃* SL(2,GaloisField 2 k)) := by
  have hnp : ¬ IsPGroup 2 H := by
    intro hp
    have ht : (⊤ : Subgroup H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    rw [hc] at ht
    have he : (P : Subgroup H) = ⊥ := le_bot_iff.mp (le_top.trans ht)
    have hp1 : Nat.card P = 1 := by
      rw [he]
      simp
    omega
  obtain ⟨r,hr⟩ := P.isPGroup'.exists_card_eq
  have hnorm : normalizer (P : Set H) ≠ (P : Subgroup H) := by
    intro he
    rcases Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
        hF H P hr (by omega) he with h | h | h
    · let := h.2
      exact hnp (IsElementaryAbelian.isPGroup 2 H)
    · omega
    · omega
  have hfinish (k : ℕ) (hk : k ≠ 0) (hkn : k ∣ n)
      (e : H ≃* SL(2,GaloisField 2 k)) :
      ∃ k : ℕ, 1 < k ∧ k ∣ n ∧ Nonempty (H ≃* SL(2,GaloisField 2 k)) := by
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hec : Nat.card P = Nat.card Q :=
      Nat.card_congr (Subgroup.equivMapOfInjective (P : Subgroup H)
        e.toMonoidHom e.injective).toEquiv
    have hQc : Nat.card Q = 2^k := by
      rw [← Nat.card_congr (sylowEquivAdditive (GaloisField 2 k) 2 Q).toEquiv]
      exact GaloisField.card 2 k hk
    refine ⟨k, ?_, hkn, ⟨e⟩⟩
    rw [hec,hQc] at hP
    by_contra hh
    have : k = 1 := by omega
    simp [this] at hP
  rcases Glauberman.Dickson.huppert_II_8_26_dickson_case_p_part_normalizer_large
      hF H P (by
        change Nat.card P ≠ 1
        omega) hnorm with h | h | h | h
  · obtain ⟨m,t,ht,_,N,C,hN,hNe,hNc,hC,hCc,_,hNC⟩ := h
    let := hN
    let := hNe
    have hNb : N = ⊥ := le_bot_iff.mp (hc ▸
      (show N ≤ pCore 2 H from le_sSup ⟨hN, IsElementaryAbelian.isPGroup 2 N⟩))
    have hCt : C = ⊤ := by simpa [hNb] using hNC
    have hCyc : IsCyclic H := by
      let := hC
      exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom.comp
        (MulEquiv.subgroupCongr hCt).toMonoidHom)
        (Subgroup.topEquiv.surjective.comp (MulEquiv.subgroupCongr hCt).surjective)
    let := hCyc
    have hPN : (P : Subgroup H).Normal := inferInstance
    have hPb : (P : Subgroup H) ≤ pCore 2 H := le_sSup ⟨hPN,P.isPGroup'⟩
    have he : (P : Subgroup H) = ⊥ := le_bot_iff.mp (hc ▸ hPb)
    have : Nat.card P = 1 := by rw [show Nat.card P = Nat.card (P : Subgroup H) from rfl,he]; simp
    omega
  · obtain ⟨m,hm,_⟩ := h
    cases m with
    | zero => norm_num at hm
    | succ m => rw [pow_succ] at hm; omega
  · obtain ⟨k,hk,hd,⟨e⟩⟩ := h
    exact hfinish k hk (dvd_trans (dvd_mul_left k 2) hd)
      ((e.trans (pslEquivPGL (GaloisField 2 k)).symm).trans
        (slEquivPSL (GaloisField 2 k)).symm)
  · obtain ⟨k,hk,hd,⟨e⟩⟩ := h
    exact hfinish k hk hd (e.trans (slEquivPSL (GaloisField 2 k)).symm)
/-- The same recognition on the literal determinant-one matrix subgroup. -/
theorem sl_subgroup_recognition {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (I : Subgroup SL(2,F))
    (hc : pCore 2 I = ⊥) (P : Sylow 2 I) (hP : 4 ≤ Nat.card P) :
    ∃ k : ℕ, 1 < k ∧ k ∣ n ∧ Nonempty (I ≃* SL(2,GaloisField 2 k)) := by
  let f := slEquivPSL F
  let H := I.map f.toMonoidHom
  let e : I ≃* H := I.equivMapOfInjective f.toMonoidHom f.injective
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcore : pCore 2 H = ⊥ := by rw [← pCore_map_iso 2 e, hc, Subgroup.map_bot]
  have hcard : 4 ≤ Nat.card Q := by
    have hec : Nat.card P = Nat.card Q := Nat.card_congr
      (Subgroup.equivMapOfInjective (P : Subgroup I) e.toMonoidHom e.injective).toEquiv
    omega
  obtain ⟨k,hk,hd,⟨d⟩⟩ := psl_subgroup_recognition hF H hcore Q hcard
  exact ⟨k,hk,hd,⟨e.trans d⟩⟩

end Matrix.SpecialLinearGroup.TwoConjugateWitness
