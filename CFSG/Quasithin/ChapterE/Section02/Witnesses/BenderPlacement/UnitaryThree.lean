module
public import Theory.SpecificGroups.SU3.NormalElementaryPlacement
public import Theory.SpecificGroups.SU3.TwoConjugateWitness.Witness
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearTwo.Source
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Placement and the original unitary normal-Bender witness

Normality of the elementary V in T forces each of its root displacements
inside K to have square one. The concrete Hermitian coordinate calculation
excludes every outer involution with this property. The faithful normal
supplement therefore contains V, whose Sylow intersection has omega equal
to its center. The central-root SL₂ pair is then transported through the
original inclusion K → H, with the original maximal subgroup's exact Borel
intersection supplied by the normal-Bender source theorem.

Source: Aschbacher–Smith E.2.7, printed p.218, normal unitary Bender case.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H] {E : Type} [Field E] [Finite E]
private instance : Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

/-- Normality in T forces the required placement; the resulting Pair uses
exactly the original unique maximal subgroup. No placement input remains. -/
theorem source_unitary (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀x : E, J.conj x = x^(2^n))
    (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) (hrank : 1 < primeRank 2 V) :
    V ≤ K ∧ (∃ S : Sylow 2 K,
      (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype) ∧
    Nonempty (LinearTwo.Witness T (ChapterB.minimalParabolicMax T hP) V n) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa [Nat.card_eq_fintype_card,pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨hVK,S,hS,hVZ⟩ := HermitianForm.SylowQuadraticInner.normal_elementary_placement
    J hJ hn hcard hconj K e T hgen hcore V hVT hvn
  let M := ChapterB.minimalParabolicMax T hP
  have hMK : M.subgroupOf K = normalizer (S : Set K) := by
    have h := (Structure.source_normal_bender_conclusions T hP K hgen
      (.unitary n hn ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨e⟩⟩)).1
    rw [←hS] at h
    exact h
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let W := (V.subgroupOf K).map e.toMonoidHom
  have hWZ : W ≤ (center Q).map (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype := by
    have hh := map_mono (f := e.toMonoidHom) hVZ
    rw [map_embeddedCenter (S : Subgroup K) e.toMonoidHom e.injective] at hh
    exact hh
  have hVc : 4 ≤ Nat.card V := by
    by_contra hh
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hle : Nat.card V ≤ 2 := by
      have hp : 2^a < 4 := ha ▸ Nat.lt_of_not_ge hh
      have hn : a ≤ 1 := by
        by_contra h
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a)
        norm_num at hh
        omega
      rw [ha]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans_eq (by norm_num)
    have hr := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 1) V
      (by simpa only [pow_one] using hle)
    omega
  have hWc : 4 ≤ Nat.card W := by
    change 4 ≤ Nat.card ((V.subgroupOf K).map e.toMonoidHom)
    rw [card_map_of_injective (f := e.toMonoidHom) e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
    exact hVc
  obtain ⟨w⟩ := HermitianForm.TwoConjugateWitness.exists_unitary_witness
    J hJ hn hcard hfixed Q W hWZ hWc
  let f : ProjectiveSpecialUnitaryMatrixGroup J →* H := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hTf : (T : Subgroup H).comap f = Q := by
    change ((T : Subgroup H).subgroupOf K).comap e.symm.toMonoidHom = _
    rw [←hS]
    exact comap_equiv_eq_map_symm e.symm (S : Subgroup K)
  have hMf : M.comap f = normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    change (M.subgroupOf K).comap e.symm.toMonoidHom = _
    rw [hMK]
    change (normalizer ((S : Subgroup K) : Set K)).comap e.symm.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (f := e.symm.toMonoidHom) (S : Subgroup K) e.symm.surjective]
    have heS : (S : Subgroup K).comap e.symm.toMonoidHom = (Q : Subgroup _) :=
      comap_equiv_eq_map_symm e.symm (S : Subgroup K)
    rw [heS]
    rfl
  have hWV : W.map f = V := by
    change ((V.subgroupOf K).map e.toMonoidHom).map f = _
    rw [Subgroup.map_map]
    have he : f.comp e.toMonoidHom = K.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [he,map_subgroupOf_eq_of_le hVK]
  have result := w.map f hf (T : Subgroup H) M hTf hMf
  rw [hWV] at result
  exact ⟨hVK,⟨S,hS,hVZ⟩,⟨LinearTwo.of_model_witness result⟩⟩

/-- The stored PSU model may use an arbitrary Hermitian form; its actual
basis-change equivalence discharges the standard-coordinate hypothesis. -/
theorem source_unitary_of_isPSU (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU K 3 (2^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) (hrank : 1 < primeRank 2 V) :
    V ≤ K ∧ (∃ S : Sylow 2 K,
      (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype) ∧
    Nonempty (LinearTwo.Witness T (ChapterB.minimalParabolicMax T hP) V n) := by
  obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := hmodel
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨d⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hfixed
  exact source_unitary T hP K hgen hcore
    (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
    rfl hn hcard hconj (e.trans d) V hVT hvn hrank

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
