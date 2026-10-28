module
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Intermediate
public import Theory.GroupTheory.NormalSymmetricThreeSupplement

/-!
# The unique escaping parabolic in a symmetric-three pair quotient

Above any Sylow two-subgroup, S₃×S₃ has exactly two strict proper
overgroups. Given one of them M, every Sylow overgroup escaping M
contains the other. Pulling back through a surjection whose kernel lies
in the original Sylow preserves this containment.

For a normal subgroup N with N/O₂(N)≅S₃ supplementing a proper Sylow
overgroup M with M/O₂(M)≅S₃, the other parabolic is N S. The quotient
calculation proves that N S is proper, so the escaping subgroup is
constructed rather than supplied as a hypothesis.

Source: Aschbacher–Smith 13.4.8(3), printed p.905. The source application
uses the literal Thompson span and component-normalizer intersection.
-/

public noncomputable section
open Subgroup
namespace SymmetricThreeProduct
private theorem coatom_of_strict_intermediate (S : Sylow 2 G) (A : Subgroup G)
    (hSA : (S : Subgroup G) < A) (hA : A ≠ ⊤) : IsCoatom A := by
  obtain ⟨B,hB,hAB⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  have ha := (intermediate_card_and_core (MulEquiv.refl G) S A hSA hA).1
  have hb := (intermediate_card_and_core (MulEquiv.refl G) S B
    (hSA.trans_le hAB) hB.ne_top).1
  exact (eq_of_le_of_card_ge hAB (by rw [ha,hb])).symm ▸ hB

theorem contains_other_parabolic_of_escape (S : Sylow 2 G) (M Q A : Subgroup G)
    (hSM : (S : Subgroup G) < M) (hM : M ≠ ⊤)
    (hSQ : (S : Subgroup G) < Q) (hQ : Q ≠ ⊤) (hne : M ≠ Q)
    (hSA : (S : Subgroup G) ≤ A) (hout : ¬ A ≤ M) : Q ≤ A := by
  by_cases ht : A = ⊤
  · rw [ht]; exact le_top
  have hSA' : (S : Subgroup G) < A := lt_of_le_of_ne hSA (by
    intro he; exact hout (he ▸ hSM.le))
  obtain ⟨P,R,_,_,hPR⟩ := exists_parabolics_over_sylow S
  have hm := (hPR M).mp ⟨coatom_of_strict_intermediate S M hSM hM,hSM.le⟩
  have hq := (hPR Q).mp ⟨coatom_of_strict_intermediate S Q hSQ hQ,hSQ.le⟩
  have ha := (hPR A).mp ⟨coatom_of_strict_intermediate S A hSA' ht,hSA⟩
  rcases hm with rfl | rfl <;> rcases hq with rfl | rfl <;>
    rcases ha with rfl | rfl <;> simp_all

end SymmetricThreeProduct

namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

theorem contains_other_sylow_overgroup_of_pair_quotient
    (f : H →* SymmetricThreeProduct.G) (hf : Function.Surjective f)
    (S : Sylow 2 H) (hker : f.ker ≤ S) (M Q A : Subgroup H)
    (hSM : (S : Subgroup H) < M) (hM : M ≠ ⊤)
    (hSQ : (S : Subgroup H) < Q) (hQ : Q ≠ ⊤) (hne : M ≠ Q)
    (hSA : (S : Subgroup H) ≤ A) (hout : ¬ A ≤ M) : Q ≤ A := by
  have reflect (X Y : Subgroup H) (hY : f.ker ≤ Y) (hXY : X.map f ≤ Y.map f) : X ≤ Y := by
    have hh := (map_le_iff_le_comap).mp hXY
    rwa [comap_map_eq,sup_eq_left.mpr hY] at hh
  have strict (X : Subgroup H) (hSX : (S : Subgroup H) < X) :
      (S : Subgroup H).map f < X.map f := by
    apply lt_of_le_of_ne (map_mono hSX.le)
    intro he
    exact hSX.not_ge (reflect X S hker he.symm.le)
  have proper (X : Subgroup H) (hSX : (S : Subgroup H) ≤ X) (hX : X ≠ ⊤) :
      X.map f ≠ ⊤ := by
    intro he
    apply hX
    apply top_unique
    apply reflect ⊤ X (hker.trans hSX)
    rw [he]
    exact le_top
  apply reflect Q A (hker.trans hSA)
  exact SymmetricThreeProduct.contains_other_parabolic_of_escape
    (S.mapSurjective hf) (M.map f) (Q.map f) (A.map f)
    (strict M hSM) (proper M hSM.le hM) (strict Q hSQ) (proper Q hSQ.le hQ)
    (fun he => hne (le_antisymm
      (reflect M Q (hker.trans hSQ.le) he.le)
      (reflect Q M (hker.trans hSM.le) he.symm.le)))
    (map_mono hSA) (fun he => hout (reflect A M (hker.trans hSM.le) he))


/-- A normal S₃ section selects the other parabolic above the original Sylow. -/
theorem normal_symmetricThree_supplement_controls_escape
    (eH : (H ⧸ pCore 2 H) ≃* SymmetricThreeProduct.G)
    (N M : Subgroup H) [N.Normal]
    (eN : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3))
    (eM : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 H) (hSM : (S : Subgroup H) ≤ M) (hM : M ≠ ⊤)
    (hgen : N ⊔ M = ⊤) :
    ¬ N ⊔ (S : Subgroup H) ≤ M ∧
      N ⊔ (S : Subgroup H) ≠ ⊤ ∧
      ∀ A : Subgroup H, (S : Subgroup H) ≤ A → ¬ A ≤ M →
        N ⊔ (S : Subgroup H) ≤ A := by
  have hNM : ¬ N ≤ M := by
    intro hh
    exact hM (top_unique (hgen ▸ sup_le hh le_rfl))
  have hQM : ¬ N ⊔ (S : Subgroup H) ≤ M := fun hh => hNM (le_sup_left.trans hh)
  have hMstrict : (S : Subgroup H) < M := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨hSM,?_⟩
    intro hh
    have hp : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
      ((S.isPGroup'.to_le hh).to_quotient (pCore 2 M)).of_equiv eM
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hthree : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hn] at hthree
    exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)
  have hQ : N ⊔ (S : Subgroup H) ≠ ⊤ := by
    intro hh
    obtain ⟨e⟩ := NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement
      N S eN S.isPGroup' hh
    have hc := Nat.card_congr (eH.symm.trans e).toEquiv
    rw [SymmetricThreeProduct.card_group] at hc
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hc
  have hQstrict : (S : Subgroup H) < N ⊔ (S : Subgroup H) :=
    lt_iff_le_not_ge.mpr ⟨le_sup_right,fun hh => hQM (hh.trans hSM)⟩
  refine ⟨hQM,hQ,?_⟩
  intro A hSA hout
  let f := eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ S := by
    rw [MonoidHom.ker_comp_of_injective _ _ eH.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  exact contains_other_sylow_overgroup_of_pair_quotient f hf S hk M _ A
    hMstrict hM hQstrict hQ (fun he => hQM he.symm.le) hSA hout

end Theory.GroupTheory
