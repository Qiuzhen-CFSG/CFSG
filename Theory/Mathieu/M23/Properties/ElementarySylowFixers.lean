module

public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.Properties.Order

/-!
# Elementary pointwise Sylow fixers of M₂₃

The actual M₂₂ point stabilizer has odd index 23 in M₂₃. Its Sylow
two-subgroup is therefore Sylow in M₂₃, and the checked M₂₂ center bound
transfers along the literal embedding. All M₂₃ automorphisms are inner,
so an elementary abelian group fixing a Sylow subgroup has order at most two.

Source: Aschbacher–Smith, 1.1.5(3)(f), pp.501–503, and the exclusion
in the proof of 13.6.6, p.927. The point-stabilizer comparison uses the
imported native Witt-design models, without an abstract family identification.
-/

public section
open Subgroup
namespace Sporadic.Mathieu

theorem m23_sylow_center_card_le_two (S : Sylow 2 M23) : Nat.card (center S) ≤ 2 := by
  let P := M22EvenGeometry.sylow
  let f : M22 →* M23 :=
    (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
      m23EquivM22PointStabilizer.toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp m23EquivM22PointStabilizer.injective
  let U : Subgroup M23 := (P : Subgroup M22).map f
  obtain ⟨T, hUT⟩ := (P.isPGroup'.map f).exists_le_sylow
  have hU : Nat.card U = 128 := by
    rw [card_map_of_injective hf]
    exact M22EvenGeometry.sylow_card
  have hT : Nat.card T = 128 := by
    rw [T.card_eq_multiplicity, m23_order]
    decide +kernel
  have he : U = (T : Subgroup M23) :=
    eq_of_le_of_card_ge hUT (by rw [hU]; exact hT.le)
  let e : P ≃* T := ((P : Subgroup M22).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr he)
  rw [Nat.card_congr (centerCongr ((S.equiv T).trans e.symm)).toEquiv]
  exact m22_sylow_center_card_le_two P

theorem m23_sylow_center_isCyclic (S : Sylow 2 M23) : IsCyclic (center S) :=
by
  apply isCyclic_of_card_dvd_prime (p := 2)
  have h := m23_sylow_center_card_le_two S
  have hp := Nat.card_pos (α := center S)
  have hc : Nat.card (center S) = 1 ∨ Nat.card (center S) = 2 := by omega
  rcases hc with hc | hc <;> simp [hc]

theorem m23_elementary_sylow_fixer_card_le_two (hZ : center M23 = ⊥)
    (S : Sylow 2 M23) (A : Subgroup (MulAut M23)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let _ := m23_sylow_center_isCyclic S
  apply Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner S hZ _ A hfix
  intro a _ _
  obtain ⟨g, hg⟩ := m23_conj_surjective a
  exact ⟨g, hg.symm⟩

end Sporadic.Mathieu
