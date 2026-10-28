module

public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PGroup.Omega

/-!
# Maximal two-locals from elementary abelian normalizers

If M = N_G(Q) is maximal two-local, the nontrivial characteristic subgroup
Ω₁(Z(Q)) is elementary abelian and its ambient normalizer contains M.
Maximality therefore identifies this normalizer with M. Sylow conjugacy
then places the elementary subgroup inside any fixed Sylow two-subgroup.

Thus coverage of the elementary-abelian normalizers in one Sylow subgroup
suffices to cover every maximal two-local. The final lemma keeps the actual
conjugating elements and only requires inclusion in the covering groups.

Source: the definition of two-local subgroups in Aschbacher–Smith,
*The Classification of Quasithin Groups*, §0.1, printed pp.3–4, and the
standard characteristic-center reduction for finite p-groups.
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupTheory

/-- Every maximal two-local is the full normalizer of a nontrivial elementary
abelian two-subgroup. -/
public theorem exists_elementary_normalizer_of_isMaximalTwoLocal
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ IsElementaryAbelian 2 A ∧
      M = normalizer (A : Set G) := by
  obtain ⟨Q, hQ, hpQ, hMQ⟩ := hM.1
  let _ : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQ
  let _ : Nontrivial (center Q) := hpQ.center_nontrivial
  let O := omega₁ (center Q) (p := 2)
  let _ : O.Characteristic := omega₁_characteristic _
  let _ : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let A0 := O.map (center Q).subtype
  let _ : A0.Characteristic := inferInstance
  let _ : IsElementaryAbelian 2 A0 := IsElementaryAbelian.map_subtype
  let A := A0.map Q.subtype
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  have hdiv : 2 ∣ Nat.card (center Q) :=
    (hpQ.to_subgroup (center Q)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := center Q); omega)
  have hA0 : A0 ≠ ⊥ := omega₁_map_subtype_ne_bot (center Q) 2 hdiv
  have hA : A ≠ ⊥ := by
    intro h
    exact hA0 ((map_eq_bot_iff_of_injective A0 Q.subtype_injective).mp h)
  have hle : M ≤ normalizer (A : Set G) := by
    rw [hMQ]
    exact normalizer_le_normalizer_characteristic_image Q A0
  exact ⟨A, hA, inferInstance, hM.eq_of_le
    ⟨A, hA, IsElementaryAbelian.isPGroup 2 A, rfl⟩ hle⟩

/-- The elementary subgroup can be placed in any fixed Sylow two-subgroup;
the original maximal local is a conjugate of its full normalizer. -/
public theorem exists_elementary_normalizer_in_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) :
    ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian 2 A ∧ ∃ g : G,
      M = (normalizer (A : Set G)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨B, hB, hEB, rfl⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hM
  let _ := hEB
  obtain ⟨P, hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  let f := MulAut.conj g
  let A := B.map f.toMonoidHom
  have hAS : A ≤ (S : Subgroup G) := by
    rw [← hg]
    exact map_mono hBP
  refine ⟨A, hAS, ?_, IsElementaryAbelian.map _, g⁻¹, ?_⟩
  · exact fun h => hB ((map_eq_bot_iff_of_injective B f.injective).mp h)
  · rw [show normalizer (A : Set G) = (normalizer (B : Set G)).map f.toMonoidHom
      from (map_equiv_normalizer_eq B f).symm]
    rw [map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp f.toMonoidHom = MonoidHom.id G := by
      ext x
      simp [f, mul_assoc]
    rw [hid, map_id]

/-- An exhaustive cover of elementary normalizers in one Sylow subgroup
gives an exhaustive cover of all maximal two-locals. -/
public theorem maximalTwoLocal_cover_of_elementary_normalizer_cover
    {G : Type*} [Group G] [Finite G] {ι : Type*}
    (S : Sylow 2 G) (L : ι → Subgroup G)
    (hcover : ∀ A : Subgroup G, A ≤ (S : Subgroup G) → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : ι) (g : G),
        normalizer (A : Set G) ≤ (L i).map (MulAut.conj g).toMonoidHom)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    ∃ (i : ι) (g : G), M ≤ (L i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨A, hAS, hA, hEA, g, rfl⟩ := exists_elementary_normalizer_in_sylow S hM
  obtain ⟨i, k, hk⟩ := hcover A hAS hA hEA
  refine ⟨i, g * k, ?_⟩
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) hk
  rw [map_map] at h
  have heq : (MulAut.conj g).toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (g * k)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rwa [heq] at h

end Theory.GroupTheory
