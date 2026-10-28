module

public import Theory.GroupAction.RegularCentralizerEmbedding
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow centralizers from a regular action off one point

Suppose a group acts faithfully, the normalizer of a Sylow subgroup is a
proper point stabilizer, and the Sylow subgroup acts regularly on the
remaining points. Its centralizer fixes the distinguished point, so its
action on the remaining points is faithful. The regular-action centralizer
embedding makes this centralizer a p-group. Since it normalizes the Sylow
subgroup, Sylow maximality places it inside that subgroup.

This is the regular-action centralizer theorem (GLS, Volume 2, Chapter 1,
Lemma 2.10) applied to rank-one permutation groups.
-/

open Subgroup

/-- A faithful regular action off the point fixed by a proper Sylow normalizer
forces the Sylow subgroup to contain its ambient centralizer. -/
public theorem Sylow.centralizer_le_of_faithful_regular_compl
    {G Ω : Type*} [Group G] {p : ℕ} (S : Sylow p G)
    (ρ : G →* Equiv.Perm Ω) (hρ : Function.Injective ρ) (a : Ω)
    (hN : normalizer (S : Set G) =
      (MulAction.stabilizer (Equiv.Perm Ω) a).comap ρ)
    (hproper : normalizer (S : Set G) < ⊤)
    (hregular : ∀ b c : Ω, b ≠ a → c ≠ a → ∃! s : S, ρ (s : G) b = c) :
    centralizer (S : Set G) ≤ (S : Subgroup G) := by
  classical
  let C := centralizer (S : Set G)
  let : MulAction G Ω := MulAction.compHom Ω ρ
  have hfix (c : C) : (c : G) • a = a := by
    have hc := Subgroup.centralizer_le_normalizer (S : Set G) c.property
    rw [hN] at hc
    exact hc
  have hex : ∃ b : Ω, b ≠ a := by
    by_contra! hn
    apply hproper.ne
    apply top_unique
    intro g _
    rw [hN]
    exact hn (ρ g a)
  obtain ⟨b, hb⟩ := hex
  obtain ⟨f, hf⟩ := MulAction.exists_injective_hom_of_commuting_regular_action
    (H := S) (J := C) {c : Ω | c ≠ a} b hb
    (by
      intro c hc d hd
      exact hregular c d hc hd)
    (by
      intro c d hd he
      apply hd
      apply (ρ (c : G)).injective
      exact he.trans (hfix c).symm)
    (by
      intro s c d
      change (s : G) • ((c : G) • d) = (c : G) • ((s : G) • d)
      rw [← mul_smul, ← mul_smul, c.property s s.property])
    (by
      intro c hc
      apply Subtype.ext
      apply hρ
      change ρ (c : G) = ρ 1
      rw [map_one]
      ext d
      by_cases hd : d = a
      · subst d
        exact hfix c
      · exact hc d hd)
  have hC : IsPGroup p C := S.isPGroup'.of_injective f hf
  have hsup : IsPGroup p ((S : Subgroup G) ⊔ C : Subgroup G) :=
    S.isPGroup'.to_sup_of_normal_left' hC (Subgroup.centralizer_le_normalizer _)
  exact sup_eq_left.mp (S.is_maximal' hsup le_sup_left)
