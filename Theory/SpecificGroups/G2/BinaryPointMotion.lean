module
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder

/-!
# Point stabilizers in the full binary G₂ group

The subgroup interval above a Sylow two-subgroup consists of that subgroup,
the two root parabolics and the full group. Root descent supplies parabolic
containment, and each parabolic has index three over the positive roots.
Consequently a Sylow overgroup avoiding two proper generators is the Sylow
subgroup itself. The proof transports the literal Sylow marking along the
actual group isomorphism and an inner conjugation.

The original point-action consumer is Aschbacher--Smith 13.2.12,
printed p.882. Root geometry uses the existing licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Theory.SpecificGroups.G2.BinaryPointMotion

private theorem standard_interval (H : Subgroup (Model (ZMod 2)))
    (hU : unipotent ≤ H) :
    H = unipotent ∨ H = parabolic₁ ∨ H = parabolic₂ ∨ H = ⊤ := by
  have step (P : Subgroup (Model (ZMod 2))) (hUP : unipotent ≤ P)
      (hc : Nat.card P = 192) (hHP : H ≤ P) : H = unipotent ∨ H = P := by
    have hi : unipotent.relIndex P = 3 := by
      have h := (unipotent.subgroupOf P).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv, card_unipotent,
        Nat.card_zmod, hc] at h
      change 64 * unipotent.relIndex P = 192 at h
      omega
    have hp : (unipotent.relIndex H * H.relIndex P).Prime := by
      rw [relIndex_mul_relIndex _ _ _ hU hHP, hi]
      exact Nat.prime_three
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hp⟩ | ⟨_,hp⟩
    · exact Or.inr (le_antisymm hHP (relIndex_eq_one.mp hp))
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp hp) hU)
  by_cases ht : H = ⊤
  · exact Or.inr (Or.inr (Or.inr ht))
  rcases ProperSylowOvergroups.le_parabolic H hU (lt_top_iff_ne_top.mpr ht) with h | h
  · rcases step parabolic₁ (le_sup_left.trans borel_le_parabolic₁) (by
      norm_num [ParabolicCells.short_card, card_borel, Nat.card_zmod]) h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases step parabolic₂ (le_sup_left.trans borel_le_parabolic₂) (by
      norm_num [card_parabolic, Nat.card_zmod]) h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

private theorem standard_avoids (A B C : Subgroup (Model (ZMod 2)))
    (hUA : unipotent ≤ A) (hUB : unipotent ≤ B)
    (hgen : A ⊔ B = ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hUC : unipotent ≤ C) (hAC : ¬ A ≤ C) (hBC : ¬ B ≤ C) :
    C = unipotent := by
  have hP : (parabolic₁ (F := ZMod 2)) ≠ ⊤ := by
    intro he
    have hc := ParabolicCells.short_card (F := ZMod 2)
    rw [he,Nat.card_congr topEquiv.toEquiv,card_Model,card_borel,Nat.card_zmod] at hc
    norm_num at hc
  have hQ : (parabolic₂ (F := ZMod 2)) ≠ ⊤ := by
    intro he
    have hc := card_parabolic (F := ZMod 2)
    change (parabolic (F := ZMod 2)) = ⊤ at he
    rw [he,Nat.card_congr topEquiv.toEquiv,card_Model,Nat.card_zmod] at hc
    norm_num at hc
  have ha : A = parabolic₁ ∨ A = parabolic₂ := by
    rcases standard_interval A hUA with h | h | h | h
    · exact (hAC (h ▸ hUC)).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (hA h).elim
  have hb : B = parabolic₁ ∨ B = parabolic₂ := by
    rcases standard_interval B hUB with h | h | h | h
    · exact (hBC (h ▸ hUC)).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (hB h).elim
  rcases standard_interval C hUC with h | h | h | h
  · exact h
  · rcases ha with ha | ha
    · exact (hAC (ha ▸ h.ge)).elim
    · rcases hb with hb | hb
      · exact (hBC (hb ▸ h.ge)).elim
      · rw [ha,hb,sup_idem] at hgen
        exact (hQ hgen).elim
  · rcases ha with ha | ha
    · rcases hb with hb | hb
      · rw [ha,hb,sup_idem] at hgen
        exact (hP hgen).elim
      · exact (hBC (hb ▸ h.ge)).elim
    · exact (hAC (ha ▸ h.ge)).elim
  · exact (hAC (h ▸ le_top)).elim

/-- In the actual full binary G₂ group, any Sylow overgroup avoiding both
proper generators is the Sylow subgroup itself. -/
theorem sylow_overgroup_eq_of_avoids_generators
    {D : Type*} [Group D] [Finite D] (e : D ≃* Model (ZMod 2))
    (S : Sylow 2 D) (A B C : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hSB : (S : Subgroup D) ≤ B)
    (hgen : A ⊔ B = ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hSC : (S : Subgroup D) ≤ C) (hAC : ¬ A ≤ C) (hBC : ¬ B ≤ C) :
    C = (S : Subgroup D) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model (ZMod 2))
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (sylow (F := ZMod 2))
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup D).map f.toMonoidHom = unipotent := by
    change (S : Subgroup D).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map]
    exact (congrArg Sylow.toSubgroup hg).trans (sylow_coe (F := ZMod 2))
  have proper (X : Subgroup D) (hX : X ≠ ⊤) : X.map f.toMonoidHom ≠ ⊤ := by
    intro he
    apply hX
    exact map_injective f.injective (he.trans (map_top_of_surjective _ f.surjective).symm)
  have hc := standard_avoids (A.map f.toMonoidHom) (B.map f.toMonoidHom)
    (C.map f.toMonoidHom) (hS ▸ map_mono hSA) (hS ▸ map_mono hSB)
    (by rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ f.surjective])
    (proper A hA) (proper B hB) (hS ▸ map_mono hSC)
    (fun h => hAC ((map_le_map_iff_of_injective f.injective).mp h))
    (fun h => hBC ((map_le_map_iff_of_injective f.injective).mp h))
  exact map_injective f.injective (hc.trans hS.symm)

end Theory.SpecificGroups.G2.BinaryPointMotion
