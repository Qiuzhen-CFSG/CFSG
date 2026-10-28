module
public import Theory.SpecificGroups.AlternatingSevenNormalControl
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# Sylow normalizers above perfect central covers of A₇

The actual conjugation action on a normal perfect subgroup descends faithfully
through its center. An A₇ identification of that central quotient therefore
produces a permutation action with kernel exactly the original centralizer.
Its image contains A₇, so the A₇/S₇ Sylow-normalizer theorem gives the desired
normalizer containment. In particular it preserves the literal marked subgroup
S∩C_H(L) for every S-normalized L in the cover.

Source: Aschbacher–Smith, C.5.12, printed p.163. This preserves the central
three-cover alternative instead of replacing the original component by A₇.
-/
public section
open Subgroup
namespace AlternatingSevenCentralCover
variable {H : Type*} [Group H] [Finite H]
private noncomputable def permAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by decide) (by decide))
omit [Finite H] in
theorem exists_permutation_action (D : Subgroup H) [D.Normal] [Group.IsPerfect D]
    (e : D ⧸ center D ≃* alternatingGroup (Fin 7)) :
    ∃ f : H →* Equiv.Perm (Fin 7), f.ker = centralizer (D : Set H) ∧
      D.map f = alternatingGroup (Fin 7) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center D))
  let f : H →* Equiv.Perm (Fin 7) := permAut.symm.toMonoidHom.comp
    ((MulAut.centralQuotientAction e).comp (MulAut.conjNormal : H →* MulAut D))
  have hf (d : D) : f d = (q d : Equiv.Perm (Fin 7)) := by
    apply permAut.injective
    change permAut (permAut.symm (MulAut.centralQuotientAction e (MulAut.conjNormal (d : H)))) = _
    rw [permAut.apply_symm_apply]
    have hd : MulAut.conjNormal (d : H) = MulAut.conj d := by ext x; rfl
    rw [hd,MulAut.centralQuotientAction_conj]
    rfl
  refine ⟨f,?_,?_⟩
  · ext g
    change permAut.symm (MulAut.centralQuotientAction e (MulAut.conjNormal g)) = 1 ↔ _
    rw [← map_one permAut.symm,permAut.symm.injective.eq_iff,
      ← map_one (MulAut.centralQuotientAction e),
      (MulAut.centralQuotientAction_injective e).eq_iff]
    change g ∈ (MulAut.conjNormal : H →* MulAut D).ker ↔ _
    rw [MulAut.conjNormal_ker_eq_centralizer]
  · apply le_antisymm
    · rintro _ ⟨d,hd,rfl⟩
      rw [hf ⟨d,hd⟩]
      exact (q ⟨d,hd⟩).property
    · intro z hz
      obtain ⟨d,hd⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center D))) ⟨z,hz⟩
      refine ⟨d,d.property,?_⟩
      rw [hf]
      exact congrArg Subtype.val hd

theorem sylow_normalizer_le (D : Subgroup H) [D.Normal] [Group.IsPerfect D]
    (e : D ⧸ center D ≃* alternatingGroup (Fin 7)) (S : Sylow 2 H) :
    normalizer (S : Set H) ≤ (S : Subgroup H) ⊔ centralizer (D : Set H) := by
  obtain ⟨f,hker,hD⟩ := exists_permutation_action D e
  let Q := S.mapSurjective f.rangeRestrict_surjective
  have hA : alternatingGroup (Fin 7) ≤ f.range := hD ▸ D.map_le_range f
  have hn := AlternatingSevenSylow.overgroup_sylow_normalizer f.range hA Q
  have hm : (normalizer (S : Set H)).map f.rangeRestrict ≤ (S : Subgroup H).map f.rangeRestrict := by
    rw [← show normalizer (Q : Set f.range) = (S : Subgroup H).map f.rangeRestrict from hn]
    exact (S : Subgroup H).le_normalizer_map f.rangeRestrict
  have hh := map_le_iff_le_comap.mp hm
  rwa [comap_map_eq,MonoidHom.ker_rangeRestrict,hker] at hh

theorem sylow_normalizer_le_marked_centralizer
    (D : Subgroup H) [D.Normal] [Group.IsPerfect D]
    (e : D ⧸ center D ≃* alternatingGroup (Fin 7)) (S : Sylow 2 H)
    (L : Subgroup H) (hLD : L ≤ D)
    (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) := by
  have hDL : centralizer (D : Set H) ≤ normalizer (L : Set H) :=
    (centralizer_le hLD).trans (centralizer_le_normalizer (L : Set H))
  have hnL := (sylow_normalizer_le D e S).trans (sup_le hSL hDL)
  exact (le_inf le_rfl (hnL.trans (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
end AlternatingSevenCentralCover
