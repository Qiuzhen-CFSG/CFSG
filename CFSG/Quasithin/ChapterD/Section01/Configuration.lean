module

public import CFSG.Quasithin.ChapterD.Defs

/-!
# Stellmacher's qrc-Lemma: basic subgroup consequences

Source: Aschbacher–Smith, §D.1, printed pp. 171–177. The no-common-normal
condition excludes normality of a nontrivial internal module in the second
group. The conjugate-span lemmas give its containment in normal overgroups.
-/

namespace CFSG.Quasithin.ChapterD

variable {G : Type*} [Group G]

/-- The generating module is contained in its conjugate span. -/
public theorem le_conjugateSpan (H V : Subgroup G) : V ≤ conjugateSpan H V := by
  calc
    V = V.map (MulAut.conj (1 : G)).toMonoidHom := by
      have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [he, Subgroup.map_id]
    _ ≤ conjugateSpan H V := le_iSup (fun g : H =>
      V.map (MulAut.conj (g : G)).toMonoidHom) (1 : H)

/-- Every H-invariant overgroup of V contains its H-conjugate span. -/
public theorem conjugateSpan_le (H V K : Subgroup G) (hVK : V ≤ K)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : conjugateSpan H V ≤ K := by
  apply iSup_le
  intro g
  exact (Subgroup.map_mono hVK).trans_eq
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHK g.property))

/-- If V is already H-invariant, its H-conjugate span is V. -/
public theorem conjugateSpan_eq_of_normalized (H V : Subgroup G)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) : conjugateSpan H V = V :=
  le_antisymm (conjugateSpan_le H V V le_rfl hHV) (le_conjugateSpan H V)

/-- An internal elementary abelian normal subgroup lies in the 2-core. -/
public theorem QRCConfiguration.module_le_core
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V) :
    V ≤ twoCoreIn G₁ := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsElementaryAbelian 2 V := h.module_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf G₁) :=
    IsElementaryAbelian.subgroupOf h.module_le
  have hcore : V.subgroupOf G₁ ≤ pCore 2 G₁ := by
    apply le_sSup
    exact ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer h.module_le).mpr
      h.module_normalized, IsElementaryAbelian.isPGroup 2 (V.subgroupOf G₁)⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le h.module_le]
  exact Subgroup.map_mono hcore

/-- A subgroup cannot simultaneously be normal in both members of the
configuration and lie nontrivially inside the first 2-core. -/
public theorem QRCConfiguration.eq_bot_of_normalized
    {G₁ G₂ T V K : Subgroup G} (h : QRCConfiguration G₁ G₂ T V)
    (hK : K ≤ twoCoreIn G₁) (h₁ : G₁ ≤ Subgroup.normalizer (K : Set G))
    (h₂ : G₂ ≤ Subgroup.normalizer (K : Set G)) :
    K = ⊥ :=
  h.no_common_normal K hK (sup_le h₁ h₂)

/-- The normality contradiction used in D.1.3 and D.1.4. -/
public theorem QRCConfiguration.module_not_normalized_right
    {G₁ G₂ T V : Subgroup G} (h : QRCConfiguration G₁ G₂ T V)
    (hV : V ≠ ⊥) :
    ¬ G₂ ≤ Subgroup.normalizer (V : Set G) := by
  intro h₂
  exact hV (h.eq_bot_of_normalized h.module_le_core h.module_normalized h₂)

end CFSG.Quasithin.ChapterD
