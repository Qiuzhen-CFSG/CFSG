module

public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.Completion

/-!
# Distinct TI-conjugates in the diagonal-outer branch

In 15.3.38, suppose the graph-field involution is fused to a nonidentity
member of the TI four-group `V₁`. It lies outside `V₁` and centralizes
`V₁`. Its conjugate four-group is therefore distinct from `V₁`, and the
TI centralizer criterion makes `V₁` normalize that conjugate. The corrected
I.6.2 now applies and makes the two groups commute.

The proof below establishes distinctness from the fusion witness before
invoking I.6.2, and transports both the TI and elementary-abelian properties
along the actual conjugating automorphism. It proves this step only; the
remaining centralizer, transfer and nonfusion arguments are separate.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
p.1137; corrected I.6.2 as documented in `docs/quasithin-proof-basis.md`.
-/

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup
open CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G]

private theorem ti_map (V : Subgroup G) (hV : IsTISubgroup V) (e : G ≃* G) :
    IsTISubgroup (V.map e.toMonoidHom) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg x hx hconj
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  have hgn : e.symm g ∉ normalizer (V : Set G) := by
    intro hn
    apply hg
    rw [← V.map_equiv_normalizer_eq e]
    exact mem_map.mpr ⟨e.symm g, hn, e.apply_symm_apply g⟩
  have hc : e.symm g * a * (e.symm g)⁻¹ ∈ V := by
    obtain ⟨b, hb, he⟩ := mem_map.mp hconj
    have he' := congrArg e.symm he
    have hb' : b = e.symm g * a * (e.symm g)⁻¹ := by
      simpa using he'
    exact hb' ▸ hb
  have ha1 := (isTISubgroup_iff V).mp hV (e.symm g) hgn a ha hc
  simp [ha1]

private theorem ti_disjoint (V : Subgroup G) (hV : IsTISubgroup V) (g : G)
    (hne : V.map (MulAut.conj g).toMonoidHom ≠ V) :
    Disjoint (V.map (MulAut.conj g).toMonoidHom) V := by
  apply Disjoint.symm
  apply Subgroup.disjoint_def.mpr
  intro a haV ha
  have hgn : g ∉ normalizer (V : Set G) := by
    intro hn
    exact hne (mem_normalizer_iff_map_conj_eq.mp hn)
  obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
  have hb1 := (isTISubgroup_iff V).mp hV g hgn b hb haV
  simp [hb1]

/-- The corrected I.6.2 application in 15.3.38. The conjugate containing
`w` is proved distinct using `w ∉ V`; distinctness is not an extra
hypothesis left for the caller. -/
public theorem ti_conjugate_centralizes_of_fusion_outside [Finite G]
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : IsTISubgroup V)
    {v w g : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hfusion : (MulAut.conj g) v = w) (hw : w ∉ V)
    (hwC : w ∈ centralizer (V : Set G)) :
    V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  have hwA : w ∈ A := mem_map.mpr ⟨v, hv, hfusion⟩
  have hw1 : w ≠ 1 := by
    intro he
    apply hv1
    have hh := (MulAut.conj g).injective (hfusion.trans (he.trans (map_one _).symm))
    exact hh
  have hVA : V ≠ A := by
    intro he
    exact hw (he.symm ▸ hwA)
  have hA : IsTISubgroup A := ti_map V hV (MulAut.conj g)
  have hVN : V ≤ normalizer (A : Set G) := by
    apply le_trans _ (hA.centralizer_le_normalizer hwA hw1)
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hwC a ha)
  have hcross : ∀ a : G, A.map (MulAut.conj a).toMonoidHom ≠ V →
      Disjoint (A.map (MulAut.conj a).toMonoidHom) V := by
    intro a hne
    have he : A.map (MulAut.conj a).toMonoidHom =
        V.map (MulAut.conj (a * g)).toMonoidHom := by
      dsimp [A]
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [he] at hne ⊢
    exact ti_disjoint V hV (a * g) hne
  have hUeq : V ⊓ normalizer (A : Set G) = V := inf_eq_left.mpr hVN
  have hU : V ⊓ normalizer (A : Set G) ≠ ⊥ := by
    rw [hUeq]
    intro hbot
    exact hv1 (Subgroup.mem_bot.mp (hbot ▸ hv))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (A := V) (MulAut.conj g).toMonoidHom
  have hcard : Nat.card V = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective V (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv
  have h := lemma_I_6_2_elementary V A hVA hV hA hcard hcross hU
  exact (h.2.2.2.2.2.2.1 (Or.inl hUeq)).1

end CFSG.Quasithin.Chapter15.Section03
