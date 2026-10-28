module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.PGLComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# The nine-element field extension in F.6.18(8)

The actual PSL₂(9) equivalence identifies the component with A₆. Its
supplementing involution acts faithfully, since F* is self-centralizing.
The proved outer-involution comparison gives either the natural S₆ or
PGL₂(9). The latter has an element of order eight, whereas the supplied
Sylow C₂ × D₈ has exponent four. The natural extension is therefore the
whole S₆, through its actual conjugation action on A₆.

The full field row, including its Frobenius action, is retained. The proof
works for every involution supplement with this component and Sylow group.
The terminal consumer is `SourceInput.component_row_eight_field` in
`ComponentRows.OddFields`.

Sources: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18(8), printed p.309, and the proof of 15.3.1, printed p.1155;
GLS, Volume 3, Proposition 5.2.7(a), for outer-involution conjugacy.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open AlternatingSix.ShadowLocal AlternatingSix.OuterInvolutionExtension
open Atlas.Comparisons.Exceptional

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.OddFields
variable {D : Type*} [Group D] [Finite D]

private theorem no_eight (S : Sylow 2 D)
    (e : S ≃* (FSource.C 2 × DihedralGroup 4)) (x : D) : orderOf x ≠ 8 := by
  intro hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_zpowers, hx]; decide)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let y : P := ⟨x, hP (mem_zpowers x)⟩
  let a := (P.equiv S).trans e
  have hfour : ∀ z : FSource.C 2 × DihedralGroup 4, z ^ 4 = 1 := by decide +kernel
  have hy : orderOf (a y) = 8 := by rw [a.orderOf_eq, ← Subgroup.orderOf_coe]; exact hx
  have hd := orderOf_dvd_of_pow_eq_one (hfour (a y))
  rw [hy] at hd
  norm_num at hd

private theorem natural_extension (β : AutA6) (hn : β ∈ natural) (hi : β ∉ AlternatingSix.ShadowLocal.inner) :
    AlternatingSix.ShadowLocal.inner ⊔ zpowers β = natural := by
  obtain ⟨s, hs⟩ := hn
  change permutationAction s = β at hs
  have hsout : s ∉ alternatingGroup (Fin 6) := by
    intro ha
    exact hi ⟨⟨s, ha⟩, (permutationAction_coe ⟨s, ha⟩).symm.trans hs⟩
  have hgen : alternatingGroup (Fin 6) ⊔ zpowers s = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ alternatingGroup (Fin 6)
    · exact mem_sup_left hx
    · have hxs : x * s⁻¹ ∈ alternatingGroup (Fin 6) :=
        ((alternatingGroup (Fin 6)).mul_mem_iff_of_index_two
          alternatingGroup.index_eq_two).mpr (iff_of_false hx (by simpa using hsout))
      have hm := (alternatingGroup (Fin 6) ⊔ zpowers s).mul_mem
        (mem_sup_left hxs) (mem_sup_right (mem_zpowers s))
      simpa using hm
  have hm : (alternatingGroup (Fin 6)).map permutationAction = AlternatingSix.ShadowLocal.inner := by
    ext a
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, (permutationAction_coe ⟨s, hs⟩).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.property, permutationAction_coe g⟩
  have h := congrArg (Subgroup.map permutationAction) hgen
  rw [Subgroup.map_sup, hm, MonoidHom.map_zpowers, hs, ← MonoidHom.range_eq_map] at h
  simpa only [permutationAction, natural,
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup] using h

/-- The actual field-extension row at p = 3 is S₆. The prescribed Sylow
excludes the exceptional PGL₂(9) extension of its actual A₆ component. -/
theorem fieldRow_nine_equiv_symmetricSix (r : FSource.FieldExtensionRow (D := D))
    (hp : r.field.prime = 3) (S : Sylow 2 D)
    (es : S ≃* (FSource.C 2 × DihedralGroup 4)) : Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  have hc : Nat.card r.field.Carrier = 9 := by rw [r.field.card, r.degree, hp]; decide
  let e := r.componentEquiv.trans (psl2Card9EquivAlt6 hc)
  have hrN : r.element ∈ normalizer (generalizedFitting D : Set D) := by
    rw [(generalizedFitting D).normalizer_eq_top]; trivial
  have hrout : r.element ∉ centralizer (generalizedFitting D : Set D) ⊔ generalizedFitting D := by
    rw [sup_eq_right.mpr CFSG.Quasithin.ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le]
    exact r.outside
  let β := normalizerAction e ⟨r.element, hrN⟩
  let ed : ↥(generalizedFitting D ⊔ zpowers r.element) ≃* D :=
    (MulEquiv.subgroupCongr r.generated).trans topEquiv
  let ea := extensionEquiv e hrN r.involution hrout
  have hn : β ∈ natural := by
    by_contra hn
    obtain ⟨ex⟩ := exceptional_extension_equiv_canonical β
      (normalizerAction_sq e hrN (r.involution ▸ pow_orderOf_eq_one r.element)) hn
    obtain ⟨ec⟩ := canonicalExtension_equiv_pgl2
    let a := ((ed.symm.trans ea).trans ex).trans ec
    obtain ⟨U, _, hcyc, hcard, _⟩ := GorensteinWalter.pgl2_split_torus_reflection_data Nine.F
    let _ : IsCyclic U := hcyc
    obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    have h8 : orderOf (a.symm (x : GorensteinWalter.PGL2 Nine.F)) = 8 := by
      rw [a.symm.orderOf_eq, Subgroup.orderOf_coe, hx, hcard, Nine.card]
    exact no_eight S es _ h8
  have he : AlternatingSix.ShadowLocal.inner ⊔ zpowers β = natural :=
    natural_extension β hn (normalizerAction_not_inner e hrN hrout)
  exact ⟨((ed.symm.trans ea).trans (MulEquiv.subgroupCongr he)).trans
    GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms.symm⟩
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.OddFields
