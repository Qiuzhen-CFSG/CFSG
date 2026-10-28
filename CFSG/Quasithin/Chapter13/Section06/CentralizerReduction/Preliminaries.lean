module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.ConjugacyClassProduct
public import Theory.GroupTheory.CharacteristicLocalSylow

/-!
# Initial reductions in the A₅ centralizer argument

The abelian-span implication uses the A₅ specialization of the genuine
earlier theorem 13.5.12 and the equivalence in 13.5.10. Both remain explicit
inputs for the Section 13.6 assembly owner. The counterexample premise
excludes the actual projective matrix groups U₄(2) and L₄(3).

The Baumann and Thompson assertions follow from B.2.3 once 13.2.4 supplies
Baum(T) ≤ C_T(v). The normalizer bound uses 13.2.5 and 12.2.6. Finally, the
three-singular-vector product gives the normalizer-to-centralizer reduction
in the paragraph preceding 13.6.8. Its conjugacy-class and product premises
are geometric facts to be supplied from the actual A₅ module and 13.2.6(2).

These implications do not assert 13.6.6 or 13.6.7. Their component analysis
and the construction of all local geometry still belong to the complete
centralizer reduction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.926–928.
-/

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

open Subgroup ChapterB Stellmacher
open scoped BigOperators IsMulCommutative
variable {G : Type*} [Group G]

/-- The actual counterexample condition for the A₅ branch of 13.6.1. -/
@[expose] public def IsA5Counterexample (G : Type*) [Group G] : Prop :=
  ¬ ClassicalGroup.IsPSU G 4 2 ∧ ¬ ClassicalGroup.IsPSL G 4 3

/-- 13.6.2 from the two named earlier results, with the actual conjugate
spans and both actual classification alternatives retained. The global
earlier span controls every local span by inclusion of conjugators. -/
public theorem abelian_spans_of_earlier_source
    (V V₃ : Subgroup G) (z : G) (hcounter : IsA5Counterexample G)
    (h13512 : ¬ IsMulCommutative (conjugateSpanBy V₃ (Gv z)) →
      ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (h13510 : IsMulCommutative (conjugateSpanBy V₃ (Gv z)) ↔
      IsMulCommutative (conjugateSpanBy V (Gv z))) :
    IsMulCommutative (conjugateSpanBy V (Gv z)) ∧
      ∀ H : Subgroup G, H ≤ Gv z → IsMulCommutative (conjugateSpanBy V H) := by
  have hsmall : IsMulCommutative (conjugateSpanBy V₃ (Gv z)) := by
    by_contra hn
    exact (h13512 hn).elim hcounter.1 hcounter.2
  have hlarge := h13510.mp hsmall
  refine ⟨hlarge, ?_⟩
  let := hlarge
  intro H hH
  exact conjugateSpanBy_isMulCommutative_of_le le_rfl hH

/-- The contradiction used in the S₆ branch of 13.6.6 once C_G(V) = V
has been obtained from C.1.13(c) and 3.2.11. -/
public theorem not_selfCentralizing_of_abelian_span
    (V M : Subgroup G) (z : G)
    [IsMulCommutative (conjugateSpanBy V (Gv z))]
    (houtside : ¬ Gv z ≤ M) (hNM : normalizer (V : Set G) ≤ M) :
    ¬ centralizer (V : Set G) ≤ V := by
  intro hC
  exact houtside ((le_normalizer_of_abelian_conjugateSpanBy V (Gv z) hC).trans hNM)

/-- 13.6.4: both subgroups are inherited by the literal C_T(v).
The only local input is the earlier 13.2.4 containment. -/
public theorem baumann_and_thompson_centralizer [Finite G]
    (T : Subgroup G) (v : G) (hS : baumann T ≤ Tv T v) :
    baumann T = baumann (Tv T v) ∧
      elementaryAbelianMaxJ T = elementaryAbelianMaxJ (Tv T v) := by
  have hJ : elementaryAbelianMaxJ T ≤ baumann T := by
    apply le_inf (sSup_le fun _ hA => hA.1)
    intro j hj
    apply mem_centralizer_iff.mpr
    intro a ha
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj).symm
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq (Tv T v) T inf_le_left
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le T (Tv T v)
    (hJ.trans hS)
  have hord := le_antisymm hsmall.1 hlarge.1
  exact ⟨lemma_B_2_3_4 T (Tv T v) hS inf_le_left,
    le_antisymm (hlarge.2 hord.symm) (hsmall.2 hord)⟩

/-- The global Sylow witness has exactly C_T(v) as its ambient image.
The input index is only the local index in C_M(v); the characteristic
normalizer argument promotes it to C_G(v), as in 13.2.6(1). -/
public theorem exists_sylow_centralizer [Finite G]
    (T : Sylow 2 G) (M : Subgroup G) (v : G)
    (B : Subgroup (Tv (T : Subgroup G) v)) [B.Characteristic]
    (hlocal : ¬ 2 ∣ (Tv (T : Subgroup G) v).relIndex (Mv M v))
    (hBN : normalizer
      (B.map (Tv (T : Subgroup G) v).subtype : Set G) ≤ M) :
    ∃ P : Sylow 2 (Gv v), (P : Subgroup (Gv v)).map (Gv v).subtype =
      Tv (T : Subgroup G) v := by
  exact exists_sylow_of_characteristic_normalizer (Tv (T : Subgroup G) v) M
    (Gv v) B (T.isPGroup'.to_le inf_le_left) inf_le_right hlocal hBN

/-- 13.6.5, keeping the normalizer relative to Gᵥ. Its local-centralizer
identity uses both containments from Notation 12.2.5 and 12.2.6. -/
public theorem baumann_normalizer_control [Finite G]
    (T M V : Subgroup G) (v : G)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M) :
    Gv v ⊓ normalizer (baumann T : Set G) ≤ Mv M v ∧
      Mv M v = normalizer (V : Set G) ⊓ Gv v := by
  refine ⟨le_inf (inf_le_right.trans h1325) inf_le_left, ?_⟩
  exact le_antisymm (le_inf h1226 inf_le_right) (inf_le_inf_right _ hMV)

/-- The geometric reduction used before 13.6.8: the full normalizer of
Vᵥ fixes the product of its three singular vectors. Membership in their
finite set is expressed by actual ambient conjugacy with z. -/
public theorem normalizer_Vv_le_Gv
    (L : Subgroup G) (z v : G) [IsMulCommutative (Vv L z v)]
    (singular : Finset (Vv L z v))
    (hsingular : ∀ x : Vv L z v, x ∈ singular ↔
      ∃ c : G, MulAut.conj c z = (x : G))
    (hproduct : ((∏ x ∈ singular, x : Vv L z v) : G) = v) :
    normalizer (Vv L z v : Set G) ≤ Gv v :=
  normalizer_le_centralizer_of_conjugacy_product (Vv L z v) z v singular
    hsingular hproduct

/-- Once the main containment is proved, it gives both assertions of
13.6.7 using the geometric normalizer reduction above. The first containment
is explicitly an input here, not a claimed proof of the source theorem. -/
public theorem centralizer_conclusions_of_containment
    (L M V : Subgroup G) (z v : G)
    (hmain : Gv v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (hgeom : normalizer (Vv L z v : Set G) ≤ Gv v) :
    Gv v = normalizer (V : Set G) ⊓ Gv v ∧
      normalizer (Vv L z v : Set G) ≤ M :=
  ⟨(inf_eq_right.mpr hmain).symm, hgeom.trans (hmain.trans hMV)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
