module
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.ConjugateSpanOrder
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.ElementaryAbelian.Join

/-!
# Conjugate spans of elementary TI subgroups

A nonidentity common point identifies two TI conjugates. For elementary
TI subgroups, a centralizing point makes its whole conjugate centralize.
Consequently, a displacement group preserving a point orbit in a maximum
elementary product normalizes the product. Transitivity identifies that
product with the conjugate span.

Source: Aschbacher–Smith, 2.4.21, printed p.536.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Two conjugates of a TI subgroup sharing a nonidentity point are equal. -/
theorem IsTISubgroup.conjugate_eq_of_common_point
    {Z : Subgroup G} (hTI : IsTISubgroup Z) (g h a : G)
    (ha1 : a≠1) (hag : a∈Z.map (MulAut.conj g).toMonoidHom)
    (hah : a∈Z.map (MulAut.conj h).toMonoidHom) :
    Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj h).toMonoidHom := by
  have he : (Z.map (MulAut.conj h).toMonoidHom).map (MulAut.conj (g*h⁻¹)).toMonoidHom =
      Z.map (MulAut.conj g).toMonoidHom := by
    change (Z.conjBy h).conjBy (g*h⁻¹)=Z.conjBy g
    rw [←conjBy_mul]
    simp only [inv_mul_cancel_right]
  rcases (hTI.map_equiv (MulAut.conj h)).eq_or_disjoint_conjugate (g*h⁻¹) with hh | hd
  · exact he.symm.trans hh
  · rw [he] at hd
    exact False.elim (ha1 (mem_bot.mp ((disjoint_iff.mp hd) ▸ (show a∈Z.map (MulAut.conj g).toMonoidHom ⊓ Z.map (MulAut.conj h).toMonoidHom from ⟨hag,hah⟩))))

/-- A nonidentity element of a conjugate centralizing an elementary TI
subgroup makes the whole conjugate centralize it. -/
theorem IsTISubgroup.conjugate_le_centralizer_of_point
    {Z : Subgroup G} [IsElementaryAbelian 2 Z] (hTI : IsTISubgroup Z)
    (g a : G) (ha : a ∈ Z.map (MulAut.conj g).toMonoidHom) (ha1 : a ≠ 1)
    (hac : a ∈ centralizer (Z : Set G)) :
    Z.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) := by
  let E := Z.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  rcases hTI.eq_or_disjoint_conjugate g with he | hd
  · rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hn : E ⊓ centralizer (Z : Set G) ≠ ⊥ := by
    intro hh
    exact ha1 (mem_bot.mp (hh ▸ (show a ∈ E ⊓ centralizer (Z : Set G) from ⟨ha,hac⟩)))
  have hfull := ti_pair_full_normalizer_of_centralizer_ne_bot Z E hd.symm (hTI.map_equiv _) hn
  exact le_centralizer_iff.mp (ti_pair_commute_of_full_normalizer Z E hd.symm
    hTI (hTI.map_equiv _) (card_map_of_injective (MulAut.conj g).injective).symm hfull)

/-- A displacement group preserves the maximum elementary product once
its translates of one nonidentity point remain in that product. -/
theorem IsTISubgroup.normalizes_product_of_point_orbit
    {Z : Subgroup G} [IsElementaryAbelian 2 Z] (hTI : IsTISubgroup Z)
    (g a : G) (K : Subgroup G)
    (ha : a ∈ Z.map (MulAut.conj g).toMonoidHom) (ha1 : a ≠ 1)
    (hV : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ∈
      Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hKZ : K ≤ centralizer (Z : Set G))
    (horbit : ∀ k ∈ K, k*a*k⁻¹ ∈ Z ⊔ Z.map (MulAut.conj g).toMonoidHom) :
    K ≤ normalizer ((Z ⊔ Z.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  let E := Z.map (MulAut.conj g).toMonoidHom
  let V := Z ⊔ E
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := hV.2.1
  intro k hk
  let b := k*a*k⁻¹
  have hbV : b ∈ V := horbit k hk
  have hb1 : b ≠ 1 := by
    intro he
    apply ha1
    exact (MulAut.conj k).map_eq_one_iff.mp (show (MulAut.conj k) a = 1 from he)
  have hbE : b ∈ E.map (MulAut.conj k).toMonoidHom := mem_map_of_mem _ ha
  have heMap : E.map (MulAut.conj k).toMonoidHom = Z.map (MulAut.conj (k*g)).toMonoidHom :=
    (conjBy_mul Z k g).symm
  have hbCZ : b ∈ centralizer (Z : Set G) := by
    intro z hz
    exact congrArg Subtype.val (mul_comm (⟨z,mem_sup_left hz⟩ : V) ⟨b,hbV⟩)
  have hbCE : b ∈ centralizer (E : Set G) := by
    intro z hz
    exact congrArg Subtype.val (mul_comm (⟨z,mem_sup_right hz⟩ : V) ⟨b,hbV⟩)
  have hECZ : E.map (MulAut.conj k).toMonoidHom ≤ centralizer (Z : Set G) := by
    rw [heMap]
    exact hTI.conjugate_le_centralizer_of_point (k*g) b (heMap ▸ hbE) hb1 hbCZ
  have hECE : E.map (MulAut.conj k).toMonoidHom ≤ centralizer (E : Set G) :=
    (hTI.map_equiv (MulAut.conj g)).conjugate_le_centralizer_of_point k b hbE hb1 hbCE
  have hECV : E.map (MulAut.conj k).toMonoidHom ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hECZ) (le_centralizer_iff.mp hECE)
  let : IsElementaryAbelian 2 (E.map (MulAut.conj k).toMonoidHom) := IsElementaryAbelian.map _
  have hj : IsElementaryAbelian 2 (V ⊔ E.map (MulAut.conj k).toMonoidHom : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hECV
  have he : V ⊔ E.map (MulAut.conj k).toMonoidHom = V :=
    (eq_of_le_of_card_ge le_sup_left (hV.2.2 _ le_top hj)).symm
  have hEV : E.map (MulAut.conj k).toMonoidHom ≤ V := le_sup_right.trans_eq he
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup]
    refine sup_le ?_ hEV
    have hZn : k ∈ normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _ (hKZ hk)
    rw [mem_normalizer_iff_map_conj_eq.mp hZn]
    exact le_sup_left
  · rw [card_map_of_injective (MulAut.conj k).injective]

omit [Finite G] in
/-- Transitivity on the central coset identifies the full product with the
span of the actual conjugate under the displacement group. -/
theorem product_eq_conjugate_span_of_central_translates
    (Z E K : Subgroup G) (a : G) (ha : a ∈ E)
    (hK : K ≤ normalizer ((Z ⊔ E : Subgroup G) : Set G))
    (htrans : ∀ z ∈ Z, ∃ k ∈ K, k*a*k⁻¹=a*z) :
    Z ⊔ E = conjugateSpanBy E K := by
  apply le_antisymm
  · refine sup_le ?_ (le_conjugateSpanBy E K)
    intro z hz
    obtain ⟨k,hk,he⟩ := htrans z hz
    have haz : a*z ∈ conjugateSpanBy E K := he ▸ subset_closure ⟨k,hk,a,ha,rfl⟩
    exact (conjugateSpanBy E K).mul_mem_cancel_left (le_conjugateSpanBy E K ha) |>.mp haz
  · exact conjugateSpanBy_le le_sup_right hK
end CFSG.Quasithin.ChapterI.Section06To08
