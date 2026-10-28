module
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.FullAxis
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Mutual TI normalizers in an odd quotient

The two mutual normalizers of a proper conjugate elementary TI pair lie in
the derived subgroup of the pair. If the conjugator maps to a normal odd
p-group, the pair has abelian image after that p-group is factored out.
Its mutual normalizers therefore map to both two-groups and p-groups, and
vanish. This gives the core containment used before inverter selection in
Aschbacher–Smith 12.2.21, printed p.802, using I.6.2(2a), pp.424–425.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G K : Type*} [Group G] [Finite G] [Group K]

/-- In an odd normal quotient image, the two mutual normalizers of a proper
conjugate TI pair vanish. -/
theorem ti_pair_mutual_normalizers_le_kernel_of_odd_image
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hTI : IsTISubgroup V)
    (q : G →* K) {p : ℕ} (R : Subgroup K) [R.Normal]
    (hR : IsPGroup p R) (hp : Nat.Coprime 2 p)
    (g : G) (hg : q g ∈ R)
    (hi : (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2) :
    (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ⊔
      (V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G)) ≤ q.ker := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let I := V ⊔ A
  let Y := (V ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (V : Set G))
  let f := (QuotientGroup.mk' R).comp q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hcard : Nat.card V = Nat.card A := (card_map_of_injective (MulAut.conj g).injective).symm
  have hproper : V ⊓ normalizer (A : Set G) ≠ V := by
    intro he
    have hh := relIndex_eq_one.mpr ((inf_eq_left.mp he) : V ≤ normalizer (A : Set G))
    change (normalizer (A : Set G)).relIndex V = 2 at hi
    omega
  have hne : A ≠ V := by
    intro he
    apply hproper
    rw [he, inf_eq_left.mpr V.le_normalizer]
  have hd : Disjoint V A := ((hTI.eq_or_disjoint_conjugate g).resolve_left hne).symm
  have hApr : A ⊓ normalizer (V : Set G) ≠ A := by
    intro he
    exact hproper (ti_pair_full_normalizer_right A V hd.symm (hTI.map_equiv _) hTI hcard.symm he)
  have hYI : Y ≤ I := sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hYder : Y ≤ ⁅I, I⁆ := by
    apply sup_le
    · obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp
        (fun h => hproper (le_antisymm inf_le_left h))
      rw [← ti_pair_commutator_eq V A hd hTI (hTI.map_equiv _) hcard hv hvU]
      exact commutator_mono hYI ((zpowers_le.mpr hv).trans le_sup_left)
    · obtain ⟨a, ha, haB⟩ := SetLike.not_le_iff_exists.mp
        (fun h => hApr (le_antisymm inf_le_left h))
      rw [← ti_pair_commutator_eq_right V A hd hTI (hTI.map_equiv _) hcard ha haB]
      exact commutator_mono hYI ((zpowers_le.mpr ha).trans le_sup_right)
  have hfg : f g = 1 := (QuotientGroup.eq_one_iff (q g)).mpr hg
  have hAf : A.map f = V.map f := by
    change (V.map (MulAut.conj g).toMonoidHom).map f = _
    rw [map_map]
    have he : f.comp (MulAut.conj g).toMonoidHom = f := by
      ext x
      simp [MulAut.conj_apply, hfg]
    rw [he]
  have hIf : I.map f = V.map f := by rw [Subgroup.map_sup, hAf, sup_idem]
  have hder : ⁅I, I⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator, hIf]
    let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map _
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hYR : Y.map q ≤ R := by
    rintro x ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff (q y)).mp (hder (hYder hy))
  have hY2 : IsPGroup 2 Y :=
    (isPGroup_pCoreIn 2 I).to_le (ti_pair_mutual_normalizers_le_twoCore V A hd hTI (hTI.map_equiv _))
  exact (map_eq_bot_iff Y (f := q)).mp (bot_unique
    ((le_inf le_rfl hYR).trans ((hY2.map q).disjoint_of_coprime hR hp).le_bot))
end CFSG.Quasithin.ChapterI.Section06To08
