module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeSection
public import Mathlib.GroupTheory.IsSubnormal

/-!
# The residual of a Sylow conjugate span

If a p-subgroup S normalizes L, put N=⟨S^L⟩. The whole join LS normalizes N
and its embedded p-residual. The quotient LS/L is a p-group, so that residual
lies in L. It is therefore normal in L and subnormal in every ambient group
in which L is subnormal. No arbitrary subgroup of N has this property.

Source application: Aschbacher--Smith C.1.26, printed p.132.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem conjugateSpanBy_normalized_by_join (S L : Subgroup G) :
    L ⊔ S ≤ normalizer (conjugateSpanBy S L : Set G) :=
  sup_le (le_normalizer_conjugateSpanBy S L)
    ((le_conjugateSpanBy S L).trans (conjugateSpanBy S L).le_normalizer)

omit [Fact p.Prime] in
theorem embedded_residual_conjugateSpanBy_normalized (S L : Subgroup G) :
    L ⊔ S ≤ normalizer ((pResidual p (conjugateSpanBy S L)).map
      (conjugateSpanBy S L).subtype : Set G) :=
  (conjugateSpanBy_normalized_by_join S L).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual p (conjugateSpanBy S L)))

variable [Finite G]

theorem embedded_residual_conjugateSpanBy_le (S L : Subgroup G)
    (hS : IsPGroup p S) (hn : S ≤ normalizer (L : Set G)) :
    (pResidual p (conjugateSpanBy S L)).map (conjugateSpanBy S L).subtype ≤ L := by
  let N := conjugateSpanBy S L
  let P := L ⊔ S
  let K := (pResidual p N).map N.subtype
  have hNP : N ≤ P := conjugateSpanBy_le le_sup_right
    (le_sup_left.trans P.le_normalizer)
  have hKP : K ≤ P := (map_subtype_le _).trans hNP
  have hLP : L ≤ P := le_sup_left
  have hSP : S ≤ P := le_sup_right
  let : (L.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hg : L.subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
    rw [←subgroupOf_sup hLP hSP,subgroupOf_self]
  have hpK : IsPPerfect p (K.subgroupOf P) :=
    (isPPerfect_embedded_pResidual p N).of_surjective (subgroupOfEquivOfLe hKP).symm.toMonoidHom
      (subgroupOfEquivOfLe hKP).symm.surjective
  have hKL := le_normal_of_isPPerfect_of_le_sup_pGroup
    (K.subgroupOf P) (L.subgroupOf P) (S.subgroupOf P) hpK hS.comap_subtype
      (by rw [hg]; exact le_top)
  intro k hk
  exact hKL (show (⟨k,hKP hk⟩ : P) ∈ K.subgroupOf P from hk)

/-- The canonical residual is subnormal in the original ambient group. -/
theorem embedded_residual_conjugateSpanBy_subnormal (S L : Subgroup G)
    (hS : IsPGroup p S) (hn : S ≤ normalizer (L : Set G)) (hL : L.IsSubnormal) :
    ((pResidual p (conjugateSpanBy S L)).map (conjugateSpanBy S L).subtype).IsSubnormal := by
  let K := (pResidual p (conjugateSpanBy S L)).map (conjugateSpanBy S L).subtype
  have hKL : K ≤ L := embedded_residual_conjugateSpanBy_le S L hS hn
  have hLN : L ≤ normalizer (K : Set G) :=
    le_sup_left.trans (embedded_residual_conjugateSpanBy_normalized (p := p) S L)
  have hnormal : (K.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr hLN
  exact IsSubnormal.trans hKL hnormal.isSubnormal hL
end Subgroup
