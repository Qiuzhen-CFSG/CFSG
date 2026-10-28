module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Lifting the C.1.27 conjugate span through its centralizer quotient

A two-perfect seed generates a two-perfect conjugate span L. If the
seed centralizes O₂(G) modulo V, so does L. The two-layer fixer theorem
places [C_G(V),L] in O₂(G). The latter normalizes L, so L is exactly the
two-residual of LO₂(G); therefore C_G(V) normalizes L. Subnormality in
the original centralizer quotient now lifts, and U(L) lies in V.

The preimage consumer takes an actual subnormal subgroup in G/C_G(V).
B.1.13 supplies this subgroup; no assumption that C_G(V) is a two-group
is made. The later irreducible short-group recognition is separate.
Source: Aschbacher–Smith C.1.27, printed pp.132–133.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
public theorem conjugateSpan_twoPerfect (K P : Subgroup G) (hpK : IsPPerfect 2 K) :
    IsPPerfect 2 (conjugateSpanBy K P) := by
  let L := conjugateSpanBy K P
  let R := (pResidual 2 L).map L.subtype
  have hKL : K ≤ L := le_conjugateSpanBy K P
  have hpKL : IsPPerfect 2 (K.subgroupOf L) :=
    hpK.of_surjective (subgroupOfEquivOfLe hKL).symm.toMonoidHom
      (subgroupOfEquivOfLe hKL).symm.surjective
  have hKR : K ≤ R := by
    have hh := map_mono (f := L.subtype) (le_pResidual_of_isPPerfect _ hpKL)
    rwa [map_subgroupOf_eq_of_le hKL] at hh
  have hPR : P ≤ normalizer R :=
    (le_normalizer_conjugateSpanBy K P).trans
      (normalizer_le_normalizer_characteristic_image L (pResidual 2 L))
  have hLR : L ≤ R := conjugateSpanBy_le hKR hPR
  apply (pResidual_eq_top_iff 2 L).mp
  apply map_injective (f := L.subtype) L.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm (map_subtype_le _) hLR

public theorem conjugateSpan_subnormal_of_centralizer_image
    (V K P : Subgroup G) [V.Normal] (hpV : IsPGroup 2 V)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hpK : IsPPerfect 2 K) (hQP : pCore 2 G ≤ P)
    (hKQ : ⁅K, pCore 2 G⁆ ≤ V)
    (himage : ((conjugateSpanBy K P).map
      (QuotientGroup.mk' (centralizer (V : Set G)))).IsSubnormal) :
    (conjugateSpanBy K P).IsSubnormal ∧
      (blockU (conjugateSpanBy K P)).map (conjugateSpanBy K P).subtype ≤ V := by
  let Q := pCore 2 G
  let C := centralizer (V : Set G)
  let L := conjugateSpanBy K P
  let D := commutatorPreimage ⊤ Q V
  let : Q.Normal := pCore_normal
  let : C.Normal := inferInstance
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (commutatorPreimage_normalized ⊤ Q V ⊤
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal)
  have hLD : L ≤ D := conjugateSpanBy_le
    (le_commutatorPreimage le_top hKQ) le_normalizer_of_normal
  have hLQ : ⁅L, Q⁆ ≤ V := (commutator_mono hLD le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ Q V le_normalizer_of_normal)
  have hCQ : ⁅C, L⁆ ≤ Q :=
    (le_inf (commutator_le_left _ _)
      ((commutator_mono le_rfl hLD).trans (commutator_le_right _ _))).trans
      (two_layer_le_radical Q V Q hpV (pCore_quotient_pCore_eq_bot 2)
        (inf_le_right.trans hchar))
  have hQL : Q ≤ normalizer L := hQP.trans (le_normalizer_conjugateSpanBy K P)
  have hpL : IsPPerfect 2 L := conjugateSpan_twoPerfect K P hpK
  let X := L ⊔ Q
  have hLX : L ≤ X := le_sup_left
  let : (L.subgroupOf X).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hQL)
  have hpLX : IsPPerfect 2 (L.subgroupOf X) :=
    hpL.of_surjective (subgroupOfEquivOfLe hLX).symm.toMonoidHom
      (subgroupOfEquivOfLe hLX).symm.surjective
  have hres : (pResidual 2 X).map X.subtype = L := by
    rw [pResidual_eq_of_isPPerfect_sup (L.subgroupOf X) (Q.subgroupOf X)
      hpLX (pCore_isPGroup (p := 2) (G := G)).comap_subtype
      (codisjoint_subgroupOf_sup L Q).eq_top,
      map_subgroupOf_eq_of_le hLX]
  have hCX : C ≤ normalizer X :=
    le_normalizer_sup_of_commutator_le L C L Q le_rfl
      (by rwa [commutator_comm])
  have hCL : C ≤ normalizer L := by
    rw [← hres]
    exact hCX.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
  have hsup : (L ⊔ C).IsSubnormal := by
    have hh := himage.comap (QuotientGroup.mk' C)
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at hh
  have hsub : L.IsSubnormal := IsSubnormal.step L (L ⊔ C) le_sup_left hsup
    (normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hCL))
  refine ⟨hsub, ?_⟩
  rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact (commutator_mono (pCoreIn_le_of_subnormal 2 hsub) le_rfl).trans
    ((commutator_comm Q L).le.trans hLQ)


omit [Finite G] in
/-- The normal span inside a subnormal image is subnormal; the source
preimage and the original quotient map are retained. -/
public theorem conjugateSpan_preimage_image_subnormal
    {D : Type*} [Group D] (q : G →* D) (hq : Function.Surjective q)
    (K : Subgroup G) (B : Subgroup D) (hB : B.IsSubnormal) (hKB : K.map q ≤ B) :
    ((conjugateSpanBy K (B.comap q)).map q).IsSubnormal := by
  rw [map_conjugateSpanBy, map_comap_eq_self_of_surjective hq]
  have hRB : conjugateSpanBy (K.map q) B ≤ B := conjugateSpanBy_le_self hKB
  exact IsSubnormal.step _ B hRB hB
    (normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _))

/-- The exact C.1.27 lift after B.1.13 has supplied its actual component
(or central cubic subgroup) in G/C_G(V). This proves subnormality and the
required U-support without making the centralizer kernel a two-group. -/
public theorem lift_subnormal_quotient_block
    (V K : Subgroup G) [V.Normal] (hpV : IsPGroup 2 V)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hpK : IsPPerfect 2 K) (hQC : pCore 2 G ≤ centralizer (V : Set G))
    (hKQ : ⁅K, pCore 2 G⁆ ≤ V)
    (B : Subgroup (G ⧸ centralizer (V : Set G))) (hB : B.IsSubnormal)
    (hKB : K.map (QuotientGroup.mk' (centralizer (V : Set G))) ≤ B) :
    let L := conjugateSpanBy K (B.comap (QuotientGroup.mk' (centralizer (V : Set G))))
    K ≤ L ∧ IsPPerfect 2 L ∧ L.IsSubnormal ∧ (blockU L).map L.subtype ≤ V := by
  dsimp only
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  have hQP : pCore 2 G ≤ B.comap q := by
    intro x hx
    change q x ∈ B
    have he : q x = 1 := (QuotientGroup.eq_one_iff x).mpr (hQC hx)
    rw [he]
    exact B.one_mem
  obtain ⟨hs, hu⟩ := conjugateSpan_subnormal_of_centralizer_image V K (B.comap q)
    hpV hchar hpK hQP hKQ (conjugateSpan_preimage_image_subnormal q
      (QuotientGroup.mk'_surjective _) K B hB hKB)
  exact ⟨le_conjugateSpanBy K _, conjugateSpan_twoPerfect K _ hpK, hs, hu⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
