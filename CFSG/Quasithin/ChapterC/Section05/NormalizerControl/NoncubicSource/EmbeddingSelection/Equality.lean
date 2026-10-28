module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Kernel
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Lifting equality of the original component images

The auxiliary two-core lies in the original Sylow, so it normalizes K.
Equality modulo that core puts the perfect normal closure L inside K·O₂(N).
A two-perfect subgroup cannot acquire containment merely by adjoining a
two-group, giving L=K on the original ambient subgroups.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem twoPerfect_le_of_join (B K R : Subgroup G)
    (hB : IsPPerfect 2 B) (hR : IsPGroup 2 R)
    (hn : R ≤ normalizer (K : Set G)) (hb : B ≤ K ⊔ R) : B ≤ K := by
  let J := K ⊔ R
  let : (K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hg : K.subgroupOf J ⊔ R.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hh := le_normal_of_isPPerfect_of_le_sup_pGroup (B.subgroupOf J)
    (K.subgroupOf J) (R.subgroupOf J)
    (hB.of_surjective (subgroupOfEquivOfLe hb).symm.toMonoidHom
      (subgroupOfEquivOfLe hb).symm.surjective) hR.comap_subtype (hg ▸ le_top)
  intro b h
  exact hh (show (⟨b,hb h⟩ : J) ∈ B.subgroupOf J from h)

theorem source_eq_of_twoCore_image_eq (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hL : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      ((conjugateSpanBy K N).subgroupOf N).IsCComponent)
    (heq : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let r := QuotientGroup.mk' (pCore 2 N)
      (K.subgroupOf N).map r = ((conjugateSpanBy K N).subgroupOf N).map r) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  obtain ⟨Q,hQ⟩ := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS).2.2
  let D := (pCore 2 N).map N.subtype
  have hDT : D ≤ T := hQ ▸ pCoreIn_le_sylow N Q
  have hDK : D ≤ normalizer (K : Set G) := hDT.trans hTK
  have hLsup : L ≤ K ⊔ D := by
    have hi : L.subgroupOf N ≤ K.subgroupOf N ⊔ pCore 2 N := by
      have hm := map_le_iff_le_comap.mp heq.symm.le
      simpa only [comap_map_eq,QuotientGroup.ker_mk'] using hm
    have hm := map_mono (f := N.subtype) hi
    rwa [map_subgroupOf_eq_of_le hLN,Subgroup.map_sup,map_subgroupOf_eq_of_le hKN] at hm
  let : Group.IsPerfect (L.subgroupOf N) := hL.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLN).toMonoidHom) (subgroupOfEquivOfLe hLN).surjective
  have hperfect : IsPPerfect 2 L := by
    intro H hH hq
    let : H.Normal := hH
    by_contra hne
    let : Nontrivial (L ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (L ⧸ H) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
    let : Group.IsNilpotent (L ⧸ H) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (L ⧸ H) inferInstance
  exact le_antisymm (twoPerfect_le_of_join L K D hperfect (pCore_isPGroup.map N.subtype) hDK hLsup)
    (le_conjugateSpanBy K N)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
