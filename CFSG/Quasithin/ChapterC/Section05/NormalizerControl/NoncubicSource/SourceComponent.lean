module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AuxiliaryModule
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AmbientImage
/-!
# The C.5.12 auxiliary image is an actual component

The original full module contains U(L), and L/U(L) is quasisimple. Its
nontrivial action image L* is consequently quasisimple, while the source
normalizer-image identity makes it normal in C(P₁*). This gives an actual
component of that centralizer with the literal larger quotient X/C_X(V).
The auxiliary short-block premise is discharged by the original consumers.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
private theorem quotient_quasisimple_of_perfect {A : Type*} [Group A]
    (h : IsShort A) [Group.IsPerfect A] : IsQuasisimple (A ⧸ pCore 2 A) := by
  let := h.finite
  apply h.quotient.resolve_right
  intro hc
  let : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hc
  let : CommGroup (A ⧸ pCore 2 A) := IsMulCommutative.instCommGroup
  let : Nontrivial (A ⧸ pCore 2 A) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  let : Group.IsPerfect (A ⧸ pCore 2 A) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative (A ⧸ pCore 2 A) inferInstance

theorem noncubic_auxiliary_image_isComponent
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G)) (hUV : U K ≤ V)
    [IsElementaryAbelian 2 V]
    (hL : IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)))) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    let C := centralizer ((((K ⊔ T).pCoreIn 2).subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X)))
    let B := (L.subgroupOf X).map q
    B ≤ C ∧ IsComponent C (B.subgroupOf C) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let C := centralizer ((((K ⊔ T).pCoreIn 2).subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X)))
  let B := (L.subgroupOf X).map q
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have hLX : L ≤ X := (conjugateSpanBy_le_self hKN).trans inf_le_left
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let : Group.IsPerfect K := BlockCommutation.perfect_of_quasisimple_quotient hK.chi.short
  let : Group.IsPerfect L := conjugateSpanBy_isPerfect K N
  let : IsQuasisimple (L ⧸ pCore 2 L) := quotient_quasisimple_of_perfect hL
  have hUL := noncubic_auxiliary_blockU_le_source_module K T X V hK h3 hT hUT hTK P hP hA hAX S hS hXV hUV
  let : IsQuasisimple B := short_centralizer_image_quasisimple L X V hL hLX hVX hXV hUL
  have hn := noncubic_source_auxiliary_centralizer_normal K T X V hK h3 hT hTK P hP S hS hAX hVX hXV hUV
  exact ⟨hn.1,hn.2.isSubnormal,IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hn.1).symm⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
