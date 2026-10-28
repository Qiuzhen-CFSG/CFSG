module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicBlockNormal.Core
public import Theory.GroupTheory.CubicTwoLayerNormality

/-!
# The A₃ auxiliary alternative in C.5.13

The auxiliary normalizer preserves the original four-group U. Its two-core
is P₁, and the original block fixes P₁/U. The two-layer kernel lies in P₁;
the cubic image in Aut(U), of order six, is normal. Thus KP₁ is normal,
and its characteristic two-residual is K. The actual conjugate span L
therefore equals K.

Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The actual X₁ normalizes K₁ in the A₃ branch of C.5.13. The
characteristic-two hypothesis on X is supplied by C.5.10. -/
theorem alternating_three_source_normalizes_block
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hX : X ∈ Chapter1.He G)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G) ≤ normalizer (K : Set G) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hUN : U K ≤ N := (map_subtype_le _).trans hKN
  have hNU := alternating_three_source_normalizes_module h ha hT hTK P hP hA X hAX PX hPX hx hnc
  have hcore := alternating_three_auxiliary_core h ha hT hTK P hP X hAX PX hPX hNU
  have hN : N ∈ Chapter1.He G := Chapter1.normalizer_mem_He_of_isPGroup hX
    (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAX)
  let Ui := (U K).subgroupOf N
  let Ki := K.subgroupOf N
  let : Ui.Normal := (normal_subgroupOf_iff_le_normalizer hUN).mpr hNU
  let : IsElementaryAbelian 2 (U K) := h.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.subgroupOf hUN
  have hcard : Nat.card Ui = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv).trans (h.cubic_module_card ha)
  have hself : centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
    intro n hn
    have hc : (n : G) ∈ centralizer (N.pCoreIn 2 : Set G) := by
      rintro _ ⟨q,hq,rfl⟩
      exact congrArg N.subtype (hn q hq)
    obtain ⟨q,hq,he⟩ := hN ⟨n.property,hc⟩
    exact (Subtype.ext he : q=n) ▸ hq
  have hcoreT : A.pCoreIn 2 ≤ T := hP ▸ pCoreIn_le_sylow A P
  have hcoreC : A.pCoreIn 2 ≤ centralizer (U K : Set G) := by
    rw [← CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer K T h.short hT hTK]
    exact inf_le_right
  have hd : ⁅Ki,pCore 2 N⁆ ≤ Ui := by
    have hh := block_fixer_displacement h.short (hcoreT.trans hTK) hcoreC
    intro n hn
    have hm : (n : G) ∈ ⁅K,A.pCoreIn 2⁆ := by
      have hm := mem_map_of_mem N.subtype hn
      rw [map_commutator,map_subgroupOf_eq_of_le hKN] at hm
      change (n : G) ∈ ⁅K,N.pCoreIn 2⁆ at hm
      rwa [hcore] at hm
    exact hh hm
  have himage : Nat.card (Ki.map (MulAut.conjNormal : N →* MulAut Ui)) = 3 := by
    have hh := alternating_three_quotient_image_card K T N (U K) ha hTK hAN hUN hNU le_rfl hcoreC
    rw [← relIndex_ker,MulAut.conjNormal_ker_eq_centralizer]
    simpa only [← relIndex_ker,QuotientGroup.ker_mk'] using hh
  let : (Ki ⊔ pCore 2 N).Normal := Theory.GroupTheory.cubic_join_core_normal Ki Ui hcard hself hd himage
  have hj : (Ki ⊔ pCore 2 N).map N.subtype = K ⊔ A.pCoreIn 2 := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKN]
    exact congrArg (K ⊔ ·) hcore
  have hnorm : N ≤ normalizer ((K ⊔ A.pCoreIn 2 : Subgroup G) : Set G) := by
    have hh := (Ki ⊔ pCore 2 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype,hj] using hh
  have he := CounterexampleCharacteristic.normal_extension_residual K (A.pCoreIn 2)
    h.short.twoPerfect (isPGroup_pCoreIn 2 A) (hcoreT.trans hTK)
  have hh := hnorm.trans (normalizer_le_normalizer_characteristic_image
    (K ⊔ A.pCoreIn 2) (pResidual 2 (K ⊔ A.pCoreIn 2 : Subgroup G)))
  rwa [he] at hh
/-- The literal auxiliary group L=⟨K₁ˣ : x∈N_X(P₁)⟩ is K₁.
This is alternative (1) of C.5.13 in the A₃ branch. -/
theorem alternating_three_source_auxiliary_eq_block
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (hX : X ∈ Chapter1.He G)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K := by
  exact le_antisymm (conjugateSpanBy_le le_rfl
    (alternating_three_source_normalizes_block h ha hT hTK P hP hA X hAX hX PX hPX hx hnc))
    (le_conjugateSpanBy _ _)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
