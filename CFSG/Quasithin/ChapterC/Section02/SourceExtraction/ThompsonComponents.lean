module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CentralModule

/-!
# Thompson subgroups normalize surviving quasisimple components

Pass through the actual two-core quotient, where the given C-component is
quasisimple, and then through the centralizer of the normal elementary
module. Nontrivial action makes the component survive. Every nontrivial
maximum-elementary image is a best offender, so source B.1.5(4) normalizes
that component image. Ordinary component calculus and the C-component
quotient-normalizer theorem lift this normalization back to the original
component.

The final theorem applies this argument to the literal Ω₁Z(O₂(G)) constructed
from a radical subgroup and characteristic-normalizer control. It retains
the ambient characteristic-two hypothesis of Aschbacher's source theorem;
the more general C.2.4 extraction is not asserted here.

Source: Aschbacher, *Pushing-up in finite groups*, Math. Z. 177 (1981),
10.3, printed p.78; Aschbacher--Smith, B.1.5(4), B.2.5 and C.2.4.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

private theorem thompson_image_le_normalizer_component
    {H : Type*} [Group H] [Finite H]
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    {K : Subgroup H} (hK : IsComponent H K) :
    (Stellmacher.elementaryAbelianMaxJ R).map q ≤ normalizer (K : Set H) := by
  classical
  let ρ : Representation (ZMod 2) H (Additive V) :=
    Representation.NormalElementaryQuotient.representation V q hq hker
  have hf : Function.Injective ρ :=
    Representation.NormalElementaryQuotient.representation_injective V q hq hker
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hbot : A.map q = ⊥
  · rw [hbot]; exact bot_le
  · have hbest : Representation.BinaryOffender.IsBestOffender ρ (A.map q) :=
      Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        V q hq hker R A hVR hA hbot
    exact ChapterB.source_lemma_B_1_5_4 (G := H) (V := Additive V)
      (A := A.map q) (L := K) ρ hf hbest hK

/-- A normal elementary module forces its maximum-elementary Thompson family
to normalize each noncentral C-component with quasisimple two-core quotient. -/
theorem thompson_le_component_normalizer
    (V R L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hcore : pCore 2 G ≤ centralizer (V : Set G))
    (hmove : ¬ L ≤ centralizer (V : Set G)) :
    Stellmacher.elementaryAbelianMaxJ R ≤ normalizer (L : Set G) := by
  classical
  let C := centralizer (V : Set G)
  let q := QuotientGroup.mk' C
  let q₂ := QuotientGroup.mk' (pCore 2 G)
  have hker : q.ker = centralizer (V : Set G) := QuotientGroup.ker_mk' C
  let π : (G ⧸ pCore 2 G) →* G ⧸ C := QuotientGroup.lift (pCore 2 G) q (by
    exact hker.symm ▸ hcore)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C y
    exact ⟨q₂ g,rfl⟩
  have hcomp : π.comp q₂ = q := by ext; rfl
  have hmap : (L.map q₂).map π = L.map q := by rw [map_map,hcomp]
  have hne : (L.map q₂).map π ≠ ⊥ := by
    rw [hmap]
    intro he
    exact hmove (hker ▸ (Subgroup.map_eq_bot_iff L).mp he)
  have hL₂ : IsComponent (G ⧸ pCore 2 G) (L.map q₂) :=
    ⟨hL.subnormal.quotient, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)⟩
  have hLq : IsComponent (G ⧸ C) (L.map q) := by
    rw [← hmap]
    exact (hL₂.map_surjective π hπ).resolve_left hne
  have hJq := thompson_image_le_normalizer_component V R hVR q
    (QuotientGroup.mk'_surjective C) hker hLq
  let := pCore_isNilpotent (p := 2) (G := G)
  intro a ha
  rw [← normalizer_cComponent_quotient hL (pCore 2 G)]
  apply hL₂.mem_normalizer_of_mem_normalizer_map π hne
  change q a ∈ normalizer ((L.map q₂).map π : Set (G ⧸ C))
  rw [hmap]
  exact hJq (mem_map_of_mem q ha)

/-- The literal characteristic-two pushing-up application. -/
theorem thompson_le_component_normalizer_of_characteristicTwo
    (R M L : Subgroup G) (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ L ≤ M)
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)] :
    Stellmacher.elementaryAbelianMaxJ R ≤ normalizer (L : Set G) := by
  let := radicalCentralModule_normal (G := G)
  let := radicalCentralModule_elementary (G := G)
  exact thompson_le_component_normalizer (radicalCentralModule (G := G)) R L
    (radicalCentralModule_le hr) hL core_centralizes_radicalCentralModule
    (outside_moves_radicalCentralModule hr hc hcontrol hout)

end CFSG.Quasithin.ChapterC.Section02Source
