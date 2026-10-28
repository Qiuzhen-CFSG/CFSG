module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction.BlockLayer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer

/-!
# Faithfulness and the full covered-six embedding

The component map has the literal K⁺ as its normal image. Its quotient is a
two-group, using the actual Sylow witness in the local family. The kernel of
the block action intersects this component trivially, hence embeds in that
two-group quotient. The earlier R₂ consequence O₂(G⁺)=1 kills the kernel.

In the prescribed coordinates every full-group operator normalizes the even
hexacode image. The exact binary-normalizer theorem then constructs an
injective map into the full hexacode automorphism group. Both the prescribed
component equation and conjugation on the original U(K) are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the R₂
paragraph before 13.6.14 (printed p.929) and the covered-six paragraph of
13.6.22 (p.932). The imported normalizer calculation retains its licensed
ATLAS-derived carrier and attribution.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G] {K L T : Subgroup G} {z v : G}
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
include hf
/-- The prescribed core map has precisely the literal plus image of K as its range. -/
theorem component_range : f.range = plusImage K L T z v hL hz K := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
    rw [hf]
    exact mem_map_of_mem _ k.property
  · rintro ⟨k, hk, rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 K) ⟨k, hk⟩, hf ⟨k, hk⟩⟩

/-- Tᵥ-invariance and Lᵥ≤K make that actual component image normal. -/
theorem component_range_normal (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) : f.range.Normal := by
  rw [component_range hL hz f hf]
  have hKN : (K.subgroupOf (plusActor K L T v)).Normal :=
    normal_subgroupOf_of_le_normalizer (by rw [plusActor_eq hn hLK]; exact sup_le K.le_normalizer hn)
  exact hKN.map _ (plusMk_surjective K L T z v hL hz)

/-- The component and the actual Tᵥ-image generate the full plus quotient. -/
theorem component_range_sup (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) : f.range ⊔ plusImage K L T z v hL hz (Tv T v) = ⊤ := by
  rw [component_range hL hz f hf]
  change (K.subgroupOf (plusActor K L T v)).map (plusMk K L T z v hL hz) ⊔
    ((Tv T v).subgroupOf (plusActor K L T v)).map (plusMk K L T z v hL hz) = ⊤
  rw [← Subgroup.map_sup, ← subgroupOf_sup (K_le_plusActor K L T v) le_sup_right,
    ← plusActor_eq hn hLK, subgroupOf_self,
    map_top_of_surjective _ (plusMk_surjective K L T z v hL hz)]

/-- The source Sylow witness makes the quotient by the component a two-group. -/
theorem component_quotient_isPGroup
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hK : K ∈ Yz L T z v) :
    let := component_range_normal hL hz f hf hn hLK
    IsPGroup 2 (Gplus K L T z v hL hz ⧸ f.range) := by
  let := component_range_normal hL hz f hf hn hLK
  have ht : IsPGroup 2 (Tv T v) := by
    obtain ⟨P, hP⟩ := hK.1.2.2.1
    rw [← hP]
    exact P.isPGroup'.map (K ⊔ Tv T v).subtype
  exact isPGroup_quotient_of_sup_eq_top f.range _
    (ht.comap_subtype.map (plusMk K L T z v hL hz))
    (component_range_sup hL hz f hf hn hLK)

variable [IsElementaryAbelian 2 (blockU K)] (h : IsExceptionalAhat6Block K)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hUW : (blockU K).map K.subtype ≤ WK K L T z v)
include h in
/-- The kernel embeds in the two-group quotient and therefore lies in the trivial two-core. -/
theorem blockPlusRepresentation_injective
    (hK : K ∈ Yz L T z v) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    Function.Injective (blockPlusRepresentation hL hz hn hLK hUW) := by
  let ρ := blockPlusRepresentation hL hz hn hLK hUW
  let := component_range_normal hL hz f hf hn hLK
  let q := (QuotientGroup.mk' f.range).comp ρ.ker.subtype
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro x hx
    have hxR : (x : Gplus K L T z v hL hz) ∈ f.range := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨a, ha⟩ := hxR
    have he : binaryAction h a = 1 := by
      apply LinearMap.ext
      intro u
      rw [← blockPlusRepresentation_component hL hz hn hLK hUW h f hf]
      change ρ (f a) u = u
      rw [ha, show ρ (x : Gplus K L T z v hL hz) = 1 from x.property]
      rfl
    have ha1 : a = 1 := binaryAction_injective h (he.trans (binaryAction h).map_one.symm)
    apply Subtype.ext
    change (x : Gplus K L T z v hL hz) = 1
    simpa only [ha1, map_one] using ha.symm
  have hp : IsPGroup 2 ρ.ker :=
    (component_quotient_isPGroup hL hz f hf hn hLK hK).of_injective q hq
  apply ρ.ker_eq_bot_iff.mp
  exact le_bot_iff.mp ((show ρ.ker ≤ pCore 2 (Gplus K L T z v hL hz) from
    le_sSup ⟨inferInstance, hp⟩).trans_eq hcore)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
open Atlas.Codes Hexacode.SixDimensional
variable {G : Type*} [Group G] {K L T : Subgroup G} {z v : G}
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)] (m : HexacodeModel h)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))

include hf in
/-- The exact binary normalizer constructs the full embedding, retaining the prescribed even coordinates. -/
theorem nonempty_plusBlockModel_of_block_le
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hUW : (blockU K).map K.subtype ≤ WK K L T z v)
    (hK : K ∈ Yz L T z v) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    Nonempty (PlusBlockModel K L T z v h hL hz m f) := by
  let ρ := blockPlusRepresentation hL hz hn hLK hUW
  have hρ := blockPlusRepresentation_injective hL hz f hf h hn hLK hUW hK hcore
  let c := coordinateAction ρ m.coordinates
  have hc (a : K ⧸ pCore 2 K) : c (f a) = hexAction (m.quotientIso a).val := by
    apply LinearEquiv.ext
    intro u
    change m.coordinates (ρ (f a) (m.coordinates.symm u)) = _
    rw [blockPlusRepresentation_component hL hz hn hLK hUW h f hf,
      m.intertwining, m.coordinates.apply_symm_apply]
    rfl
  have himage : f.range.map c = evenBinaryImage := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨m.quotientIso a, (hc a).symm⟩
    · rintro _ ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := m.quotientIso.surjective a
      exact ⟨f b, ⟨b, rfl⟩, hc b⟩
  let := component_range_normal hL hz f hf hn hLK
  have hmem (g : Gplus K L T z v hL hz) : c g ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    exact le_normalizer_map c ⟨g, by rw [f.range.normalizer_eq_top]; trivial, rfl⟩
  let j := c.codRestrict hexAction.range hmem
  let e : Gplus K L T z v hL hz →* HexAutomorphisms :=
    (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have he (g : Gplus K L T z v hL hz) : hexAction (e g) = c g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  refine ⟨{ embedding := e, injective := ?_, component := ?_, conjugation := ?_ }⟩
  · intro a b hab
    apply coordinateAction_injective ρ m.coordinates hρ
    rw [← he, ← he, hab]
  · intro a
    apply hexAction_injective
    rw [he, hc]
  · intro g u
    have ha : m.coordinates.symm (Hexacode.action (e (plusMk K L T z v hL hz g))
        (m.coordinates u)) = ρ (plusMk K L T z v hL hz g) u := by
      apply m.coordinates.injective
      rw [m.coordinates.apply_symm_apply]
      have hh := LinearEquiv.congr_fun (he (plusMk K L T z v hL hz g)) (m.coordinates u)
      change Hexacode.action (e (plusMk K L T z v hL hz g)) (m.coordinates u) =
        m.coordinates (ρ (plusMk K L T z v hL hz g) (m.coordinates.symm (m.coordinates u))) at hh
      simpa only [m.coordinates.symm_apply_apply] using hh
    rw [ha]
    exact blockPlusRepresentation_apply hL hz hn hLK hUW g u
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
