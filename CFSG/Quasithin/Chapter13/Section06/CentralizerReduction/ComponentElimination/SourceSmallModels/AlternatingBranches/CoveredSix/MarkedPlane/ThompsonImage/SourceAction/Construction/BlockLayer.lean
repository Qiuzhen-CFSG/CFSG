module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.SourceLine
public import Theory.Representation.HexacodeAction.TerminalIrreducible

/-!
# The original block layer inside the plus module

The marked commutator [V,Lᵥ] has order four and lies in both U(K) and W_K.
Transporting their intersection through the prescribed hexacode coordinates
and using even irreducibility gives U(K)≤W_K. Characteristicness makes U(K)
invariant under KTᵥ, so its conjugation action descends through the original
plus quotient, with the original ambient and component equations.

The two-group input for Uᵥ is the consequence of Uᵥ∈R₂(Gᵥ) on printed p.928.
The normalization and containment inputs are 13.6.14 and 13.6.20; the marked
central seed is the setup on p.926. No faithfulness of the descended action
is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926–932, especially the paragraph before 13.6.14 and 13.6.22.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L V T : Subgroup G}
variable (s : A5Module.Marking L V) (h : IsExceptionalAhat6Block K)
  [IsElementaryAbelian 2 (blockU K)] (m : HexacodeModel h)

include h m in
/-- The nonzero marked commutator forces the entire irreducible block layer into W_K. -/
theorem blockU_le_WK
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (hzT : markedZ s ∈ Tv T (markedV s))
    (hU : IsPGroup 2 (Uv (markedZ s) (markedV s)))
    (hLK : Lv L (markedV s) ≤ K) :
    (blockU K).map K.subtype ≤ WK K L T (markedZ s) (markedV s) := by
  let W := WK K L T (markedZ s) (markedV s)
  have hKW : K ≤ normalizer (W : Set G) :=
    (K_le_plusActor K L T (markedV s)).trans
      (plusActor_normalizes_WK K L T (markedZ s) (markedV s) hL hz)
  let j : blockU K →* G := K.subtype.comp (blockU K).subtype
  let P : Submodule (ZMod 2) (Additive (blockU K)) :=
    AddSubgroup.toZModSubmodule 2 (W.comap j).toAddSubgroup
  have hP (a : K ⧸ pCore 2 K) (u : Additive (blockU K)) (hu : u ∈ P) :
      binaryAction h a u ∈ P := by
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
    change (((binaryAction h (QuotientGroup.mk' (pCore 2 K) k) u).toMul : K) : G) ∈ W
    rw [binaryAction_apply]
    exact (mem_normalizer_iff.mp (hKW k.property) _).mp hu
  let Q : Subrepresentation Hexacode.evenAction :=
    ⟨P.map m.coordinates.toLinearMap, by
      rintro a _ ⟨u, hu, rfl⟩
      obtain ⟨b, rfl⟩ := m.quotientIso.surjective a
      exact ⟨binaryAction h b u, hP b u hu, m.intertwining b u⟩⟩
  have hlineU := source_commutator_le_block s K T h hK hn hzT hU hLK
  have hlineW : ⁅V, Lv L (markedV s)⁆ ≤ W := by
    rw [source_commutator_eq_seed s]
    apply (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
    exact le_normalizer_iff_commutator_le_left.mp
      ((show Lv L (markedV s) ≤ plusActor K L T (markedV s) from
        le_sup_of_le_left le_sup_right).trans
          (plusActor_normalizes_WK K L T (markedZ s) (markedV s) hL hz))
  have hline_ne : ⁅V, Lv L (markedV s)⁆ ≠ ⊥ := by
    intro he
    have hc := source_commutator_card s
    rw [he, Subgroup.card_bot] at hc
    omega
  rcases Hexacode.evenAction_isIrreducible.eq_bot_or_eq_top Q with hbot | htop
  · have := (Subgroup.nontrivial_iff_ne_bot _).mpr hline_ne
    obtain ⟨x, hx, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial ⁅V, Lv L (markedV s)⁆
    obtain ⟨u, hu, rfl⟩ := hlineU hx
    let w : Additive (blockU K) := Additive.ofMul ⟨u, hu⟩
    have hw : m.coordinates w ∈ Q := ⟨w, hlineW hx, rfl⟩
    rw [hbot] at hw
    have hw0 : w = 0 := m.coordinates.map_eq_zero_iff.mp hw
    exact (hx1 (congrArg (fun t : Additive (blockU K) => ((t.toMul : K) : G)) hw0)).elim
  · rintro x ⟨u, hu, rfl⟩
    let w : Additive (blockU K) := Additive.ofMul ⟨u, hu⟩
    have hw : m.coordinates w ∈ Q := by rw [htop]; trivial
    obtain ⟨w', hw', he⟩ := hw
    have hwP : w ∈ P := m.coordinates.injective he ▸ hw'
    exact hwP

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G] {K L T : Subgroup G} {z v : G}

/-- After 13.6.14 and 13.6.20, the literal plus actor is KTᵥ. -/
theorem plusActor_eq (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K) :
    plusActor K L T v = K ⊔ Tv T v := by
  rw [plusActor, Kminus_eq_of_invariant K T v hn, sup_eq_left.mpr hLK]

/-- The characteristic block layer is invariant under the full original actor. -/
theorem plusActor_normalizes_block (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) :
    plusActor K L T v ≤ normalizer ((blockU K).map K.subtype : Set G) := by
  rw [plusActor_eq hn hLK]
  exact (sup_le K.le_normalizer hn).trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))

/-- Conjugation on the intrinsic block, transported through its injective ambient inclusion. -/
noncomputable def blockConjugation (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) : plusActor K L T v →* MulAut (blockU K) :=
  (MulAut.congr ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm).toMonoidHom.comp
    (conjugationAction ((blockU K).map K.subtype) (plusActor K L T v)
      (plusActor_normalizes_block hn hLK))

/-- The transported action is still the original ambient conjugation. -/
theorem blockConjugation_apply (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (g : plusActor K L T v) (u : blockU K) :
    (((blockConjugation hn hLK g u : blockU K) : K) : G) =
      (g : G) * ((u : K) : G) * (g : G)⁻¹ := by
  let e := (blockU K).equivMapOfInjective K.subtype K.subtype_injective
  change (e (e.symm (conjugationAction _ _ _ g (e u))) : G) = _
  rw [e.apply_symm_apply]
  rfl

variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hUW : (blockU K).map K.subtype ≤ WK K L T z v)

include hUW in
/-- Containment in W_K makes its centralizer act trivially on the block. -/
theorem plusKernel_le_blockKernel :
    (plusConjugation K L T z v hL hz).ker ≤ (blockConjugation hn hLK).ker := by
  rw [plusConjugation_ker]
  intro g hg
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  rw [blockConjugation_apply]
  change (g : G) * ((u : K) : G) * (g : G)⁻¹ = ((u : K) : G)
  have hc : ((u : K) : G) * (g : G) = (g : G) * ((u : K) : G) :=
    hg _ (hUW (mem_map_of_mem K.subtype u.property))
  rw [← hc, mul_inv_cancel_right]

/-- Descend block conjugation through the literal plus quotient. -/
noncomputable def blockPlusAut : Gplus K L T z v hL hz →* MulAut (blockU K) :=
  QuotientGroup.lift _ (blockConjugation hn hLK) (plusKernel_le_blockKernel hL hz hn hLK hUW)

variable [IsElementaryAbelian 2 (blockU K)]
/-- The full plus representation on Additive U(K). -/
noncomputable def blockPlusRepresentation :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive (blockU K)) where
  toFun g := (blockPlusAut hL hz hn hLK hUW g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (blockPlusAut hL hz hn hLK hUW 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (blockPlusAut hL hz hn hLK hUW (a * b) u.toMul) = _
    rw [map_mul]
    rfl

/-- Plus representatives act by their original ambient conjugation. -/
theorem blockPlusRepresentation_apply (g : plusActor K L T v) (u : Additive (blockU K)) :
    (((blockPlusRepresentation hL hz hn hLK hUW (plusMk K L T z v hL hz g) u).toMul : K) : G) =
      (g : G) * ((u.toMul : K) : G) * (g : G)⁻¹ :=
  blockConjugation_apply hn hLK g u.toMul

variable (h : IsExceptionalAhat6Block K)
    (f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz)
    (hf : ∀ k : K, f (QuotientGroup.mk' (pCore 2 K) k) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))

include hf in
/-- The prescribed component map recovers the original core-quotient action. -/
theorem blockPlusRepresentation_component (a : K ⧸ pCore 2 K) (u : Additive (blockU K)) :
    blockPlusRepresentation hL hz hn hLK hUW (f a) u = binaryAction h a u := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
  rw [hf]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [blockPlusRepresentation_apply, binaryAction_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
