module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.BlockSection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The A₅ block quotient and its actual plus actor

The block model makes the action on U(K)/C_U(K) faithful. Since U(K) lies
inside W_K, the kernel of the component map lies in O₂(K). Conversely, the
explicit earlier-source trivial two-core assertion kills O₂(K) in K⁺.
The resulting actor equivalence and the literal block-section comparison
intertwine the quotient action, retaining componentMap on representatives.

This identifies only the quotient module. The parent module proves the
lifting to the full constituent required by the seed exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7–12,
printed pp.123–124, and 13.6.15–18, pp.930–931 (PDF pp.947–948).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection ComponentElimination.SourceTransferFields.RankOneBorel
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingBlock
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
local notation "W" => WK K L T z v
local notation "Kp" => plusImage K L T z v hL hz K
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v
local notation "C" => Submodule.comap (Submodule.subtype D) (Representation.invariants ρ)

omit [IsElementaryAbelian 2 (WK K L T z v)] in
/-- Faithfulness of the block section detects every element centralizing W_K. -/
theorem componentMap_ker_le_twoCore (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA)
    (hρA : ∀ (g : alternatingGroup (Fin 5)) (w : Multiplicative (BinaryPermutation.natural (Fin 5))),
      Multiplicative.toAdd (rhoA g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) g w.toAdd) :
    (componentMap K L T z v hL hz).ker ≤ pCore 2 K := by
  have hm := Replacement.MovingBlock.source_moving_eq_blockU K L T z v hL hz hK hn hW hb
  have hker : (componentMap K L T z v hL hz).ker =
      (centralizer (W : Set G)).subgroupOf K := by
    ext x
    change componentMap K L T z v hL hz x = 1 ↔ _
    rw [Subtype.ext_iff]
    change inclusion (K_le_plusActor K L T v) x ∈
      (plusMk K L T z v hL hz).ker ↔ _
    rw [plusMk_ker]
    rfl

  rw [hker]
  intro k hk
  have hcomm : ⁅W, K⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp
      ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))
  have hq : rhoA (model.quotientIso (QuotientGroup.mk' (pCore 2 K) k)) = 1 := by
    ext w
    obtain ⟨u, hu⟩ := model.moduleIso.surjective w
    obtain ⟨u0, hu0⟩ := QuotientGroup.mk'_surjective (blockFixed K) u
    rw [← hu, ← hu0]
    have hi := model.intertwining k u0
    have hu' : ((u0 : ChapterC.blockU K) : G) ∈ (blockU K).map K.subtype :=
      ⟨u0, u0.property, rfl⟩
    have hucomm : ((u0 : ChapterC.blockU K) : G) ∈ ⁅W, K⁆ := hm.symm ▸ hu'
    have huW : ((u0 : ChapterC.blockU K) : G) ∈ W := hcomm hucomm
    have hku : (k : G) * (u0 : ChapterC.blockU K) =
        (u0 : ChapterC.blockU K) * (k : G) :=
      (hk ((u0 : ChapterC.blockU K) : G) huW).symm
    have hblock : ChapterC.blockConjugate K k u0 = u0 := by
      apply Subtype.ext
      change (k : K) * (u0 : K) * (k : K)⁻¹ = u0
      apply Subtype.ext
      change (k : G) * (u0 : ChapterC.blockU K) * (k : G)⁻¹ = (u0 : ChapterC.blockU K)
      rw [hku, mul_inv_cancel_right]
    rw [hblock] at hi
    simpa using hi.symm
  have hnat : BinaryPermutation.naturalRepresentation (Fin 5)
      (model.quotientIso (QuotientGroup.mk' (pCore 2 K) k) : Equiv.Perm (Fin 5)) = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have hh := hρA (model.quotientIso (QuotientGroup.mk' (pCore 2 K) k))
      (Multiplicative.ofAdd w)
    rw [hq] at hh
    simpa using congrArg Subtype.val hh.symm
  have hqa : model.quotientIso (QuotientGroup.mk' (pCore 2 K) k) = 1 := by
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
    simpa using hnat
  have hmk : QuotientGroup.mk' (pCore 2 K) k = 1 :=
    model.quotientIso.injective (hqa.trans model.quotientIso.map_one.symm)
  exact (QuotientGroup.eq_one_iff k).mp hmk

omit [IsElementaryAbelian 2 (WK K L T z v)] in
/-- The earlier trivial two-core assertion kills the image of O₂(K). -/
theorem twoCore_le_componentMap_ker (hK : K ∈ ComponentSelection.Yz L T z v)
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    pCore 2 K ≤ (componentMap K L T z v hL hz).ker := by
  have hplus : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2
      (plusImage_K_subnormal K L T z v hL hz hK), hcore]
    change (plusImage K L T z v hL hz K).subtype.ker = ⊥
    exact (MonoidHom.ker_eq_bot_iff _).mpr
      (plusImage K L T z v hL hz K).subtype_injective
  have hmap : (pCore 2 K).map (componentMap K L T z v hL hz) ≤
      pCore 2 (plusImage K L T z v hL hz K) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _
      (componentMap_surjective K L T z v hL hz), pCore_isPGroup.map _⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hmap.trans hplus.le))

omit [IsElementaryAbelian 2 (WK K L T z v)] in
/-- The actual plus map has kernel O₂(K); this equality is proved, not assumed. -/
theorem componentMap_ker_eq_twoCore
    (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA)
    (hρA : ∀ (g : alternatingGroup (Fin 5)) (w : Multiplicative (BinaryPermutation.natural (Fin 5))),
      Multiplicative.toAdd (rhoA g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) g w.toAdd) :
    (componentMap K L T z v hL hz).ker = pCore 2 K := by
  apply le_antisymm
  · exact componentMap_ker_le_twoCore K L T z v hL hz hK hn hW hb rhoA model hρA
  · exact twoCore_le_componentMap_ker K L T z v hL hz hK hcore

/-- Identify K⁺ with the block actor through the kernel of componentMap. -/
noncomputable def actorEquiv
    (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA)
    (hρA : ∀ (g : alternatingGroup (Fin 5)) (w : Multiplicative (BinaryPermutation.natural (Fin 5))),
      Multiplicative.toAdd (rhoA g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) g w.toAdd) :
    Kp ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    (componentMap K L T z v hL hz) (componentMap_surjective K L T z v hL hz)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (componentMap_ker_eq_twoCore K L T z v hL hz hK hn hW hb hcore rhoA model hρA)).trans
      model.quotientIso)

/-- Coordinates on the literal moving quotient, through BlockModule K. -/
noncomputable def sectionCoordinates
    (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA) :
    (D ⧸ C) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) := by
  let e : Multiplicative (D ⧸ C) ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
    (sourceBlockSectionEquiv K L T z v hL hz hK hn hW hb).symm.trans model.moduleIso
  let a : (D ⧸ C) ≃+ BinaryPermutation.natural (Fin 5) := {
    toFun := fun x => Multiplicative.toAdd (e.toMonoidHom (Multiplicative.ofAdd (α := D ⧸ C) x))
    invFun := fun y => Multiplicative.toAdd (e.symm.toMonoidHom (Multiplicative.ofAdd (α := BinaryPermutation.natural (Fin 5)) y))
    left_inv := by
      intro x
      change Multiplicative.toAdd
        (e.symm.toMonoidHom (e.toMonoidHom (Multiplicative.ofAdd (α := D ⧸ C) x))) = x
      change Multiplicative.toAdd (e.symm (e (Multiplicative.ofAdd (α := D ⧸ C) x))) = x
      rw [e.symm_apply_apply]
      rfl
    right_inv := by
      intro y
      change Multiplicative.toAdd
        (e.toMonoidHom (e.symm.toMonoidHom (Multiplicative.ofAdd (α := BinaryPermutation.natural (Fin 5)) y))) = y
      change Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd (α := BinaryPermutation.natural (Fin 5)) y))) = y
      rw [e.apply_symm_apply]
      rfl
    map_add' := by
      intro x y
      rw [show Multiplicative.ofAdd (α := D ⧸ C) (x + y) =
        Multiplicative.ofAdd (α := D ⧸ C) x * Multiplicative.ofAdd (α := D ⧸ C) y by rfl,
        map_mul]
      rfl }
  exact a.toLinearEquiv (ZMod.map_smul a.toAddMonoidHom)

/-- The quotient coordinates intertwine the original plus action with A₅. -/
noncomputable def sectionActionEquiv
    (hK : K ∈ ComponentSelection.Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (rhoA : alternatingGroup (Fin 5) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 5))))
    (model : ChapterC.BlockModuleModel K rhoA)
    (hρA : ∀ (g : alternatingGroup (Fin 5)) (w : Multiplicative (BinaryPermutation.natural (Fin 5))),
      Multiplicative.toAdd (rhoA g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) g w.toAdd) :
    ActionEquiv (Replacement.Action.sectionRepresentation K L T z v hL hz)
      (alternatingNatural 5) where
  groupEquiv := actorEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
  linearEquiv := sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model
  intertwines := by
    intro a x
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz a
    let hm := Replacement.MovingBlock.source_moving_eq_blockU K L T z v hL hz hK hn hW hb
    let bs := sourceBlockSectionEquiv K L T z v hL hz hK hn hW hb
    obtain ⟨b, hbx⟩ := bs.surjective (Multiplicative.ofAdd x)
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (blockFixed K) b
    have hbu : bs (QuotientGroup.mk' (blockFixed K) u) = Multiplicative.ofAdd x := by
      rw [hu]
      exact hbx
    have hx : Multiplicative.toAdd (bs (QuotientGroup.mk' (blockFixed K) u)) = x :=
      congrArg Multiplicative.toAdd hbu
    rw [← hx]
    have hconj := Replacement.NaturalRecognition.blockSectionEquiv_conjugate
      K L T z v hL hz hm k u
    have hactor : actorEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
        (componentMap K L T z v hL hz k) =
        model.quotientIso (QuotientGroup.mk' (pCore 2 K) k) := by
      change model.quotientIso
        ((QuotientGroup.quotientMulEquivOfEq
          (componentMap_ker_eq_twoCore K L T z v hL hz hK hn hW hb hcore rhoA model hρA))
          ((QuotientGroup.quotientKerEquivOfSurjective
            (componentMap K L T z v hL hz)
            (componentMap_surjective K L T z v hL hz)).symm
            (componentMap K L T z v hL hz k))) =
        model.quotientIso (QuotientGroup.mk' (pCore 2 K) k)
      apply congrArg model.quotientIso
      let q := QuotientGroup.quotientKerEquivOfSurjective
        (componentMap K L T z v hL hz)
        (componentMap_surjective K L T z v hL hz)
      have hq : q.symm (componentMap K L T z v hL hz k) =
          QuotientGroup.mk' (componentMap K L T z v hL hz).ker k := by
        change q.symm (componentMap K L T z v hL hz k) =
          QuotientGroup.mk (k : K)
        apply q.injective
        rw [q.apply_symm_apply]
        rfl
      rw [hq]
      exact QuotientGroup.quotientMulEquivOfEq_mk
        (componentMap_ker_eq_twoCore K L T z v hL hz hK hn hW hb hcore rhoA model hρA) k
    change
      (sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model)
          (Replacement.Action.sectionRepresentation K L T z v hL hz
            (componentMap K L T z v hL hz k)
            (Multiplicative.toAdd (bs (QuotientGroup.mk' (blockFixed K) u)))) =
        (alternatingNatural 5)
          (actorEquiv K L T z v hL hz hK hn hW hb hcore rhoA model hρA
            (componentMap K L T z v hL hz k))
          ((sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model)
            (Multiplicative.toAdd (bs (QuotientGroup.mk' (blockFixed K) u))))
    have hcoord (u : ChapterC.blockU K) :
        (sectionCoordinates K L T z v hL hz hK hn hW hb rhoA model)
            (Multiplicative.toAdd (bs (QuotientGroup.mk' (blockFixed K) u))) =
          Multiplicative.toAdd (model.moduleIso (QuotientGroup.mk' (blockFixed K) u)) := by
      simp [sectionCoordinates, bs, sourceBlockSectionEquiv]
    have hconj' : Multiplicative.toAdd
        (bs (QuotientGroup.mk' (blockFixed K) (ChapterC.blockConjugate K k u))) =
        Replacement.Action.sectionRepresentation K L T z v hL hz
          (componentMap K L T z v hL hz k)
          (Multiplicative.toAdd (bs (QuotientGroup.mk' (blockFixed K) u))) := by
      simpa [bs, sourceBlockSectionEquiv] using hconj
    rw [← hconj']
    rw [hcoord (ChapterC.blockConjugate K k u), hcoord u]
    rw [model.intertwining, hactor, hρA]
    rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingBlock
end
