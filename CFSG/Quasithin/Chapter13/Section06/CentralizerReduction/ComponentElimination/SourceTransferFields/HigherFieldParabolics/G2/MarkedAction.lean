module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.ElementaryAbelian.VectorSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules

/-!
# The literal moved quotient and marked G₂ action

Convert the actual plus action on W_K to a binary representation and restrict
it to K⁺. Its moved space embeds as [W_K,K], hence as the source U_K after
13.6.14. The quotient map has precisely the fixed subspace as kernel; in the
original group its vectors commute with every element of K.

An action identification on this quotient supplies both the group marking
and the octonion coordinates. Sylow alignment conjugates these together.
The parabolic application retains that intertwiner and derives movement of z
from Y_z and T_v-invariance. It still assumes the natural identification and
the two-group property of the relative action kernel. Constructing those from
the full B.5 and earlier ambient hypotheses remains a source obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
preceding 13.6.14, 13.6.14 and 13.6.19, printed pp.929–931; B.5.1/B.5.6.
The octonion quotient action is the existing attributed ATLAS construction
in Theory/Representation/G2Natural.lean. No upstream source is copied.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction
open ComponentSelection ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- The binary form of the literal faithful plus action on W_K. -/
def representation : Representation (ZMod 2) (Gplus K L T z v hL hz)
    (Additive (WK K L T z v)) where
  toFun x := (plusAction K L T z v hL hz x).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul ((plusAction K L T z v hL hz 1) w.toMul) = w
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul ((plusAction K L T z v hL hz (x * y)) w.toMul) = _
    rw [map_mul]
    rfl

theorem representation_injective : Function.Injective (representation K L T z v hL hz) := by
  intro x y h
  apply plusAction_injective K L T z v hL hz
  apply MulEquiv.ext
  intro w
  exact congrArg Additive.toMul
    (congrArg (fun f : Module.End (ZMod 2) (Additive (WK K L T z v)) =>
      f (Additive.ofMul w)) h)

/-- Restriction to the actual subgroup K⁺, rather than an abstract G₂ copy. -/
def componentRepresentation :=
  (representation K L T z v hL hz).comp (plusImage K L T z v hL hz K).subtype

theorem componentRepresentation_injective :
    Function.Injective (componentRepresentation K L T z v hL hz) :=
  (representation_injective K L T z v hL hz).comp
    (plusImage K L T z v hL hz K).subtype_injective

theorem componentRepresentation_apply (k : K) (w : Additive (WK K L T z v)) :
    ((componentRepresentation K L T z v hL hz (componentMap K L T z v hL hz k) w).toMul : G) =
      (k : G) * (w.toMul : G) * (k : G)⁻¹ := rfl

/-- Put a binary subspace back into its original ambient group. -/
def ambientSpace (U : Submodule (ZMod 2) (Additive (WK K L T z v))) : Subgroup G :=
  U.toAddSubgroup.toSubgroup'.map (WK K L T z v).subtype

/-- The linear moved space is exactly the source commutator [W_K,K]. -/
theorem moved_ambientSpace :
    ambientSpace K L T z v (moved (componentRepresentation K L T z v hL hz) ⊤) =
      ⁅WK K L T z v, K⁆ := by
  let C := ⁅WK K L T z v, K⁆
  let Cspace : Submodule (ZMod 2) (Additive (WK K L T z v)) :=
    AddSubgroup.toZModSubmodule (n := 2) ((C.comap (WK K L T z v).subtype).toAddSubgroup)
  have hspan : moved (componentRepresentation K L T z v hL hz) ⊤ ≤ Cspace := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, _, w, _, rfl⟩
    obtain ⟨k, rfl⟩ := componentMap_surjective K L T z v hL hz a
    change ((componentRepresentation K L T z v hL hz
      (componentMap K L T z v hL hz k) w).toMul : G) / (w.toMul : G) ∈ C
    rw [componentRepresentation_apply, div_eq_mul_inv]
    exact (commutator_comm _ _).le (commutator_mem_commutator k.property w.toMul.property)
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hspan hw
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk w hw
    let d := componentRepresentation K L T z v hL hz
      (componentMap K L T z v hL hz ⟨k, hk⟩) (Additive.ofMul ⟨w, hw⟩) -
        Additive.ofMul ⟨w, hw⟩
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ moved (componentRepresentation K L T z v hL hz) ⊤
      exact Submodule.subset_span ⟨componentMap K L T z v hL hz ⟨k, hk⟩,
        mem_top _, Additive.ofMul ⟨w, hw⟩, Submodule.mem_top, rfl⟩
    · change ((componentRepresentation K L T z v hL hz
        (componentMap K L T z v hL hz ⟨k, hk⟩) (Additive.ofMul ⟨w, hw⟩)).toMul : G) / w = _
      rw [componentRepresentation_apply, div_eq_mul_inv]
      rfl

/-- The canonical moved module and its fixed submodule, with their induced actions. -/
def movedSection : MovedSection (componentRepresentation K L T z v hL hz) ⊤ :=
  MovedSection.ofNormal _ ⊤

/-- Under the invariance clause of 13.6.14, the moved space is the original U_K. -/
theorem movedSection_ambient (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    ambientSpace K L T z v (movedSection K L T z v hL hz).space.toSubmodule =
      UX L z v (starImage z v K) := by
  rw [(movedSection K L T z v hL hz).space_eq, moved_ambientSpace]
  exact (invariant_component_consequences K L T z v hK hn).2.symm

abbrev MovedSpace := (movedSection K L T z v hL hz).space.toSubmodule
abbrev FixedSpace := (movedSection K L T z v hL hz).central.toSubmodule
abbrev QuotientSpace := MovedSpace K L T z v hL hz ⧸ FixedSpace K L T z v hL hz
abbrev quotientRepresentation := (movedSection K L T z v hL hz).action

/-- The fixed kernel is retained in the literal quotient map. -/
def projection : MovedSpace K L T z v hL hz →ₗ[ZMod 2] QuotientSpace K L T z v hL hz :=
  (FixedSpace K L T z v hL hz).mkQ

theorem projection_surjective : Function.Surjective (projection K L T z v hL hz) :=
  Submodule.mkQ_surjective _

theorem projection_ker : LinearMap.ker (projection K L T z v hL hz) =
    fixedSpace (movedSection K L T z v hL hz).space.toRepresentation ⊤ := by
  rw [projection, Submodule.ker_mkQ]
  exact (movedSection K L T z v hL hz).central_eq

/-- In ambient terms, the kernel consists precisely of moved vectors commuting
with every element of the original K. -/
theorem projection_eq_zero_iff (w : MovedSpace K L T z v hL hz) :
    projection K L T z v hL hz w = 0 ↔
      (w.val.toMul : G) ∈ centralizer (K : Set G) := by
  rw [← LinearMap.mem_ker, projection_ker]
  change (∀ a : (⊤ : Subgroup (plusImage K L T z v hL hz K)),
    (movedSection K L T z v hL hz).space.toRepresentation a.val w = w) ↔ _
  constructor
  · intro hw
    apply mem_centralizer_iff.mpr
    intro k hk
    have he := congrArg (fun x : MovedSpace K L T z v hL hz => (x.val.toMul : G))
      (hw ⟨componentMap K L T z v hL hz ⟨k, hk⟩, mem_top _⟩)
    change ((componentRepresentation K L T z v hL hz
      (componentMap K L T z v hL hz ⟨k, hk⟩) w.val).toMul : G) = _ at he
    rw [componentRepresentation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hw a
    obtain ⟨k, hk⟩ := componentMap_surjective K L T z v hL hz a.val
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((componentRepresentation K L T z v hL hz a.val w.val).toMul : G) = _
    rw [← hk, componentRepresentation_apply]
    rw [mem_centralizer_iff.mp hw k k.property]
    simp [mul_assoc]

/-- The quotient intertwines the original component action, before any model recognition. -/
theorem quotientRepresentation_projection (k : plusImage K L T z v hL hz K)
    (w : MovedSpace K L T z v hL hz) :
    quotientRepresentation K L T z v hL hz k (projection K L T z v hL hz w) =
      projection K L T z v hL hz ((movedSection K L T z v hL hz).space.toRepresentation k w) := rfl

/-- An actual action identification on the moved quotient. Constructing it from
B.5 is a separate recognition obligation. It makes no assertion that W_K is irreducible. -/
abbrev NaturalMarking (F : BinaryField) :=
  ActionEquiv (quotientRepresentation K L T z v hL hz) (binaryG2 F)

variable {K L T z v hL hz}

/-- Change coordinates together with an inner change of the G₂ group marking.
This is needed when aligning T_v ∩ K with the standard Sylow subgroup. -/
def NaturalMarking.conjugate {F : BinaryField}
    (e : NaturalMarking K L T z v hL hz F) (g : Atlas.G2.Model F.Carrier) :
    NaturalMarking K L T z v hL hz F where
  groupEquiv := e.groupEquiv.trans (MulAut.conj g)
  linearEquiv := e.linearEquiv.trans
    (LinearEquiv.ofBijective (binaryG2 F g) ((binaryG2 F).apply_bijective g))
  intertwines a w := by
    change binaryG2 F g (e.linearEquiv (quotientRepresentation K L T z v hL hz a w)) = _
    rw [e.intertwines]
    change binaryG2 F g (binaryG2 F (e.groupEquiv a) (e.linearEquiv w)) =
      binaryG2 F (g * e.groupEquiv a * g⁻¹) (binaryG2 F g (e.linearEquiv w))
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The map from the genuine moved space to octonion coordinates. -/
def NaturalMarking.coordinates {F : BinaryField}
    (e : NaturalMarking K L T z v hL hz F) :
    MovedSpace K L T z v hL hz →ₗ[ZMod 2] Atlas.G2.Natural.Space F.Carrier :=
  e.linearEquiv.toLinearMap.comp (projection K L T z v hL hz)

/-- Recognition never discards the fixed part of the original moved space. -/
theorem NaturalMarking.coordinates_ker {F : BinaryField}
    (e : NaturalMarking K L T z v hL hz F) :
    LinearMap.ker e.coordinates =
      fixedSpace (movedSection K L T z v hL hz).space.toRepresentation ⊤ := by
  rw [NaturalMarking.coordinates, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr e.linearEquiv.injective)]
  exact projection_ker K L T z v hL hz

/-- The original element k acts through the literal map K → K⁺ → G₂. -/
theorem NaturalMarking.coordinates_intertwines {F : BinaryField}
    (e : NaturalMarking K L T z v hL hz F) (k : K)
    (w : MovedSpace K L T z v hL hz) :
    e.coordinates ((movedSection K L T z v hL hz).space.toRepresentation
      (componentMap K L T z v hL hz k) w) =
      binaryG2 F (modelMap K L T z v hL hz e.groupEquiv k) (e.coordinates w) := by
  exact (congrArg e.linearEquiv
    (quotientRepresentation_projection K L T z v hL hz _ w).symm).trans
      (e.intertwines _ _)

open scoped MatrixGroups

/-- Apply the constructed parabolics while retaining the actual, Sylow-aligned
intertwiner. The kernel and recognition are still explicit source obligations. -/
theorem exists_moving_nonshort_parabolic_of_marking [Finite G]
    {F : BinaryField} (hF : 1 < F.degree)
    (e : NaturalMarking K L T z v hL hz F)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) :
    ∃ (e' : NaturalMarking K L T z v hL hz F) (i : Fin 2),
      let P := liftedParabolic K L T z v hL hz e'.groupEquiv i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((residualIn P ⧸ pCore 2 (residualIn P)) ≃* PSL(2,F.Carrier)) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2,F.Carrier)) := by
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hpow : 2 ^ 2 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide) hF
    omega
  have hm : ¬ K ≤ centralizer ({z} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L T z v hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)
  obtain ⟨g, i, h⟩ := G2.exists_moving_nonshort_parabolic K L T z v hL hz
    e.groupEquiv hq hK hm hk
  exact ⟨e.conjugate g, i, h⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction

