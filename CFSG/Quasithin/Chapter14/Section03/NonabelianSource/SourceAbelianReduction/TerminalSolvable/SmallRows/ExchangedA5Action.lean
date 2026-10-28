module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5Kernel
public import Theory.Representation.OrthogonalFourPlusMatrix.SymplecticNormalizerDefs
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

/-!
# Transporting the actual paired terminal action

A model consists of an equivalence on the dotted normal component span and
equivariant binary coordinates on U/Z(U). It does not assert recognition,
small actor rank, or a normalizer order. Such a model embeds the entire
faithful terminal action in the symplectic normalizer of the transported
source form. The two-core quotient of the span joined with T is therefore
bounded by that normalizer, once the original small-actor argument applies.

Source: Aschbacher--Smith G.11.2(7) and 14.3.15, pp.364,994.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
namespace ExchangedA5
abbrev ModelGroup := ClassicalOrthogonal.FourPlusMatrix.Binary.G
abbrev ModelSpace := ClassicalOrthogonal.FourPlusMatrix.Binary.V
open ClassicalOrthogonal.FourPlusMatrix.Binary
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
  [IsElementaryAbelian 2 F.Uhat] (K : Subgroup G)

/-- Genuine binary coordinates and the action of the literal normal span. -/
structure ActionModel where
  componentEquiv : F.terminalDot (conjugateSpanBy K (T : Subgroup G)) ≃* ModelGroup
  coordinates : Additive F.Uhat ≃ₗ[ZMod 2] ModelSpace
  intertwines : ∀ (k : F.terminalDot (conjugateSpanBy K (T : Subgroup G)))
    (u : Additive F.Uhat), coordinates (F.terminalRepresentation k u) =
      action (componentEquiv k) (coordinates u)

namespace ActionModel
variable {F K} (m : ActionModel F K)

def coordinateAction : F.TerminalHdot →* (ModelSpace ≃ₗ[ZMod 2] ModelSpace) where
  toFun h := m.coordinates.symm.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive F.Uhat)
      (F.terminalRepresentation.asGroupHom h)).trans m.coordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro u
    change m.coordinates (F.terminalRepresentation 1 (m.coordinates.symm u)) = u
    simp
  map_mul' a b := by
    apply LinearEquiv.ext
    intro u
    change m.coordinates (F.terminalRepresentation (a * b) (m.coordinates.symm u)) =
      m.coordinates (F.terminalRepresentation a
        (m.coordinates.symm (m.coordinates (F.terminalRepresentation b (m.coordinates.symm u)))))
    rw [LinearEquiv.symm_apply_apply, map_mul, Module.End.mul_apply]

theorem coordinateAction_apply (h : F.TerminalHdot) (u : ModelSpace) :
    m.coordinateAction h u = m.coordinates
      (F.terminalRepresentation h (m.coordinates.symm u)) := rfl

theorem coordinateAction_injective : Function.Injective m.coordinateAction := by
  intro a b hab
  apply F.terminalRepresentation_injective
  apply LinearMap.ext
  intro u
  apply m.coordinates.injective
  simpa only [coordinateAction_apply, LinearEquiv.symm_apply_apply] using
    LinearEquiv.congr_fun hab (m.coordinates u)

theorem coordinateAction_component_image :
    (F.terminalDot (conjugateSpanBy K (T : Subgroup G))).map m.coordinateAction =
      linearAction.range := by
  have he (k : F.terminalDot (conjugateSpanBy K (T : Subgroup G))) :
      m.coordinateAction k = linearAction (m.componentEquiv k) := by
    apply LinearEquiv.ext
    intro u
    rw [coordinateAction_apply, m.intertwines, LinearEquiv.apply_symm_apply]
    rfl
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨m.componentEquiv ⟨k,hk⟩, (he ⟨k,hk⟩).symm⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨m.componentEquiv.symm k, (m.componentEquiv.symm k).property,
      (he (m.componentEquiv.symm k)).trans
        (congrArg linearAction (m.componentEquiv.apply_symm_apply k))⟩

/-- Transport the given source form, rather than choosing a new invariant form. -/
def form (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) :
    LinearMap.BilinForm (ZMod 2) ModelSpace := LinearMap.BilinForm.congr m.coordinates B

theorem form_alternating {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)}
    (hB : B.IsAlt) : (m.form B).IsAlt := fun u => hB (m.coordinates.symm u)

theorem form_nondegenerate {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)}
    (hB : B.Nondegenerate) : (m.form B).Nondegenerate := hB.congr m.coordinates

theorem coordinateAction_preserves
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v)
    (h : F.TerminalHdot) (u v : ModelSpace) :
    m.form B (m.coordinateAction h u) (m.coordinateAction h v) = m.form B u v := by
  change B (m.coordinates.symm (m.coordinateAction h u))
    (m.coordinates.symm (m.coordinateAction h v)) = _
  rw [coordinateAction_apply, coordinateAction_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact hB h _ _

theorem form_invariant (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v)
    (a : ModelGroup) (u v : ModelSpace) :
    m.form B (action a u) (action a v) = m.form B u v := by
  have ha : linearAction a ∈ (F.terminalDot
      (conjugateSpanBy K (T : Subgroup G))).map m.coordinateAction := by
    rw [m.coordinateAction_component_image]
    exact ⟨a,rfl⟩
  obtain ⟨h,_,hh⟩ := ha
  simpa only [hh, linearAction_apply] using m.coordinateAction_preserves B hB h u v

/-- The original terminal group embeds in the actual symplectic normalizer. -/
def normalizerEmbedding {g : G} (hK : ComponentLift F g K)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v) :
    F.TerminalHdot →* symplecticNormalizer (m.form B) :=
  m.coordinateAction.codRestrict _ (by
    intro h
    refine ⟨?_, m.coordinateAction_preserves B hB h⟩
    rw [← m.coordinateAction_component_image]
    let : (F.terminalDot (conjugateSpanBy K (T : Subgroup G))).Normal :=
      Normal.map hK.normal_span _ (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    apply Subgroup.le_normalizer_map m.coordinateAction
    apply mem_map_of_mem
    rw [Subgroup.normalizer_eq_top]
    trivial)

theorem normalizerEmbedding_injective {g : G} (hK : ComponentLift F g K)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v) :
    Function.Injective (m.normalizerEmbedding hK B hB) :=
  fun _ _ hh => m.coordinateAction_injective (congrArg Subtype.val hh)

variable [Finite G]

/-- Transfer the elementary actor bound from the actual normalizer. This
recovers the small-actor premise of 14.3.12 from G.11.2(7)'s outside clause. -/
theorem small_actor_bound {g : G} (hK : ComponentLift F g K)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v)
    (hactors : ∀ A : Subgroup (symplecticNormalizer (m.form B)), IsElementaryAbelian 2 A →
      ¬ A.map (symplecticNormalizer (m.form B)).subtype ≤ linearAction.range → Nat.card A ≤ 8)
    (X : Subgroup F.TerminalHdot) [IsElementaryAbelian 2 X]
    (hout : ¬ X ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G))) :
    Module.finrank (ZMod 2) (Additive X) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 := by
  let r := m.normalizerEmbedding hK B hB
  have hr := m.normalizerEmbedding_injective hK B hB
  let A := X.map r
  have ha : ¬ A.map (symplecticNormalizer (m.form B)).subtype ≤ linearAction.range := by
    intro ha
    apply hout
    intro x hx
    have hm : m.coordinateAction x ∈ linearAction.range :=
      ha (mem_map_of_mem _ (mem_map_of_mem r hx))
    rw [← m.coordinateAction_component_image] at hm
    obtain ⟨y,hy,he⟩ := hm
    exact m.coordinateAction_injective he ▸ hy
  have hc : Nat.card X ≤ 8 := by
    have hh := hactors A (IsElementaryAbelian.map r) ha
    rwa [← Nat.card_congr (Subgroup.equivMapOfInjective X r hr).toEquiv] at hh
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 8 :=
    m.coordinates.finrank_eq.trans finrank_binary
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive X) ≤ 2 ^ 3 := by
    change Nat.card (Additive X) ≤ 8 at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact hc
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp
  simpa only [hd, Nat.reduceDiv, Nat.reduceSub] using he

/-- The order bound applies to D joined with T without asserting its normality. -/
theorem span_join_core_quotient_card_le {g : G} (hK : ComponentLift F g K)
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ h u v, B (F.terminalRepresentation h u) (F.terminalRepresentation h v) = B u v) :
    Nat.card ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≤
        Nat.card (symplecticNormalizer (m.form B)) := by
  have hJH : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) ≤ F.H :=
    sup_le (conjugateSpanBy_le hK.le_pointNormalizer
      ((F.invariant 1).trans F.H.le_normalizer)) (F.invariant 1)
  exact (terminal_subgroup_core_quotient_card_le F hJH hk).trans
    ((Subgroup.card_le_card_group _).trans (Nat.card_le_card_of_injective
      (m.normalizerEmbedding hK B hB) (m.normalizerEmbedding_injective hK B hB)))

end ActionModel
end ExchangedA5
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
