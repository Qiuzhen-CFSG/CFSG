module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Inputs

/-!
# The marked component in the original paired action

The first component acts through its specified SL₃(2) quotient on the first
coordinate and fixes the second coordinate pointwise. These statements retain
the original coordinate maps and ambient conjugation, including the precise
inclusion of L in L₀T. A lift to the faithful wreath action is kept separate
from surjectivity and the kernel calculation.

Source: Aschbacher--Smith 10.1.1(3), printed p.741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
open Chapter3.Section02 Geometry.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)
  (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)

/-- Only a lift of the original action; neither its image nor its kernel is assumed. -/
structure LiftData where
  hom : localJoin T L →* Actor
  equivariant (g : localJoin T L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D g v) = action (hom g) (fullCoordinates s hz v)

/-- The inclusion of the original component in its Sylow join. -/
def componentInclusion : L →* localJoin T L :=
  inclusion ((le_componentOrbit L T).trans le_sup_left)

/-- The prescribed component quotient, without a new choice of model. -/
def componentHom : L →* Matrix.PSL3Two.SL :=
  s.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentHom_surjective : Function.Surjective (componentHom s) :=
  s.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The first base factor in the literal wreath convention. -/
def firstBase : Matrix.PSL3Two.SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then a else 1, 1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    ext i
    · by_cases hi : i = 1 <;> simp [hi]
    · simp

theorem firstBase_action (a : Matrix.PSL3Two.SL) (v : Space) (i : Bit) :
    action (firstBase a) v i =
      if i = 1 then Multiplicative.ofAdd (a.val *ᵥ (v i).toAdd) else v i := by
  rw [action_apply]
  by_cases hi : i = 1 <;> simp [firstBase, hi]

theorem coordinates_factorProduct
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
    fullCoordinates s hz (factorProduct s hz (a,b)) i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  convert fullCoordinates_mul s hz a b i using 2
  exact Subtype.ext (factorProduct_apply s hz a b)

theorem component_equivariant (l : L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D (componentInclusion l) v) =
      action (firstBase (componentHom s l)) (fullCoordinates s hz v) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  let a' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨(l : G) * a * (l : G)⁻¹,
    (mem_normalizer_iff.mp (s.natural.normalized l.property) a).mp a.property⟩
  have hb : (l : G) * b * (l : G)⁻¹ = b := by
    rw [s.crossed b.property l l.property, mul_inv_cancel_right]
  have he : joinAction D (componentInclusion l) (factorProduct s hz (a,b)) =
      factorProduct s hz (a',b) := by
    apply Subtype.ext
    rw [joinAction_apply, factorProduct_apply, factorProduct_apply]
    change (l : G) * ((a : G) * b) * (l : G)⁻¹ =
      ((l : G) * a * (l : G)⁻¹) * b
    calc
      _ = ((l : G) * a * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) := by group
      _ = _ := by rw [hb]
  have hc (x : (⁅D.fullModule,L⁆ : Subgroup G))
      (y : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
      fullCoordinates s hz (factorProduct s hz (x,y)) i =
        if i = 1 then s.natural.coordinates x else partnerCoordinates s hz y := by
    convert fullCoordinates_mul s hz x y i using 2
    exact Subtype.ext (factorProduct_apply s hz x y)
  rw [he]
  funext i
  rw [firstBase_action, hc, hc]
  by_cases hi : i = 1
  · simp only [hi]
    exact congrArg Multiplicative.ofAdd (s.natural.equivariant l a)
  · simp only [hi, if_false]

/-- Faithfulness forces every lift to have the prescribed first-component marking. -/
theorem LiftData.component (f : LiftData s hz) (l : L) :
    f.hom (componentInclusion l) = firstBase (componentHom s l) := by
  apply action_injective
  apply MulEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
  exact (f.equivariant _ v).symm.trans (component_equivariant s hz l v)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
