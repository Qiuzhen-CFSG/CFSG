module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelKernel
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.Frattini.PGroup
public import Theory.Representation.ElementaryAbelianAction

/-!
# Faithful Cartan action on the actual unipotent core section

The full Cartan normalizes U ∩ U^s. Its intersection with the endpoint
panel kernel centralizes the simple root. An element fixing the remainder
therefore centralizes U. Local characteristic two puts it in O₂(P), hence
in U; its membership in the odd Cartan forces it to be identity.

The coprime Frattini-kernel theorem preserves this faithfulness on the
literal section (U ∩ U^s)/Φ(U ∩ U^s). This constructs its binary linear
action, with the original conjugation and quotient maps retained. No
irreducibility, rank-one model or extension field is assumed here.

Source: Fong--Seitz I (3B)(c), p.13; II (8B), p.201, and (8C), p.203.
These are the faithful scalar actors used to construct the coefficient
fields. The row-specific irreducibility and dimensions remain necessary.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

@[expose] def coreCartan : Subgroup (X ⧸ Q.D) :=
  Q.tits.B ⊓ Q.tits.N ⊓ ReeSource.embeddedPanelKernel Q i

theorem torus_normalizes_remainder :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
  (le_inf (inf_le_left.trans split.normalizes)
    (torus_normalizes_unipotentConjugate split (Q.simple i))).trans
      inf_normalizer_le_normalizer_inf

@[expose] def coreCartanAction :
    coreCartan Q i →* MulAut (simpleRemainder Q split i) :=
  (simpleRemainder Q split i).normalizerMonoidHom.comp
    (inclusion (show coreCartan Q i ≤ normalizer (simpleRemainder Q split i : Set _) from
      inf_le_left.trans (torus_normalizes_remainder Q split i)))

@[simp] theorem coreCartanAction_apply (h : coreCartan Q i) (v : simpleRemainder Q split i) :
    (coreCartanAction Q split i h v : X ⧸ Q.D) = (h : X ⧸ Q.D)*v*(h : X ⧸ Q.D)⁻¹ := rfl

/-- Local characteristic two kills a Cartan element centralizing all of U. -/
theorem cartan_eq_one_of_centralizes_unipotent
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (h : X ⧸ Q.D) (hh : h ∈ Q.tits.B ⊓ Q.tits.N)
    (hU : ∀ u ∈ split.U, Commute h u) : h = 1 := by
  let D := Q.tits.standardParabolic {Q.simple i}
  have hUD : split.U ≤ D := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hcore : pCore 2 D ≤ split.U.subgroupOf D :=
    pCore_isPGroup.le_sylow_of_normal (split.sylow.subtype hUD)
  let hD : D := ⟨h,Q.tits.B_le_standardParabolic _ hh.1⟩
  have hhcore : hD ∈ pCore 2 D := by
    apply hc
    rw [mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (hU u (hcore hu)).symm.eq
  have hm : h ∈ split.U ⊓ Q.tits.N := ⟨hcore hhcore,hh.2⟩
  rwa [split.unipotent_inf_N, mem_bot] at hm

theorem coreCartanAction_injective
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    Function.Injective (coreCartanAction Q split i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro h hh
  apply Subtype.ext
  apply cartan_eq_one_of_centralizes_unipotent Q split i hc h h.property.1
  intro u hu
  have hm : u ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
    rw [simpleRoot_mul_remainder]
    exact hu
  obtain ⟨a,ha,v,hv,rfl⟩ := hm
  have haH : Commute (h : X ⧸ Q.D) a :=
    (ReeSource.commute_of_panelKernel_of_normalizes Q split i h.property.2
      (torus_normalizes_simpleRoot Q split i h.property.1) ha)
  have hvH : Commute (h : X ⧸ Q.D) v := by
    have he := congrArg (fun f : MulAut (simpleRemainder Q split i) =>
      (f ⟨v,hv⟩ : X ⧸ Q.D)) hh
    rw [coreCartanAction_apply] at he
    change (h : X ⧸ Q.D)*v*(h : X ⧸ Q.D)⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact haH.mul_right hvH

@[expose] def coreFrattiniAction : coreCartan Q i →*
    MulAut ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) :=
  (Subgroup.quotientAut (frattini (simpleRemainder Q split i))).comp (coreCartanAction Q split i)

theorem coreFrattiniAction_injective
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    Function.Injective (coreFrattiniAction Q split i) := by
  apply MonoidHom.injective_frattini_action_of_coprime
    (split.isTwo.of_injective (inclusion (show simpleRemainder Q split i ≤ split.U from
      inf_le_left)) (inclusion_injective _)) (coreCartanAction Q split i)
    (coreCartanAction_injective Q split i hc)
  exact (split.odd.of_dvd_right (card_dvd_of_le (show coreCartan Q i ≤ Q.tits.B ⊓ Q.tits.N from
    inf_le_left))).symm

@[simp] theorem coreFrattiniAction_mk (h : coreCartan Q i) (v : simpleRemainder Q split i) :
    coreFrattiniAction Q split i h (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v) =
      QuotientGroup.mk' (frattini (simpleRemainder Q split i)) (coreCartanAction Q split i h v) :=
  Subgroup.quotientAut_apply_mk _ _ _

instance coreFrattini_elementary :
    IsElementaryAbelian 2 ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) := by
  let : Fact (IsPGroup 2 (simpleRemainder Q split i)) := ⟨split.isTwo.of_injective
    (inclusion (show simpleRemainder Q split i ≤ split.U from inf_le_left))
    (inclusion_injective _)⟩
  exact isElementaryAbelian_quotient_frattini

/-- The canonical binary vector space on the literal source core section. -/
abbrev CoreSpace := Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))

/-- The full actual Cartan kernel acts linearly on the source Frattini section. -/
@[expose] def coreFrattiniRepresentation : Representation (ZMod 2) (coreCartan Q i) (CoreSpace Q split i) where
  toFun h := (coreFrattiniAction Q split i h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change Additive.ofMul (coreFrattiniAction Q split i 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' h k := by
    ext v
    change Additive.ofMul (coreFrattiniAction Q split i (h*k) v.toMul) = _
    rw [map_mul]
    rfl

@[simp] theorem coreFrattiniRepresentation_apply (h : coreCartan Q i) (v : CoreSpace Q split i) :
    coreFrattiniRepresentation Q split i h v = Additive.ofMul (coreFrattiniAction Q split i h v.toMul) := rfl

theorem coreFrattiniRepresentation_injective
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    Function.Injective (coreFrattiniRepresentation Q split i) := by
  intro h k he
  apply coreFrattiniAction_injective Q split i hc
  ext v
  exact Additive.ofMul.injective (congrArg
    (fun f : Module.End (ZMod 2) (CoreSpace Q split i) => f (Additive.ofMul v)) he)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
