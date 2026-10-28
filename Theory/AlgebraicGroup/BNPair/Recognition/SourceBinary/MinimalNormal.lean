module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.NormalQuotients
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.ChiefFactorDirectPower.CharacteristicallySimple

/-!
# The unique minimal normal subgroup of the marked quotient

For the same finite split rank-two quotient, suppose both marked parabolics
have self-centralizing two-cores and the conjugates of U generate the group.
Every nontrivial normal subgroup has a two-group quotient, hence contains
the literal two-residual R = O²(X/D). This residual is nontrivial: otherwise
X/D would be a two-group, contradicting its trivial two-core and proper
marked parabolics. Thus R is the unique minimal normal subgroup.

Characteristic subgroups of R are ambient normal, so R is characteristically
simple. When R is perfect, its ambient centralizer is trivial, and the finite
characteristically-simple structure theorem gives an actual isomorphism
R ≃ Aⁿ with n positive and A nonabelian simple. The source adapter proves
perfectness from the original normalized perfect factors; it is not assumed
as part of the marked-quotient input.

This is a normal-subgroup reduction toward the Fong–Seitz invocation in DGS,
Groups and Graphs, Part II, pp.80–81 and224. It does not identify A, prove n=1,
or supply the full minimal configuration or seven marked Lie rows. Finiteness
is required only of the given quotient, and no quotient map or endpoint
marking is changed.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- The actual two-residual is nontrivial, without a perfectness premise. -/
theorem twoResidual_ne_bot (split : SplitData d.tits) :
    pResidual 2 (X ⧸ d.D) ≠ ⊥ := by
  intro he
  have htwo : IsPGroup 2 (X ⧸ d.D) :=
    (isPGroup_quotient_pResidual (G := X ⧸ d.D) 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)
  have ht := split.normal_two_subgroup_eq_bot ⊤ (htwo.to_subgroup ⊤)
  exact (d.parabolic_isCoatom 0).ne_top
    (le_antisymm le_top (ht ▸ bot_le))

variable (split : SplitData d.tits)
    (hc : ∀ i, centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
      Set (d.tits.standardParabolic {d.simple i})) ≤
      pCore 2 (d.tits.standardParabolic {d.simple i}))
    (hgen : split.unipotentClosure = ⊤)

include split hc hgen

/-- Every nontrivial ambient normal subgroup contains the same two-residual. -/
theorem twoResidual_le_normal (V : Subgroup (X ⧸ d.D)) [V.Normal] (hne : V ≠ ⊥) :
    pResidual 2 (X ⧸ d.D) ≤ V :=
  sInf_le ⟨inferInstance, d.quotient_isPGroup_of_ne_bot split hc hgen V hne⟩

/-- Minimality refers to normality in the full marked quotient. -/
theorem twoResidual_minimal (V : Subgroup (X ⧸ d.D)) [V.Normal]
    (hV : V ≤ pResidual 2 (X ⧸ d.D)) : V = ⊥ ∨ V = pResidual 2 (X ⧸ d.D) := by
  by_cases hz : V = ⊥
  · exact Or.inl hz
  · exact Or.inr (le_antisymm hV (d.twoResidual_le_normal split hc hgen V hz))

/-- The residual has no proper nontrivial characteristic subgroup. -/
theorem twoResidual_characteristic_simple
    (C : Subgroup (pResidual 2 (X ⧸ d.D))) [C.Characteristic] : C = ⊥ ∨ C = ⊤ := by
  let R := pResidual 2 (X ⧸ d.D)
  obtain he | he := d.twoResidual_minimal split hc hgen (C.map R.subtype)
    (map_subtype_le C)
  · exact Or.inl ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp he)
  · right
    apply map_injective R.subtype_injective
    simpa only [← MonoidHom.range_eq_map, range_subtype] using he

/-- Perfectness eliminates the entire ambient centralizer of the residual. -/
theorem twoResidual_centralizer_eq_bot
    (hp : Group.IsPerfect (pResidual 2 (X ⧸ d.D))) :
    centralizer (pResidual 2 (X ⧸ d.D) : Set (X ⧸ d.D)) = ⊥ := by
  let R := pResidual 2 (X ⧸ d.D)
  let := hp
  let : Nontrivial R := R.nontrivial_iff_ne_bot.mpr (d.twoResidual_ne_bot split)
  by_contra hn
  have hle := d.twoResidual_le_normal split hc hgen (centralizer (R : Set (X ⧸ d.D))) hn
  exact Group.IsPerfect.not_isMulCommutative R (le_centralizer_iff_isMulCommutative.mp hle)

/-- An actual positive direct-power isomorphism, with a perfect simple factor.
No Lie type or restriction on the number of factors is asserted. -/
theorem twoResidual_simple_power
    (hp : Group.IsPerfect (pResidual 2 (X ⧸ d.D))) :
    ∃ A : Subgroup (pResidual 2 (X ⧸ d.D)), IsSimpleGroup A ∧ Group.IsPerfect A ∧
      ∃ n : ℕ, 0 < n ∧ Nonempty (pResidual 2 (X ⧸ d.D) ≃* (Fin n → A)) := by
  let R := pResidual 2 (X ⧸ d.D)
  let := hp
  let : Nontrivial R := R.nontrivial_iff_ne_bot.mpr (d.twoResidual_ne_bot split)
  obtain ⟨A, hA, n, hn, ⟨e⟩⟩ := CharacteristicallySimple.exists_simple_subgroup_power
    (fun C hC => @twoResidual_characteristic_simple _ _ _ d split hc hgen C hC)
  have hperf : Group.IsPerfect A := by
    let f : R →* A := (Pi.evalMonoidHom (fun _ : Fin n => A) ⟨0, hn⟩).comp e.toMonoidHom
    apply Group.IsPerfect.ofSurjective (f := f)
    intro a
    exact ⟨e.symm (fun _ => a), by simp [f]⟩
  exact ⟨A, hA, hperf, n, hn, ⟨e⟩⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
