module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiPairSection
public import Theory.Representation.Suzuki.NormalSmallSection

/-!
# Cartan-invariant natural sections of the Suzuki radical

The subgroup HR_j acts by literal conjugation on U_sj and its Frattini
quotient; R_j is normal in this actor. Restriction to R_j is exactly the
previously constructed effective action. The five-root bound gives degree
at most 5b when a≤b. A nontrivial HR_j-irreducible section exists by
perfectness of the concrete Suzuki subgroup. Distinct Clifford conjugates
of an R_j constituent would require degree at least 8b, so the restriction
is irreducible and the small-degree classification identifies it naturally.

Both section subspaces are invariant under the entire source HR_j, and
the final intertwiner uses the literal subgroup-of inclusion and the
supplied R_j marking. The denominator is the actual radical Frattini
subgroup, as proved in SuzukiPairSection. This discharges the normal
restriction/narrow-degree step of (6C); the H-weight profile and parameter
equality, then the equal-parameter contradiction, remain separate steps.

Source: Fong--Seitz I (6C), printed pp.40--41, using Clifford restriction
and (4F). The original/geometric applications retain these same maps.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The literal source HR_j, inside the same finite quotient. -/
@[expose] def radicalCartanActor (j : Fin 2) : Subgroup (X ⧸ Q.D) :=
  (Q.tits.B ⊓ Q.tits.N) ⊔ rankOne Q split j

/-- R_j as a normal subgroup of the source HR_j. -/
@[expose] def radicalCartanRankOne (j : Fin 2) : Subgroup (radicalCartanActor Q split j) :=
  (rankOne Q split j).subgroupOf (radicalCartanActor Q split j)

instance radicalCartanRankOne_normal (j : Fin 2) :
    (radicalCartanRankOne Q split j).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show rankOne Q split j ≤ radicalCartanActor Q split j
    from le_sup_right)).mpr (sup_le (rankOne_torus_normalizes Q split j) (rankOne Q split j).le_normalizer)

/-- The subgroup-of comparison keeps the ambient representative unchanged. -/
def radicalCartanRankOneEquiv (j : Fin 2) :
    radicalCartanRankOne Q split j ≃* rankOne Q split j :=
  subgroupOfEquivOfLe (show rankOne Q split j ≤ radicalCartanActor Q split j from le_sup_right)

/-- Full Cartan and root actor conjugation on the actual radical. -/
@[expose] def radicalCartanAction (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    radicalCartanActor Q split j →* MulAut (simpleRemainder Q split j) :=
  (simpleRemainder Q split j).normalizerMonoidHom.comp
    (inclusion ((sup_le (inf_le_left.trans (Q.tits.B_le_standardParabolic {Q.simple j}))
      (rankOne_le_parabolic Q split j)).trans (remainder_parabolic_normalizes Q split j hKj)))

/-- Source right conjugation is the action of the inverse representative. -/
@[simp] theorem radicalCartanAction_right_conjugation (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (g : radicalCartanActor Q split j) (x : simpleRemainder Q split j) :
    (radicalCartanAction Q split j hKj g⁻¹ x : X ⧸ Q.D) =
      (g : X ⧸ Q.D)⁻¹ * x * (g : X ⧸ Q.D) := by
  change (g : X ⧸ Q.D)⁻¹ * x * ((g : X ⧸ Q.D)⁻¹)⁻¹ = _
  rw [inv_inv]

@[expose] def radicalCartanEffectiveAction (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    radicalCartanActor Q split j →* MulAut (radicalSection Q split j hKj).EffectiveCarrier := by
  let d := radicalSection Q split j hKj
  letI : d.effectiveDenominator.Normal := RootSection.effectiveDenominator_normal d
  exact sectionQuotientAction (A := d.numerator) (radicalCartanAction Q split j hKj)
    d.effectiveDenominator (by
      intro g
      rw [suzuki_radical_effectiveDenominator Q split j hKj]
      exact frattini_map_equiv _)

/-- The binary HR_j action on the source radical Frattini quotient. -/
@[expose] def radicalCartanRepresentation (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    Representation (ZMod 2) (radicalCartanActor Q split j)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier) where
  toFun g := (radicalCartanEffectiveAction Q split j hKj g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; simp only [map_one]; rfl
  map_mul' g h := by ext v; simp only [map_mul]; rfl

@[simp] theorem radicalCartanRepresentation_mk (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (g : radicalCartanActor Q split j) (x : simpleRemainder Q split j) :
    radicalCartanRepresentation Q split j hKj g (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (radicalCartanAction Q split j hKj g x)) := rfl

/-- On R_j the full source action is exactly the existing radical action. -/
theorem radicalCartanRepresentation_restrict (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (radicalCartanRepresentation Q split j hKj).comp
      (inclusion (show rankOne Q split j ≤ radicalCartanActor Q split j from le_sup_right)) =
      (radicalSection Q split j hKj).effectiveRepresentation := by
  apply MonoidHom.ext
  intro r
  apply LinearMap.ext
  intro v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    (radicalSection Q split j hKj).effectiveDenominator v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk x) := congrArg Additive.ofMul hx.symm
  rw [hv]
  rfl

/-- The full HR_j action admits an HR_j-invariant section which restricts
irreducibly and naturally to its actual normal Suzuki subgroup. -/
theorem suzuki_suzuki_cartan_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    let K := radicalCartanRankOne Q split j
    let μ := (radicalCartanRankOneEquiv Q split j).trans μj
    ∃ U : Subrepresentation (radicalCartanRepresentation Q split j hKj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Representation.IsIrreducible (N.quotientRepresentation.comp K.subtype) ∧
        Nonempty (Representation.Equiv
          (N.quotientRepresentation.comp (K.subtype.comp μ.symm.toMonoidHom))
          (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) := by
  let ρ := radicalCartanRepresentation Q split j hKj
  let K := radicalCartanRankOne Q split j
  let μ := (radicalCartanRankOneEquiv Q split j).trans μj
  have hf : Function.Injective (radicalSection Q split j hKj).effectiveRepresentation :=
    (radicalSection Q split j hKj).effectiveRepresentation_injective
      (suzuki_section_effectiveAction_injective Q split j hn μj _
        (suzuki_radical_action_ne_one Q split j hhex i hij
          (UnitarySource.actorReflection Q split j) hKj))
  let : IsSimpleGroup (SuzukiMatrixGroup n) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  have hne : ¬ K ≤ ρ.ker := by
    intro hk
    obtain ⟨g,hg⟩ := exists_ne (1 : SuzukiMatrixGroup n)
    let r := μj.symm g
    let k : K := (radicalCartanRankOneEquiv Q split j).symm r
    have he : ρ (k : radicalCartanActor Q split j) = 1 := hk k.property
    have hr : (radicalSection Q split j hKj).effectiveRepresentation r = 1 := by
      rw [← radicalCartanRepresentation_restrict Q split j hKj]
      exact he
    have hr1 : r = 1 := hf (hr.trans (map_one _).symm)
    exact hg (μj.symm.injective (hr1.trans μj.symm.map_one.symm))
  have hd := (suzuki_suzuki_radical_finrank_bounds Q split hhex i j hij hKj hm hn μj νi νj).2
  have hsmall : Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier) < 8*(2*n+1) := by omega
  obtain ⟨U,N,hi,hK,⟨e⟩⟩ := Representation.SuzukiSmallDegree.exists_natural_normal_section
    ρ K hn μ hne hsmall
  exact ⟨U,N,hi,hK,⟨e⟩,e.toLinearEquiv.finrank_eq.trans
    (Representation.SuzukiNatural.natural_finrank n)⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
