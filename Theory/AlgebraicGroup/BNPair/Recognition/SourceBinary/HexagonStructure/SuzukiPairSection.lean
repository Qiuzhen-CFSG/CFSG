module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.Representation.Suzuki.SmallSection

/-!
# The actual Suzuki/Suzuki radical module and its natural section

The five canonical root coordinates give a surjection from the product of
five root Frattini quotients onto the radical Frattini quotient. Thus its
binary dimension is at most 3a+2b, with a=2m+1 and b=2n+1. Root movement
and Suzuki faithfulness give the lower bound 4b. If a<b this is the source
window [4b,5b); if a≤b, a nontrivial irreducible section is small enough
for the existing Suzuki classification to identify it with the natural
module. We retain the actual subrepresentations and their intertwiner.

The effective denominator is proved equal to the literal radical Frattini
subgroup; no exact dimension or irreducibility of the whole module is
assumed. Cartan constituent control is still needed to deduce a=b, and
the equal-parameter kernel/commutator contradiction is a later step.

Source: Fong--Seitz I (6C), printed pp.40--41. The source uses (4F) and
Clifford restriction; the natural-section extraction below uses perfectness
of the concrete Suzuki actor and the proved small-degree classification.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The literal five-root product bounds the rank of the radical's Frattini
quotient by three opposite-root ranks and two own-root ranks. -/
theorem radical_frattini_index_le (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ≤
      Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i))^3 *
      Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j))^2 := by
  let V := simpleRemainder Q split j
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  have hA : A ≤ V := simpleRoot_le_other_remainder Q split hhex i j hij
  have hB : B ≤ V := (show B ≤ middleRoots Q split i j from
    le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hhex i j hij)
  have hC : C ≤ V := (exchanged_roots_le_remainder Q split hhex i j hij).2
  have hD : D ≤ V := (show D ≤ middleRoots Q split i j from
    le_sup_right).trans (middleRoots_le_remainder Q split hhex i j hij)
  have hE : E ≤ V := (exchanged_roots_le_remainder Q split hhex i j hij).1
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  let q := QuotientGroup.mk' (frattini V)
  let f (T : Subgroup (X ⧸ Q.D)) (hT : T ≤ V) :
      (T ⧸ frattini T) →* (V ⧸ frattini V) :=
    QuotientGroup.lift (frattini T) (q.comp (inclusion hT)) (by
      let : Fact (IsPGroup 2 T) := ⟨split.isTwo.to_le (hT.trans inf_le_left)⟩
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      exact frattini_map_le_of_isPGroup (p := 2) (inclusion hT) (mem_map_of_mem _ hx))
  let F : (A ⧸ frattini A) × (B ⧸ frattini B) × (C ⧸ frattini C) ×
      (D ⧸ frattini D) × (E ⧸ frattini E) → V ⧸ frattini V :=
    fun z => f A hA z.1 * f B hB z.2.1 * f C hC z.2.2.1 *
      f D hD z.2.2.2.1 * f E hE z.2.2.2.2
  have hs : Function.Surjective F := by
    intro z
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (frattini V) z
    obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hhex i j hij).surjective v
    refine ⟨(QuotientGroup.mk a,QuotientGroup.mk b,QuotientGroup.mk c,
      QuotientGroup.mk d,QuotientGroup.mk e), ?_⟩
    change q (inclusion hA a) * q (inclusion hB b) * q (inclusion hC c) *
      q (inclusion hD d) * q (inclusion hE e) = q v
    simp only [← map_mul]
    congr 1
    apply Subtype.ext
    exact (radicalCoordinates_apply Q split hhex i j hij (a,b,c,d,e)).symm.trans
      (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_surjective F hs
  have hc (k : Fin 2) (w : Weyl Q) :
      Nat.card (rootAt Q split k w ⧸ frattini (rootAt Q split k w)) =
        Nat.card (simpleRoot Q split k ⧸ frattini (simpleRoot Q split k)) :=
    Nat.card_congr (QuotientGroup.congr _ _
      (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split k) (representative w))
      (frattini_map_equiv _)).toEquiv
  simp only [Nat.card_prod,A,B,C,D,E,hc] at hh
  calc
    _ ≤ _ := hh
    _ = _ := by ring

/-- In the regular Suzuki/Suzuki row the source quotient has size at most
2^(3a+2b). This is an upper bound, not equality of dimensions. -/
theorem suzuki_suzuki_radical_frattini_upper (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (νi : simpleRoot Q split i ≃* BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* BenderSuzuki.MatrixGroups.SuzukiRootSubgroup n) :
    Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) ≤
      2^(3*(2*m+1)+2*(2*n+1)) := by
  calc
    _ ≤ _ := radical_frattini_index_le Q split hhex i j hij
    _ ≤ (2^(2*m+1))^3 * (2^(2*n+1))^2 := Nat.mul_le_mul
      (Nat.pow_le_pow_left (suzuki_root_frattini_bound Q split i hm νi) 3)
      (Nat.pow_le_pow_left (suzuki_root_frattini_bound Q split j hn νj) 2)
    _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; omega

/-- The concrete Suzuki action on the literal radical effective quotient. -/
abbrev suzukiRadicalRepresentation (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {n : ℕ} (μ : rankOne Q split j ≃* SuzukiMatrixGroup n) :=
  (radicalSection Q split j hKj).effectiveRepresentation.comp μ.symm.toMonoidHom

/-- In this section the source effective denominator is exactly Φ(U_sj). -/
theorem suzuki_radical_effectiveDenominator (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (radicalSection Q split j hKj).effectiveDenominator =
      frattini (simpleRemainder Q split j) := by
  rw [RootSection.effectiveDenominator_eq]
  exact sup_bot_eq _

/-- Both bounds concern the actual action space, with no irreducibility
premise and no perfectness premise on an original factor. -/
theorem suzuki_suzuki_radical_finrank_bounds (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    let d := Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier)
    4*(2*n+1) ≤ d ∧ d ≤ 3*(2*m+1)+2*(2*n+1) := by
  let d := radicalSection Q split j hKj
  have hc : Nat.card d.EffectiveCarrier =
      2 ^ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
  have hlo := suzuki_section_card_bound Q split j hn μj d
    (suzuki_radical_action_ne_one Q split j hhex i hij
      (UnitarySource.actorReflection Q split j) hKj)
  have hhi := suzuki_suzuki_radical_frattini_upper Q split hhex i j hij hm hn νi νj
  have he : Nat.card d.EffectiveCarrier =
      Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) := by
    change d.effectiveDenominator.index = _
    rw [suzuki_radical_effectiveDenominator Q split j hKj]
    rfl
  rw [← he,hc] at hhi
  rw [hc] at hlo
  exact ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hlo,
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hhi⟩

/-- The strict source degree window for unequal ordered Suzuki parameters. -/
theorem suzuki_suzuki_radical_degree_window (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m < n)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    let d := Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier)
    4*(2*n+1) ≤ d ∧ d < 5*(2*n+1) := by
  have hh := suzuki_suzuki_radical_finrank_bounds Q split hhex i j hij hKj hm hn μj νi νj
  dsimp only at hh ⊢
  omega

/-- A literal invariant subquotient of the source radical module is natural.
The output includes its actual Suzuki intertwiner, including when m=n. -/
theorem suzuki_suzuki_radical_natural_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) :
    ∃ U : Subrepresentation (suzukiRadicalRepresentation Q split j hKj μj),
      ∃ N : Subrepresentation U.toRepresentation,
        N.quotientRepresentation.IsIrreducible ∧
        Nonempty (N.quotientRepresentation.Equiv (Representation.SuzukiNatural.natural n)) ∧
        Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 4*(2*n+1) := by
  let ρ := suzukiRadicalRepresentation Q split j hKj μj
  have hf : Function.Injective ρ :=
    ((radicalSection Q split j hKj).effectiveRepresentation_injective
      (suzuki_section_effectiveAction_injective Q split j hn μj _
        (suzuki_radical_action_ne_one Q split j hhex i hij
          (UnitarySource.actorReflection Q split j) hKj))).comp μj.symm.injective
  let : IsSimpleGroup (SuzukiMatrixGroup n) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  have hne : ρ ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := exists_ne (1 : SuzukiMatrixGroup n)
    exact hg (hf (by rw [he]; rfl))
  have hd := (suzuki_suzuki_radical_finrank_bounds Q split hhex i j hij hKj hm hn μj νi νj).2
  have hsmall : Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier) < 10*(2*n+1) := by omega
  obtain ⟨U,N,hi,⟨e⟩⟩ := Representation.SuzukiSmallDegree.exists_natural_section hn ρ hne hsmall
  exact ⟨U,N,hi,⟨e⟩,e.toLinearEquiv.finrank_eq.trans (Representation.SuzukiNatural.natural_finrank n)⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
