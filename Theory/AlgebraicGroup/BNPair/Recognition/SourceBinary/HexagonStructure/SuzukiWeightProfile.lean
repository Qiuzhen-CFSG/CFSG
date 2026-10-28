module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanSection

/-!
# The five Cartan-equivariant maps onto the radical quotient

Each canonical root inclusion induces a map from its Frattini quotient to
U_sj/Φ(U_sj). These are intertwiners for literal H-conjugation. The ordered
five-root coordinates prove that their images span the entire radical quotient.
The denominator is the actual effective denominator, already identified with
Φ(U_sj); the first coordinate uses rootAt i 1 = U_i.

The root indices are i,j,i,j,i and the right-conjugation words are exactly
1,s_i,s_j s_i,s_i s_j,s_j. No assertion of independent images is made.
Source: Fong--Seitz I (6C), printed pp.39–40.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

@[expose] def radicalHRepresentation (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :=
  (radicalCartanRepresentation Q split j hKj).comp
    (inclusion (show Q.tits.B ⊓ Q.tits.N ≤ radicalCartanActor Q split j from le_sup_left))

@[expose] def rootFrattiniToRadical (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (k : Fin 2) (w : Weyl Q) (hA : rootAt Q split k w ≤ simpleRemainder Q split j) :
    (rootAt Q split k w ⧸ frattini (rootAt Q split k w)) →*
      (radicalSection Q split j hKj).EffectiveCarrier :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (radicalSection Q split j hKj).effectiveDenominator).comp (inclusion hA))
    (by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [suzuki_radical_effectiveDenominator Q split j hKj]
      let : Fact (IsPGroup 2 (simpleRemainder Q split j)) := ⟨split.isTwo.to_le inf_le_left⟩
      exact frattini_map_le_of_isPGroup (p := 2) (inclusion hA) (mem_map_of_mem _ hx))

@[expose] def rootFrattiniIntertwiner (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (k : Fin 2) (w : Weyl Q) (hA : rootAt Q split k w ≤ simpleRemainder Q split j) :
    (rootAtCartanFrattiniRepresentation Q split k w).IntertwiningMap
      (radicalHRepresentation Q split j hKj) where
  toLinearMap := (rootFrattiniToRadical Q split j hKj k w hA).toAdditive.toZModLinearMap 2
  isIntertwining' h := by
    ext v
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (frattini (rootAt Q split k w)) v.toMul
    have hv : v = Additive.ofMul ((QuotientGroup.mk' (frattini (rootAt Q split k w))) x) :=
      congrArg Additive.ofMul hx.symm
    rw [hv]
    change Additive.ofMul ((rootFrattiniToRadical Q split j hKj k w hA)
      ((quotientAut (frattini (rootAt Q split k w))) (rootAction Q split k w h)
        (QuotientGroup.mk' _ x))) = _
    rw [quotientAut_apply_mk]
    rfl

@[expose] def radicalRootKind (i j : Fin 2) : Fin 5 → Fin 2 := ![i,j,i,j,i]
@[expose] def radicalRootWord (i j : Fin 2) : Fin 5 → Weyl Q :=
  ![1,Q.simple i,Q.simple j*Q.simple i,Q.simple i*Q.simple j,Q.simple j]

theorem radicalRoot_le (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (t : Fin 5) : rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤
      simpleRemainder Q split j := by
  fin_cases t <;> dsimp [radicalRootKind,radicalRootWord]
  · rw [rootAt_one]; exact simpleRoot_le_other_remainder Q split hhex i j hij
  · exact (show rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hhex i j hij)
  · exact (exchanged_roots_le_remainder Q split hhex i j hij).2
  · exact (show rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j from
      le_sup_right).trans (middleRoots_le_remainder Q split hhex i j hij)
  · exact (exchanged_roots_le_remainder Q split hhex i j hij).1

@[expose] def radicalRootIntertwiner (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (t : Fin 5) := rootFrattiniIntertwiner Q split j hKj
      (radicalRootKind i j t) (radicalRootWord Q i j t) (radicalRoot_le Q split hhex i j hij t)

/-- The five actual root Frattini maps generate the same radical quotient. -/
theorem radical_root_intertwiners_span (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (⨆ t : Fin 5, (radicalRootIntertwiner Q split hhex i j hij hKj t).range) = ⊤ := by
  let ρ := radicalHRepresentation Q split j hKj
  let J : Subrepresentation ρ := ⨆ t : Fin 5,
    (radicalRootIntertwiner Q split hhex i j hij hKj t).range
  let d := radicalSection Q split j hKj
  let q := QuotientGroup.mk' d.effectiveDenominator
  have hmem (t : Fin 5)
      (x : rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)) :
      Additive.ofMul (q (inclusion (radicalRoot_le Q split hhex i j hij t) x)) ∈ J := by
    have hle : (radicalRootIntertwiner Q split hhex i j hij hKj t).range ≤ J := by
      dsimp only [J,ρ]
      exact le_iSup (fun u => (radicalRootIntertwiner Q split hhex i j hij hKj u).range) t
    apply hle
    exact ⟨Additive.ofMul (QuotientGroup.mk x),rfl⟩
  apply top_unique
  intro z _
  obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator z.toMul
  have hz : z = Additive.ofMul (q v) := congrArg Additive.ofMul hv.symm
  rw [hz]
  obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hhex i j hij).surjective v
  let a' : rootAt Q split i 1 := ⟨a,by rw [rootAt_one]; exact a.property⟩
  have h0 := hmem 0 a'
  have h1 := hmem 1 b
  have h2 := hmem 2 c
  have h3 := hmem 3 d
  have h4 := hmem 4 e
  have hsum := J.toSubmodule.add_mem (J.toSubmodule.add_mem
    (J.toSubmodule.add_mem (J.toSubmodule.add_mem h0 h1) h2) h3) h4
  have hprod : inclusion (radicalRoot_le Q split hhex i j hij 0) a' *
      inclusion (radicalRoot_le Q split hhex i j hij 1) b *
      inclusion (radicalRoot_le Q split hhex i j hij 2) c *
      inclusion (radicalRoot_le Q split hhex i j hij 3) d *
      inclusion (radicalRoot_le Q split hhex i j hij 4) e = v := by
    apply Subtype.ext
    exact (radicalCoordinates_apply Q split hhex i j hij (a,b,c,d,e)).symm.trans
      (congrArg Subtype.val he)
  change Additive.ofMul (q _ * q _ * q _ * q _ * q _) ∈ J.toSubmodule at hsum
  simp only [← map_mul,hprod] at hsum
  dsimp only [J,ρ] at hsum
  exact hsum

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
