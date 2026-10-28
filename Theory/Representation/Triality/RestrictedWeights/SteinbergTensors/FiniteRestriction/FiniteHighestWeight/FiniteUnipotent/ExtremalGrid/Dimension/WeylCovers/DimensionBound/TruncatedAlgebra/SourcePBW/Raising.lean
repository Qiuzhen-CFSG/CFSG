module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW.Lowering
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW.Weights

/-!
# Raising coefficients preserve the lowering-word span

A simple raising coefficient is moved through one lowering coefficient at a
time. Nonopposite exchange creates only lowering roots and smaller raising
orders. For an opposite pair, the actual rescaled SL2 straightening identity
applies to the torus eigenvector formed by the remaining word. Its coefficient
orders stay below the original truncation. The highest-vector endpoint kills
every nonconstant raising coefficient.

This argument includes zero intermediate vectors and both Borel signs.
Source: Steinberg (1963), sections 2–3, with the literal supplied parameters.
-/

open Theory.AlgebraicGroup CoefficientPBW
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
def raisingRoot (S:Geometry K) (negative:Bool) (i:Fin 4) : S.roots.Root :=
  S.roots.neg (turn S negative (S.simpleRoot i).val)
omit [IsAlgClosed k] in
lemma raising_ne_side (S:Geometry K) (negative:Bool) (i:Fin 4) (j:Fin 12) :
    raisingRoot S negative i ≠ sideRoot S negative j := by
  obtain ⟨l,hl⟩ := simple_side_mem S negative i
  exact fun h=>sideRoot_no_opposite S negative l j (h.symm.trans (congrArg S.roots.neg hl.symm))
lemma sideWord_weight (S:Geometry K) (rho:RationalRepresentation K V)
    (hr:IsRationalRepresentation rho) (negative:Bool) (q:ℕ)
    {χ:TorusWeight S.torus} {v:V} (hv:v∈weightSpace rho S.torus χ)
    (w:List (Fin 12 × Fin q)) :
    ∃ψ:TorusWeight S.torus,wordValue (sideCoefficient S rho hr negative q) w v∈weightSpace rho S.torus ψ := by
  induction w with
  | nil => exact ⟨χ,hv⟩
  | cons a w ih =>
    obtain ⟨ψ,hψ⟩ := ih
    exact ⟨_,rootCoefficient_weight S rho hr (sideRoot S negative a.1) a.2 hψ⟩
lemma opposite_on_weight (S:Geometry K) (negative:Bool) (i:Fin 4) (C:SimpleRootSL2Chart S i)
    (rho:RationalRepresentation K V) (hr:IsRationalRepresentation rho)
    {χ:TorusWeight S.torus} {z:V} (hz:z∈weightSpace rho S.torus χ) (a b:ℕ) :
    ∃f:ℕ→k,rootCoefficient S rho hr (raisingRoot S negative i) a
      (rootCoefficient S rho hr (turn S negative (S.simpleRoot i).val) b z) =
        ∑t∈Finset.range (min a b+1),f t • rootCoefficient S rho hr
          (turn S negative (S.simpleRoot i).val) (b-t)
          (rootCoefficient S rho hr (raisingRoot S negative i) (a-t) z) := by
  obtain ⟨m,hm⟩ := rankOne_weight_of_torus S i C rho hz
  obtain ⟨c,d,_,_,hh⟩ := rankOneChart_actual_straightening S i C rho hr
  cases negative
  · refine ⟨fun t=>(c*d)^t*((Ring.choose (-m+(a:ℤ)-(b:ℤ)) t:ℤ):k),?_⟩
    simpa only [raisingRoot,turn,Bool.false_eq_true,if_false,min_comm] using (hh m z hm b a).2
  · refine ⟨fun t=>(c*d)^t*((Ring.choose (m+(a:ℤ)-(b:ℤ)) t:ℤ):k),?_⟩
    simpa only [raisingRoot,turn,if_true,S.realized.neg_neg] using (hh m z hm a b).1
lemma raising_word_mem (S:Geometry K) (hrel:RootPairParameterRelations S)
    (negative:Bool) (i:Fin 4) (C:SimpleRootSL2Chart S i)
    (rho:RationalRepresentation K V) (hr:IsRationalRepresentation rho) (q:ℕ)
    {χ:TorusWeight S.torus} {v:V} (hv:v∈weightSpace rho S.torus χ)
    (hkill:∀j:ℕ,j ≠ 0 → rootCoefficient S rho hr (raisingRoot S negative i) j v=0)
    (a:ℕ) (ha:a<q) (w:List (Fin 12 × Fin q)) :
    rootCoefficient S rho hr (raisingRoot S negative i) a
      (wordValue (sideCoefficient S rho hr negative q) w v)∈
        operatorOrbit (sideAlgebra S rho hr negative q) v := by
  let U:=operatorOrbit (sideAlgebra S rho hr negative q) v
  have low (j:Fin 12) (b:ℕ) (hb:b<q) (z:V) (hz:z∈U) :
      rootCoefficient S rho hr (sideRoot S negative j) b z∈U :=
    operatorOrbit_stable _ v _ (sideCoefficient_mem S rho hr negative q j b hb) z hz
  induction w generalizing a with
  | nil =>
    by_cases hz:a=0
    · subst a
      simpa only [wordValue_nil,Module.End.one_apply,rootCoefficient,curveCoefficient_zero] using
        mem_operatorOrbit (sideAlgebra S rho hr negative q) v
    · simpa only [wordValue_nil,Module.End.one_apply,hkill a hz] using U.zero_mem
  | cons b w ih =>
    obtain ⟨ψ,hψ⟩ := sideWord_weight S rho hr negative q hv w
    change rootCoefficient S rho hr (raisingRoot S negative i) a
      (rootCoefficient S rho hr (sideRoot S negative b.1) b.2
        (wordValue (sideCoefficient S rho hr negative q) w v))∈U
    by_cases hop:sideRoot S negative b.1=turn S negative (S.simpleRoot i).val
    · rw [hop]
      obtain ⟨f,hf⟩ := opposite_on_weight S negative i C rho hr hψ a b.2
      rw [hf]
      apply U.sum_mem
      intro t ht
      have htq:a-t<q := lt_of_le_of_lt (Nat.sub_le _ _) ha
      apply U.smul_mem
      rw [←hop]
      exact low b.1 _ (lt_of_le_of_lt (Nat.sub_le _ _) b.2.isLt) _ (ih _ htq)
    · have hop':sideRoot S negative b.1≠S.roots.neg (raisingRoot S negative i) := by
        simpa only [raisingRoot,S.realized.neg_neg] using hop
      by_cases hs:∃c,RootSum S (raisingRoot S negative i) (sideRoot S negative b.1) c
      · obtain ⟨c,hc⟩ := hs
        obtain ⟨l,rfl⟩ := raising_sum_closed S negative i b.1 c hc
        obtain ⟨κ,_,he⟩ := rootCoefficient_exchange_of_parameterRelations S hrel rho hr _ _ _ hc
        have hh:=LinearMap.congr_fun (he a b.2) (wordValue (sideCoefficient S rho hr negative q) w v)
        change rootCoefficient S rho hr (raisingRoot S negative i) a
          (rootCoefficient S rho hr (sideRoot S negative b.1) b.2
            (wordValue (sideCoefficient S rho hr negative q) w v))=_ at hh
        rw [hh]
        simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
        apply U.sum_mem
        intro t ht
        have htmin:=Finset.mem_range.mp ht
        have htq:t<q := by omega
        apply U.smul_mem
        exact low b.1 _ (lt_of_le_of_lt (Nat.sub_le _ _) b.2.isLt) _
          (low l t htq _ (ih _ (lt_of_le_of_lt (Nat.sub_le _ _) ha)))
      · have he:=rootCoefficient_commute_of_parameterRelations S hrel rho hr _ _
          (raising_ne_side S negative i b.1) hop' hs a b.2
        have hh:=LinearMap.congr_fun he.eq (wordValue (sideCoefficient S rho hr negative q) w v)
        change rootCoefficient S rho hr (raisingRoot S negative i) a
          (rootCoefficient S rho hr (sideRoot S negative b.1) b.2
            (wordValue (sideCoefficient S rho hr negative q) w v))=_ at hh
        rw [hh]
        exact low b.1 b.2 b.2.isLt _ (ih a ha)
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
