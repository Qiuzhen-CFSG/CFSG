module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MixedNorm
/-!
# Complete positive equations for the synchronized U₅ roots

The whole B–A norm law polarizes to the C–A trace law: apply a fixed
central element of B to A(a+c), expand in two ways and cancel. The actual
source subgroup commutators supply the other three commuting pairs.
Together with the constructed B–D pairing these are all six positive
relations in the unitary presentation. The B–D pairing also forces the
remaining linear Cartan weight on C from its full actions on B and D.

The synchronized root maps keep their exact source ranges. The existing
ordered-root bijection supplies uniqueness and coverage of the whole U;
no generation assumption is introduced. PositiveApplication discharges
both mixed-law premises from the original profile and generic cover.
Source: Fong--Seitz II (8C), pp.206--209, (8.20)--(8.31).
-/

open Subgroup
open scoped MatrixGroups
@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
section Trace
variable {E Y : Type*} [Field E] [CharP E 2] [Group Y] (J : HermitianForm 5 E)
  (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter J)
    (Multiplicative E) (FivePositive.Parameter J))
  (hAD : ∀ a d, Commute (r.A a) (r.D d))
  (hCD : ∀ c d, Commute (r.C c) (r.D d))
  (hBA : ∀ (p : FivePositive.Parameter J) a, r.B p*r.A (.ofAdd a) =
    r.A (.ofAdd a)*r.D (FivePositive.normParameter J a p)*r.C (.ofAdd (a*J.conj p.val.2))*r.B p)

include hAD hCD hBA in
/-- The exact B–A norm law polarizes to the short-short trace law. -/
theorem trace_crossing_of_norm (a c : E) :
    r.C (.ofAdd c)*r.A (.ofAdd a) =
      r.A (.ofAdd a)*r.D (FivePositive.traceParameter J a c)*r.C (.ofAdd c) := by
  let p₀ : FivePositive.Parameter J := ⟨(0,1),by simp [CharTwo.add_self_eq_zero]⟩
  let np (z : E) := FivePositive.normParameter J z p₀
  have hconj (z : E) : r.B p₀*r.A (.ofAdd z)*(r.B p₀)⁻¹ =
      r.A (.ofAdd z)*r.D (np z)*r.C (.ofAdd z) := by
    rw [hBA,mul_inv_cancel_right]
    simp only [p₀,map_one,mul_one]
    rfl
  have hadd : r.A (.ofAdd c)*r.D (np c)*r.C (.ofAdd c)*
      (r.A (.ofAdd a)*r.D (np a)*r.C (.ofAdd a)) =
      r.A (.ofAdd (c+a))*r.D (np (c+a))*r.C (.ofAdd (c+a)) := by
    rw [←hconj,←hconj,←hconj]
    have hA : r.A (.ofAdd (c+a)) = r.A (.ofAdd c)*r.A (.ofAdd a) := r.A.map_mul _ _
    rw [hA]
    group
  have hparam : (np c)⁻¹*np (c+a)*(np a)⁻¹ = FivePositive.traceParameter J a c := by
    apply Subtype.ext
    change (hermitianUnipotentMul J (hermitianUnipotentMul J (hermitianUnipotentInv J (np c)) (np (c+a)))
      (hermitianUnipotentInv J (np a))).val = _
    apply Prod.ext <;> simp [hermitianUnipotentMul,hermitianUnipotentInv,np,p₀,
      FivePositive.normParameter,FivePositive.traceParameter]
    ring_nf
    simp [CharTwo.two_eq_zero]
  calc
    _ = (r.A (.ofAdd c)*r.D (np c))⁻¹*
      (r.A (.ofAdd c)*r.D (np c)*r.C (.ofAdd c)*
        (r.A (.ofAdd a)*r.D (np a)*r.C (.ofAdd a)))*(r.D (np a)*r.C (.ofAdd a))⁻¹ := by group
    _ = (r.D (np c))⁻¹*r.A (.ofAdd a)*r.D (np (c+a))*r.C (.ofAdd c)*(r.D (np a))⁻¹ := by
      rw [hadd,show r.A (.ofAdd (c+a)) = r.A (.ofAdd c)*r.A (.ofAdd a) from r.A.map_mul _ _,
        show r.C (.ofAdd (c+a)) = r.C (.ofAdd c)*r.C (.ofAdd a) from r.C.map_mul _ _]
      group
    _ = r.A (.ofAdd a)*((r.D (np c))⁻¹*r.D (np (c+a))*(r.D (np a))⁻¹)*r.C (.ofAdd c) := by
      rw [(hAD (.ofAdd a) (np c)).symm.inv_left.eq]
      calc
        _ = r.A (.ofAdd a)*(r.D (np c))⁻¹*r.D (np (c+a))*(r.C (.ofAdd c)*(r.D (np a))⁻¹) := by group
        _ = _ := by rw [(hCD (.ofAdd c) (np a)).inv_right.eq]; group
    _ = _ := by rw [←map_inv,←map_mul,←map_inv,←map_mul,hparam]
end Trace

open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j)) (ξ : E ≃+* K)

/-- The four synchronized source charts, in the presentation's literal parameter groups. -/
def synchronizedRoots : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (FivePositive.Parameter (fiveForm J)) (Multiplicative E) (FivePositive.Parameter (fiveForm J)) where
  A := (alignedSimpleParameter Q split i hVi μ s).comp
    (AddEquiv.toMultiplicative ξ.toAddEquiv).toMonoidHom
  D := (rootAt Q split j (Q.simple i)).subtype.comp (reflectedUnitaryChart Q split i j s b).toMonoidHom
  C := (rootAt Q split i (Q.simple j)).subtype.comp γ.toMonoidHom
  B := (simpleRoot Q split j).subtype.comp b.toMonoidHom

local notation "R" => synchronizedRoots Q split i j hVi s μ J b γ ξ

omit [CharP E 2] in
/-- The simple linear coordinate is the literal aligned source parameter. -/
theorem synchronizedRoots_A (a : E) :
    (R).A (.ofAdd a) = alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a)) := rfl


omit [CharP E 2] in
/-- The synchronized labels retain all four entire source roots. -/
theorem synchronizedRoots_ranges :
    (R).A.range = simpleRoot Q split i ∧ (R).D.range = rootAt Q split j (Q.simple i) ∧
    (R).C.range = rootAt Q split i (Q.simple j) ∧ (R).B.range = simpleRoot Q split j := by
  refine ⟨?_,?_,?_,?_⟩
  · change ((alignedSimpleParameter Q split i hVi μ s).comp
      (AddEquiv.toMultiplicative ξ.toAddEquiv).toMonoidHom).range = _
    have he : (AddEquiv.toMultiplicative ξ.toAddEquiv).toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (AddEquiv.toMultiplicative ξ.toAddEquiv).surjective
    rw [MonoidHom.range_comp,he,←MonoidHom.range_eq_map,alignedSimpleParameter_range]
  · change ((rootAt Q split j (Q.simple i)).subtype.comp (reflectedUnitaryChart Q split i j s b).toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (reflectedUnitaryChart Q split i j s b).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  · change ((rootAt Q split i (Q.simple j)).subtype.comp γ.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr γ.surjective,←MonoidHom.range_eq_map,range_subtype]
  · change ((simpleRoot Q split j).subtype.comp b.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr b.surjective,←MonoidHom.range_eq_map,range_subtype]

omit [CharP E 2] in
/-- The synchronized coordinates remain faithful on every whole root. -/
theorem synchronizedRoots_injective :
    Function.Injective (R).A ∧ Function.Injective (R).D ∧ Function.Injective (R).C ∧ Function.Injective (R).B :=
  ⟨(alignedSimpleParameter_injective Q split i hVi μ s).comp (AddEquiv.toMultiplicative ξ.toAddEquiv).injective,
    Subtype.val_injective.comp (reflectedUnitaryChart Q split i j s b).injective,
    Subtype.val_injective.comp γ.injective,Subtype.val_injective.comp b.injective⟩

variable (hm : rotationOrder Q = 4) (hij : i ≠ j)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)

include hm hij in
omit [CharP E 2] in
/-- Existing ordered-root coordinates apply to these exact synchronized charts. -/
theorem synchronizedRoots_coordinates :
    Function.Injective (chartWord Q R) ∧ Set.range (chartWord Q R) = (split.U : Set (X ⧸ Q.D)) ∧
      (R).generated = split.U := by
  obtain ⟨ha,hd,hc,hb⟩ := synchronizedRoots_ranges Q split i j hVi s μ J b γ ξ
  have hj : j = 1-i := by fin_cases i <;> fin_cases j <;> first | rfl | exact (hij rfl).elim
  have ho : orderedRoots Q split (decide (i=1)) (rotationOrder Q) =
      [(R).A.range,(R).D.range,(R).C.range,(R).B.range] := by
    rw [ha,hd,hc,hb,hj]
    exact ordered_four Q split hm i
  obtain ⟨hia,hid,hic,hib⟩ := synchronizedRoots_injective Q split i j hVi s μ J b γ ξ
  exact ⟨chartWord_injective Q split R _ ho hia hid hic hib,
    chartWord_range Q split R _ ho,charts_generated Q split R _ ho⟩

include hm hij hVj in
omit [CharP E 2] in
/-- Source subgroup commutators give the three commuting pairs for the synchronized charts. -/
theorem synchronizedRoots_commuting :
    (∀ a d, Commute ((R).A a) ((R).D d)) ∧
    (∀ c d, Commute ((R).C c) ((R).D d)) ∧
    (∀ b c, Commute ((R).B b) ((R).C c)) := by
  obtain ⟨ha,hd,hc,hb⟩ := synchronizedRoots_ranges Q split i j hVi s μ J b γ ξ
  have aux {U V : Subgroup (X ⧸ Q.D)} (he : ⁅U,V⁆ = ⊥)
      {u v : X ⧸ Q.D} (hu : u ∈ U) (hv : v ∈ V) : Commute u v :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he hu) v hv).symm
  refine ⟨fun a d => aux (adjacent_roots_commute Q split hm i j hij hVi hVj)
    (ha ▸ ⟨a,rfl⟩) (hd ▸ ⟨d,rfl⟩),
    fun c d => aux (middle_roots_commute Q split hm i j hij hVi hVj)
      (hc ▸ ⟨c,rfl⟩) (hd ▸ ⟨d,rfl⟩),
    fun b c => aux (adjacent_roots_commute Q split hm j i hij.symm hVj hVi)
      (hb ▸ ⟨b,rfl⟩) (hc ▸ ⟨c,rfl⟩)⟩

include hm hij hVj in
/-- The two constructed mixed laws complete all six positive relations;
the trace law is deduced by polarization, not supplied. -/
theorem synchronizedRoots_relations
    (hBA : ∀ p a, (b p : X ⧸ Q.D)*alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a)) =
      alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a))*
        (reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) a p) : X ⧸ Q.D)*
        (γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D))
    (hBD : ∀ p q : hermitianUnipotentCoord J,
      (b p : X ⧸ Q.D)*(reflectedUnitaryChart Q split i j s b q : X ⧸ Q.D) =
        (reflectedUnitaryChart Q split i j s b q : X ⧸ Q.D)*
          (γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D)) :
    FivePositive.Relations (fiveForm J) R := by
  obtain ⟨hAD,hCD,hBC⟩ := synchronizedRoots_commuting Q split i j hVi s μ J b γ ξ hm hij hVj
  exact ⟨hAD,hCD,hBC,trace_crossing_of_norm (fiveForm J) R hAD hCD hBA,hBD,fun a p => hBA p a⟩


section Cartan
variable {Y : Type*} [Group Y]
  (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter (fiveForm J))
    (Multiplicative E) (FivePositive.Parameter (fiveForm J)))

omit [CharP E 2] in
/-- The B–D pairing determines the Cartan weight on C from its full B,D actions. -/
theorem crossed_scaling_of_unitary_scaling
    (hfirst : ∀ x : E, ∃ p : hermitianUnipotentCoord J, p.val.1 = x)
    (hBD : ∀ p q : hermitianUnipotentCoord J, r.B p*r.D q =
      r.D q*r.C (.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (u : Eˣ) (α : Y ≃* Y)
    (hB : ∀ p : hermitianUnipotentCoord J, α (r.B p) = r.B (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p))
    (hD : ∀ p : hermitianUnipotentCoord J, α (r.D p) = r.D (FivePositive.normParameter (fiveForm J) (u:E) p))
    (c : E) : α (r.C (.ofAdd c)) = r.C (.ofAdd (((u:E)/J.conj (u:E))*c)) := by
  have hcomm (p q : hermitianUnipotentCoord J) :
      (r.D q)⁻¹*r.B p*r.D q*(r.B p)⁻¹ = r.C (.ofAdd (q.val.1*J.conj p.val.1)) := by
    calc
      _ = (r.D q)⁻¹*(r.B p*r.D q)*(r.B p)⁻¹ := by group
      _ = _ := by rw [hBD]; group
  obtain ⟨p,hp⟩ := hfirst 1
  obtain ⟨q,hq⟩ := hfirst c
  calc
    _ = α ((r.D q)⁻¹*r.B p*r.D q*(r.B p)⁻¹) := by rw [hcomm,hp,hq,map_one,mul_one]
    _ = (r.D (FivePositive.normParameter (fiveForm J) (u:E) q))⁻¹*
        r.B (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p)*
        r.D (FivePositive.normParameter (fiveForm J) (u:E) q)*
        (r.B (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p))⁻¹ := by
      simp only [map_mul,map_inv,hB,hD]
    _ = _ := (hcomm (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p)
      (FivePositive.normParameter (fiveForm J) (u:E) q)).trans
      (congrArg (fun x : E => r.C (.ofAdd x)) (by
        change ((u:E)*q.val.1)*J.conj ((↑u⁻¹:E)*p.val.1) = _
        rw [hp,hq,mul_one,Units.val_inv_eq_inv_val,map_inv₀]
        simp only [div_eq_mul_inv]
        ring))
end Cartan

omit [CharP E 2] in
/-- Pointwise linear Cartan equations on all four synchronized roots.
This boundary keeps the original-profile application from unfolding its actor construction. -/
theorem synchronizedRoots_linear_cartan
    (hfirst : ∀ x : E, ∃ p : hermitianUnipotentCoord J, p.val.1 = x)
    (hBD : ∀ p q : hermitianUnipotentCoord J,
      (b p : X ⧸ Q.D)*(reflectedUnitaryChart Q split i j s b q : X ⧸ Q.D) =
        (reflectedUnitaryChart Q split i j s b q : X ⧸ Q.D)*
          (γ (.ofAdd (q.val.1*J.conj p.val.1)) : X ⧸ Q.D)*(b p : X ⧸ Q.D))
    (hB : ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
      let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
      H*(b p : X ⧸ Q.D)*H⁻¹ = b (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p))
    (hD : ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
      let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
      H*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*H⁻¹ =
        reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) (u:E) p)) :
    (∀ (u : Eˣ) (a : E),
      let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
      H*(R).A (.ofAdd a)*H⁻¹ = (R).A (.ofAdd ((u:E)^2*a))) ∧
    (∀ (u : Eˣ) (c : E),
      let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
      H*(R).C (.ofAdd c)*H⁻¹ = (R).C (.ofAdd (((u:E)/J.conj (u:E))*c))) ∧
    ∀ (u : Eˣ) (p : hermitianUnipotentCoord J),
      let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
      H*(b p : X ⧸ Q.D)*H⁻¹ = b (FivePositive.normParameter (fiveForm J) (↑u⁻¹:E) p) ∧
      H*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*H⁻¹ =
        reflectedUnitaryChart Q split i j s b (FivePositive.normParameter (fiveForm J) (u:E) p) := by
  refine ⟨?_,?_,fun u p => ⟨hB u p,hD u p⟩⟩
  · intro u a
    dsimp only
    rw [synchronizedRoots_A,synchronizedRoots_A]
    rw [map_mul,map_pow]
    exact alignedTorus_root Q split i hVi μ s (Units.map ξ.toMonoidHom u) (ξ a)
  · intro u c0
    exact crossed_scaling_of_unitary_scaling J R hfirst hBD u
      (MulAut.conj (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u))) (hB u) (hD u) c0

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
