module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.AbelianPerpendicular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OmegaNonzero
public import Theory.GroupAction.SubgroupConjugation

/-!
# Both terminal binary branches of source (6H)(b)

The actual binary Suzuki root is cyclic of order four. If the near
commutator vanishes and (6.4) is nonzero, its Cartan upgrade and the six-root
three-subgroup argument force perpendicular Omega centralization. The
quintic normalization and (6.1) then contradict the trivial near commutator.

If both commutators vanish, (6.1) identifies the whole root centralizer
with three consecutive factors of order sixteen. The actual quintic fixed
subgroup has order four and is normalized by the simple root, so the
p-group fixed-point theorem gives a nonidentity point commuting with both
the root and its reflection. Reflecting its three coordinates and using
unique ordered multiplication forces that point to be the identity.

Together these arguments prove the binary near commutator is the whole
intervening linear root, without a movement or nonzero premise. Natural
faithful-panel markings and the actual linear size bound remain explicit;
rank-one pairing and the positive-parameter branch are not asserted here.

Source: Fong--Seitz I (1973), p.53. OriginalNearEquality retains both original
endpoint orientations, full markings and the literal generated quotient Q.q.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
  (n : ℕ) (hn : 0 < n)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k=1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2

include μ hB ν hC in
private theorem binary_centralizer_three_factors
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) = 2)
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hfour : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥)
    (x : X ⧸ Q.D)
    (hx : x ∈ simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))) :
    ∃ b : rootAt Q split j (Q.simple i), ∃ c : rootAt Q split i (Q.simple j*Q.simple i),
      ∃ d : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i),
        (b : X ⧸ Q.D)*(c : X ⧸ Q.D)*(d : X ⧸ Q.D) = x := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)
  let Z := simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))
  have hV := octagon_three_roots_le_remainder Q split hm i j hij
  have hV' := octagon_three_roots_le_remainder Q split hm j i hij.symm
  have hDV : D ≤ simpleRemainder Q split i := by
    apply le_inf (hV'.2.2.trans inf_le_left)
    have hh := comap_mono (f := (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom)
      (hV'.2.1.trans inf_le_left)
    change rightConjugate (rootAt Q split j (Q.simple i*Q.simple j))
      (representative (Q.simple i) : X ⧸ Q.D) ≤ unipotentConjugate split (Q.simple i) at hh
    rwa [rootAt_right Q split j _ _ _ (representative_spec _)] at hh
  have hBZ : B ≤ Z := le_inf hV.1 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (adjacent_commutator_eq_bot Q split hm i j hij
      (marked_suzuki_remainder_le_kernel Q split i 0 μ hB)
      (marked_linear_remainder_le_kernel Q split j ν T hC))))
  have hCZ : C ≤ Z := le_inf hV.2.1
    (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hnear))
  have hDZ : D ≤ Z := le_inf hDV
    (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hfour))
  let f : B × C × D → Z := fun p => ⟨(p.1 : X ⧸ Q.D)*(p.2.1 : X ⧸ Q.D)*(p.2.2 : X ⧸ Q.D),
    Z.mul_mem (Z.mul_mem (hBZ p.1.property) (hCZ p.2.1.property)) (hDZ p.2.2.property)⟩
  have hf : Function.Injective f := by
    intro p q he
    have hh := octagon_six_root_product_injective Q split hm i j hij
      (a₁ := (p.1,p.2.1,p.2.2,1,1,1)) (a₂ := (q.1,q.2.1,q.2.2,1,1,1))
      (by simpa only [OneMemClass.coe_one,mul_one] using congrArg Subtype.val he)
    exact Prod.ext (congrArg (fun z => z.1) hh) (Prod.ext (congrArg (fun z => z.2.1) hh)
      (congrArg (fun z => z.2.2.1) hh))
  have hjcard (w : Weyl Q) : Nat.card (rootAt Q split j w) = 2 := by
    change Nat.card (rightConjugate (simpleRoot Q split j) (representative w : X ⧸ Q.D)) = 2
    rw [Nat.card_congr (rightConjugateEquiv (simpleRoot Q split j) (representative w)).symm,
      Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (BinaryGaloisField n) ≃ _),hsize]
  have hprod : Nat.card (B × C × D) = 16 := by
    rw [Nat.card_prod,Nat.card_prod]
    dsimp only [B,C,D]
    rw [hjcard,hjcard]
    change 2 * (Nat.card (rightConjugate (simpleRoot Q split i)
      (representative (Q.simple j*Q.simple i) : X ⧸ Q.D))*2) = 16
    rw [Nat.card_congr (rightConjugateEquiv (simpleRoot Q split i)
        (representative (Q.simple j*Q.simple i))).symm,
      Nat.card_congr (suzukiRootEquiv Q split i 0 μ hB).toEquiv,matrixRoot_card]
    norm_num
  have hZcard : Nat.card Z = 16 := by
    have hlo := Nat.card_le_card_of_injective f hf
    rw [hprod] at hlo
    have hup := (source_six_one Q split i j ν T hC 0 μ hB hc hm hij (by simpa using hsize.le)).1
    rw [hsize] at hup
    exact le_antisymm hup hlo
  let : Fintype (B × C × D) := Fintype.ofFinite _
  let : Fintype Z := Fintype.ofFinite _
  have hs : Function.Surjective f := ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf,by simpa only [←Nat.card_eq_fintype_card] using hprod.trans hZcard.symm⟩).2
  obtain ⟨p,hp⟩ := hs ⟨x,hx⟩
  exact ⟨p.1,p.2.1,p.2.2,congrArg Subtype.val hp⟩

include μ hB ν hC in
/-- The two mixed commutators cannot both vanish in the binary source row. -/
theorem source_binary_not_both_commutators_trivial
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) = 2)
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hfour : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥) : False := by
  let s := involutoryRootReflection Q split i (UnitarySource.actorReflection Q split i)
  let c := frattiniMover Q split i 0 μ hB
  let F := simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))
  have hcomm := (source_six_three Q split i j 0 μ hB ν T hC hm hij).2
  have hV := marked_suzuki_remainder_le_kernel Q split i 0 μ hB
  have hlin : Nat.card (simpleRoot Q split j) = 2 := by
    rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (BinaryGaloisField n) ≃ _),hsize]
  have hFcard : Nat.card F = 4 :=
    binary_mover_centralizer_card Q split i hV μ hB hc hm j hij hcomm hlin
  let : Normalizes (simpleRoot Q split i) F := ⟨le_sup_left.trans
    (binary_mover_centralizer_normalized Q split i hV μ hB hm j hij hcomm)⟩
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨v,hv,hvne⟩ := (split.isTwo.to_le (simpleRoot_le Q split i)).exists_fixed_point_of_prime_dvd_card_of_fixed_point
    F (by rw [hFcard]; decide) (show (1 : F) ∈ MulAction.fixedPoints (simpleRoot Q split i) F by
      simp [MulAction.mem_fixedPoints])
  have hvC : (v : X ⧸ Q.D) ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    have hh := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hv (⟨u,hu⟩ : simpleRoot Q split i))
    change u*(v : X ⧸ Q.D)*u⁻¹ = v at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hvc : Commute (c : X ⧸ Q.D) (v : X ⧸ Q.D) :=
    mem_centralizer_iff.mp v.property.2 _ (Set.mem_singleton _)
  have hvu : Commute (suzukiParameter Q split i 0 μ hB 0 1 : X ⧸ Q.D) (v : X ⧸ Q.D) :=
    mem_centralizer_iff.mp hvC _ (suzukiParameter Q split i 0 μ hB 0 1).property
  have hvs : Commute (s.val : X ⧸ Q.D) (v : X ⧸ Q.D) := by
    have hh := hvc.mul_left hvu.inv_left
    change Commute ((s.val : X ⧸ Q.D)*(suzukiParameter Q split i 0 μ hB 0 1 : X ⧸ Q.D)*
      (suzukiParameter Q split i 0 μ hB 0 1 : X ⧸ Q.D)⁻¹) (v : X ⧸ Q.D) at hh
    simpa only [mul_inv_cancel_right] using hh
  obtain ⟨b,d,e,hfac⟩ := binary_centralizer_three_factors Q split i j μ hB n ν T hC hc hm hij hsize
    hnear hfour v ⟨v.property.1,hvC⟩
  let br := (s.val : X ⧸ Q.D)⁻¹*(b : X ⧸ Q.D)*s.val
  let dr := (s.val : X ⧸ Q.D)⁻¹*(d : X ⧸ Q.D)*s.val
  let er := (s.val : X ⧸ Q.D)⁻¹*(e : X ⧸ Q.D)*s.val
  have hbr : br ∈ simpleRoot Q split j := by
    have hh := (rightConjugateEquiv (rootAt Q split j (Q.simple i)) (s.val : X ⧸ Q.D) b).property
    simp only [rightConjugateEquiv_apply] at hh
    rw [rootAt_right Q split j _ _ s.val s.class_eq,ssq,rootAt_one] at hh
    exact hh
  have hdr : dr ∈ rootAt Q split i (Q.simple j) := by
    have hh := (rightConjugateEquiv (rootAt Q split i (Q.simple j*Q.simple i)) (s.val : X ⧸ Q.D) d).property
    simp only [rightConjugateEquiv_apply] at hh
    rw [rootAt_right Q split i _ _ s.val s.class_eq] at hh
    simpa only [dr,mul_assoc,ssq,mul_one] using hh
  have her : er ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    have hh := (rightConjugateEquiv (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i))
      (s.val : X ⧸ Q.D) e).property
    simp only [rightConjugateEquiv_apply] at hh
    rw [rootAt_right Q split j _ _ s.val s.class_eq] at hh
    simpa only [er,mul_assoc,ssq,mul_one] using hh
  have hfac' : br*dr*er = v := by
    dsimp only [br,dr,er]
    calc
      _ = (s.val : X ⧸ Q.D)⁻¹*((b : X ⧸ Q.D)*d*e)*s.val := by group
      _ = (s.val : X ⧸ Q.D)⁻¹*(v : X ⧸ Q.D)*s.val := by rw [hfac]
      _ = v := by rw [hvs.inv_left.eq,inv_mul_cancel_right]
  have hp : (b : X ⧸ Q.D)*d*e*er⁻¹*dr⁻¹*br⁻¹ = 1 := by
    calc
      _ = ((b : X ⧸ Q.D)*d*e)*(br*dr*er)⁻¹ := by simp only [mul_inv_rev,mul_assoc]
      _ = 1 := by rw [hfac,hfac',mul_inv_cancel]
  have heq := octagon_six_root_product_injective Q split hm i j hij
    (a₁ := (b,d,e,⟨er⁻¹,(rootAt Q split j (Q.simple i*Q.simple j)).inv_mem her⟩,
      ⟨dr⁻¹,(rootAt Q split i (Q.simple j)).inv_mem hdr⟩,
      ⟨br⁻¹,(simpleRoot Q split j).inv_mem hbr⟩)) (a₂ := (1,1,1,1,1,1))
    (by simpa only [OneMemClass.coe_one,mul_one] using hp)
  have hb1 : b = 1 := congrArg Prod.fst heq
  have hd1 : d = 1 := congrArg (fun z => z.2.1) heq
  have he1 : e = 1 := congrArg (fun z => z.2.2.1) heq
  have hv1 : (v : X ⧸ Q.D) = 1 := by
    rw [←hfac,hb1,hd1,he1]
    simp only [OneMemClass.coe_one,mul_one]
  exact hvne (Subtype.ext hv1.symm)

include μ hB hn ν hC in
/-- The nonzero-(6.4) branch of the binary source near-commutator equality. -/
theorem source_binary_near_eq_of_six_four_nonzero
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2)
    (hne : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≠ ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i) := by
  by_cases hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥
  · have hfour := source_six_four_eq_of_nonzero Q split i j 0 μ hB n hn ν T hC hc hm hij
      (by have hh := Nat.pow_le_pow_left hsize 4; norm_num at hh ⊢; omega) hne
    have hab : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥ := by
      let := binary_suzuki_root_cyclic Q split i μ hB
      let := IsCyclic.commGroup (α := simpleRoot Q split i)
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro x hx
      apply mem_centralizer_iff.mpr
      intro y hy
      exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : simpleRoot Q split i) ⟨x,hx⟩)
    have hΩ := abelian_omega_perpendicular_of_near_trivial_of_six_four Q split i j hm hij
      (marked_suzuki_remainder_le_kernel Q split i 0 μ hB)
      (marked_linear_remainder_le_kernel Q split j ν T hC) hab hnear hfour
    exact (source_near_eq_or_omega_perpendicular_nonzero Q split i j 0 μ hB n hn ν T hC
      hc hm hij (by simpa using hsize)).resolve_right (not_not.mpr hΩ)
  · exact source_near_eq_of_nonzero Q split i j 0 μ hB n hn ν T hC hm hij hnear

include μ hB hn ν hC in
/-- Only the simultaneous-zero near and (6.4) branch remains in the binary row. -/
theorem source_binary_near_eq_or_both_commutators_trivial
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
        rootAt Q split j (Q.simple i) ∨
      (⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
       ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥) := by
  by_cases hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥
  · by_cases hfour : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥
    · exact Or.inr ⟨hnear,hfour⟩
    · exact Or.inl (source_binary_near_eq_of_six_four_nonzero Q split i j μ hB n hn ν T hC
        hc hm hij hsize hfour)
  · exact Or.inl (source_near_eq_of_nonzero Q split i j 0 μ hB n hn ν T hC hm hij hnear)

include μ hB hn ν hC in
/-- The binary near-commutator equality, with both terminal p.53 branches discharged.
The natural panel markings and the actual source size bound remain explicit. -/
theorem source_binary_near_eq
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i) := by
  rcases source_binary_near_eq_or_both_commutators_trivial Q split i j μ hB n hn ν T hC
    hc hm hij hsize with he | hz
  · exact he
  · have htwo : Nat.card (BinaryGaloisField n) = 2 := by
      have hlo : 1 < Nat.card (BinaryGaloisField n) := Finite.one_lt_card
      omega
    exact (source_binary_not_both_commutators_trivial Q split i j μ hB n ν T hC
      hc hm hij htwo hz.1 hz.2).elim

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
