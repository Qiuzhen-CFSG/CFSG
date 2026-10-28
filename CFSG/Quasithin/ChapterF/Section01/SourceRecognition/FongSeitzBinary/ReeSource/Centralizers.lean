module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourEquality

/-!
# Exact centralizers in the source Suzuki radical

The three commuting-with-U₂ factors B, Omega(C), E have unique ordered
coordinates and total order q⁴. The proved (6.1) bound therefore identifies
C_V(U₂) with B Omega(C) E, where V=U_s₂. Reflecting this product and using
uniqueness of the seven radical coordinates gives C_V(R₂)=E for the actual
root-generated Suzuki actor. The existing short commutator laws also put
Omega(E) in the centers of both U and V, including Sz(2). Cartan
invariance and the nonzero (6.4) commutator identify Z(V) intersect E
and the full actor fixed subgroup of Z(V) with Omega(E).

These are source calculations on the same marked quotient, retaining the
natural panel markings and odd linear degree. They do not assume the exact
five-factor derived product or the reverse center inclusions. The original
and Section 10 applications retain the literal quotient and N-conjugates.

Source: Fong--Seitz I (1973), proof of (6H)(c),(g), printed p.55;
II (1974), the center clauses of (10.3), printed p.221.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)

private theorem five_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split true 5 =
      [simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)] := by
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,List.map_cons,List.map_nil]
  change [simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1),
    rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D),
    rightConjugate (rightConjugate (rootAt Q split 0 (Q.simple 1))
      (representative (Q.simple 0) : X ⧸ Q.D)) (representative (Q.simple 1) : X ⧸ Q.D),
    rightConjugate (rightConjugate (rightConjugate (rootAt Q split 1 (Q.simple 0))
      (representative (Q.simple 1) : X ⧸ Q.D)) (representative (Q.simple 0) : X ⧸ Q.D))
      (representative (Q.simple 1) : X ⧸ Q.D)] = _
  rw [right_rep,right_rep,right_rep,right_rep,right_rep]
  have he : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0*Q.simple 1) =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
    rw [←right_rep]
    exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
  rw [he]

include μ hB in
private theorem omega_card (w : Weyl Q) :
    Nat.card (omegaOneAmbient (rootAt Q split 1 w)) = 2^(2*m+1) := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]
  exact suzukiOmega_card Q split 1 m μ hB

private theorem three_injective (hm : rotationOrder Q = 8) :
    Function.Injective (fun p : rootAt Q split 0 (Q.simple 1) ×
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) ×
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =>
      (p.1 : X ⧸ Q.D)*p.2.1*p.2.2) := by
  have hinj : Function.Injective (rootProduct (orderedRoots Q split true 5)) := by
    intro p q he
    apply (orderedCoordinates Q split true 5 (by omega)).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  rw [five_list Q split hm] at hinj
  intro p q he
  have hh := hinj
    (a₁ := (1,p.1,inclusion (omegaOneAmbient_le _) p.2.1,1,p.2.2,PUnit.unit))
    (a₂ := (1,q.1,inclusion (omegaOneAmbient_le _) q.2.1,1,q.2.2,PUnit.unit))
    (by simpa only [rootProduct,coe_one,coe_inclusion,one_mul,mul_one,mul_assoc] using he)
  refine Prod.ext (congrArg (fun z => z.2.1) hh) (Prod.ext ?_ ?_)
  · apply Subtype.ext
    exact congrArg (fun z => (z.2.2.1 : X ⧸ Q.D)) hh
  · exact congrArg (fun z => z.2.2.2.2.1) hh

include ν hC μ hB hn in
/-- The exact three-factor centralizer in the Suzuki radical, including Sz(2). -/
theorem source_suzuki_radical_centralizer
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    ((simpleRemainder Q split 1 ⊓ centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) ∧
    Nat.card (simpleRemainder Q split 1 ⊓ centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) = (2^(2*m+1))^4 := by
  let Z := simpleRemainder Q split 1 ⊓ centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D))
  let B := rootAt Q split 0 (Q.simple 1)
  let C := omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1))
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hv := octagon_three_roots_le_remainder Q split hm 1 0 (by decide)
  have hBz : B ≤ Z := le_inf hv.1 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
      (marked_linear_remainder_le_kernel Q split 0 ν T hC))))
  have hCz : C ≤ Z := le_inf ((omegaOneAmbient_le _).trans hv.2.1)
    (commutator_eq_bot_iff_le_centralizer.mp (source_shifted_omega_commute Q split 1 0 m μ hB ν T hC hm (by decide)))
  have hEz : E ≤ Z := le_inf hv.2.2 (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)))
  let f : B × C × E → Z := fun p =>
    ⟨(p.1 : X ⧸ Q.D)*p.2.1*p.2.2,
      Z.mul_mem (Z.mul_mem (hBz p.1.property) (hCz p.2.1.property)) (hEz p.2.2.property)⟩
  have hinj : Function.Injective f := fun p q h => three_injective Q split hm (congrArg Subtype.val h)
  have hcard : Nat.card (BinaryGaloisField n) = 2^(2*m+1) := by
    rw [GaloisField.card 2 n hn.pos.ne',ree_common_field_exponent Q split hm n hn m ν T hC μ hB
      (UnitarySource.actorReflection Q split) hcore]
  have hBcard : Nat.card B = 2^(2*m+1) := by
    rw [linear_rootAt_card Q split 0 n ν T hC hn.pos,
      ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
  have hCcard : Nat.card C = 2^(2*m+1) := omega_card Q split m μ hB _
  have hEcard : Nat.card E = (2^(2*m+1))^2 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = _
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1) (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]
  have hdom : Nat.card (B × C × E) = (2^(2*m+1))^4 := by
    rw [Nat.card_prod,Nat.card_prod,hBcard,hCcard,hEcard]
    ring
  have hhi := (source_six_one Q split 1 0 ν T hC m μ hB hc hm (by decide) hcard.le).1
  rw [hcard] at hhi
  have hf : Function.Bijective f := hinj.bijective_of_nat_card_le (hhi.trans_eq hdom.symm)
  refine ⟨?_,(Nat.card_congr (Equiv.ofBijective f hf)).symm.trans hdom⟩
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨p,hp⟩ := hf.2 ⟨z,hz⟩
    exact ⟨_,⟨_,p.1.property,_,p.2.1.property,rfl⟩,_,p.2.2.property,congrArg Subtype.val hp⟩
  · rintro z ⟨_,⟨b,hb,c,hc,rfl⟩,e,he,rfl⟩
    exact Z.mul_mem (Z.mul_mem (hBz hb) (hCz hc)) (hEz he)

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem sinv (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (ssq Q k)
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) = rootAt Q split k w := rfl

private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _


private theorem radical_seven (hm : rotationOrder Q = 8) :
    rootIntersection split (longest Q) (alternatingWord Q false 7)⁻¹ =
      simpleRemainder Q split 1 := by
  have hw : longest Q = Q.simple 1*alternatingWord Q false 7 := by
    have hh := (alternatingWord_longest Q true).symm
    rw [hm] at hh
    exact hh
  change split.U ⊓ unipotentConjugate split (longest Q*(alternatingWord Q false 7)⁻¹) = _
  rw [hw,mul_inv_cancel_right]
  rfl

private theorem radical_list (hm : rotationOrder Q = 8) :
    orderedRoots Q split false 7 =
      [simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0),
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
        rootAt Q split 1 (Q.simple 0*Q.simple 1),rootAt Q split 0 (Q.simple 1)] := by
  have h0 := perpendicular_root_stable Q split hm 0 1 (by decide)
    (representative (Q.simple 0)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm 1 0 (by decide)
    (representative (Q.simple 1)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) h1
  have h6 := congrArg (fun A => rightConjugate A (representative (Q.simple 1*Q.simple 0) : X ⧸ Q.D)) h0
  simp only [right_rep,mul_assoc,ssq,mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  simp only [orderedRoots,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,
    List.map_cons,List.map_nil,right_simple,right_rep]
  rw [h0,h5,h6]
  simp only [mul_assoc,ssq,mul_one]


include ν hC μ hB hn in
/-- The perpendicular Omega centralizes the whole source unipotent group. -/
theorem source_perpendicular_omega_centralizes_unipotent
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
      centralizer (split.U : Set (X ⧸ Q.D)) := by
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let Z := omegaOneAmbient E
  have hA : ⁅Z,simpleRoot Q split 1⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    exact (commutator_mono (omegaOneAmbient_le _) le_rfl).trans
      ((commutator_comm _ _).trans (source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)).le
  have hBZ : ⁅Z,rootAt Q split 0 (Q.simple 1)⁆ = ⊥ := by
    let w := Q.simple 0*Q.simple 1*Q.simple 0
    have hh := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D))
      (source_six_four_support_of_odd_degree Q split hc hm n hn m ν T hC μ hB hcore).2
    rw [right_comm,right_bot,right_omega,right_simple,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.2] at hh
    exact hh
  have hCZ : ⁅Z,rootAt Q split 1 (Q.simple 0*Q.simple 1)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D))
      (source_shifted_omega_commute Q split 1 0 m μ hB ν T hC hm (by decide))
    rw [right_comm,right_bot,right_omega,right_simple,right_rep] at hh
    have he : rootAt Q split 1 ((Q.simple 0*Q.simple 1)*(Q.simple 0*Q.simple 1)) = E := by
      rw [←mul_assoc,←right_rep]
      exact perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)
    rw [he] at hh
    exact hh
  have hD : ⁅Z,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm 1 0 (by decide)
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (marked_linear_remainder_le_kernel Q split 0 ν T hC))
    rw [right_comm,right_bot,right_simple,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).1] at hh
    exact eq_bot_iff.mpr ((commutator_mono (omegaOneAmbient_le _) le_rfl).trans hh.le)
  have hE : ⁅Z,E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (commutator_eq_bot_iff_le_centralizer.mpr (suzukiOmega_centralizes Q split 1 m μ hB))
    simpa only [right_comm,right_bot,right_omega,right_simple] using hh
  have hZ : rightConjugate Z (representative (Q.simple 1) : X ⧸ Q.D) = Z := by
    rw [right_omega,perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)]
  have hF : ⁅Z,rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hD
    simpa only [right_comm,right_bot,hZ,right_rep,mul_assoc,ssq,mul_one] using hh
  have hG : ⁅Z,rootAt Q split 1 (Q.simple 0)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hCZ
    simpa only [right_comm,right_bot,hZ,right_rep,mul_assoc,ssq,mul_one] using hh
  have hH : ⁅Z,simpleRoot Q split 0⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) hBZ
    simpa only [right_comm,right_bot,hZ,right_rep,ssq,rootAt_one] using hh
  have hV : simpleRemainder Q split 1 ≤ centralizer (Z : Set (X ⧸ Q.D)) := by
    intro v hv
    obtain ⟨p,hp⟩ := (orderedCoordinates Q split false 7 (by omega)).surjective
      ⟨v,by rw [radical_seven Q split hm]; exact hv⟩
    have he : rootProduct (orderedRoots Q split false 7) p = v :=
      (orderedCoordinates_apply Q split false 7 (by omega) p).symm.trans (congrArg Subtype.val hp)
    rw [←he]
    apply rootProduct_mem
    intro R hR
    rw [radical_list Q split hm] at hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply le_centralizer_iff.mp; apply commutator_eq_bot_iff_le_centralizer.mp
    · exact hH
    · exact hG
    · exact hF
    · exact hE
    · exact hD
    · exact hCZ
    · exact hBZ
  apply le_centralizer_iff.mpr
  intro u hu
  change u ∈ (split.U : Set (X ⧸ Q.D)) at hu
  rw [←simpleRoot_mul_remainder Q split 1] at hu
  obtain ⟨a,ha,v,hv,rfl⟩ := hu
  exact mul_mem ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hA)) ha) (hV hv)


include ν hC μ hB hn in
/-- The perpendicular Omega lies in both actual centers, before the reverse center bounds. -/
theorem source_perpendicular_omega_le_centers
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
        (center split.U).map split.U.subtype ∧
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
        (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype := by
  have hZ := source_perpendicular_omega_centralizes_unipotent Q split n hn m ν T hC μ hB hm hcore hc
  have hV := (omegaOneAmbient_le (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))).trans
    (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
  have hmap (V : Subgroup (X ⧸ Q.D)) (hVU : V ≤ split.U)
      (hZV : omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤ V) :
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤ (center V).map V.subtype := by
    intro z hz
    refine ⟨⟨z,hZV hz⟩,?_,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hZ hz) v (hVU v.property)
  exact ⟨hmap split.U le_rfl (hV.trans inf_le_left),hmap _ inf_le_left hV⟩

include ν hC μ hB hn in
/-- The full source Suzuki actor fixes precisely the perpendicular root in its radical. -/
theorem source_suzuki_actor_radical_centralizer
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    simpleRemainder Q split 1 ⊓ centralizer (rankOne Q split 1 : Set (X ⧸ Q.D)) =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
  let V := simpleRemainder Q split 1
  let A := simpleRoot Q split 1
  let B := rootAt Q split 0 (Q.simple 1)
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let G := rootAt Q split 1 (Q.simple 0)
  let H := simpleRoot Q split 0
  have hprod := (source_suzuki_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).1
  have hAE := source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc
  apply le_antisymm
  · intro z hz
    have hzA : z ∈ V ⊓ centralizer (A : Set (X ⧸ Q.D)) :=
      ⟨hz.1,centralizer_le (show A ≤ rankOne Q split 1 from le_sup_left) hz.2⟩
    have hpz : z ∈ (B : Set (X ⧸ Q.D)) * (omegaOneAmbient C : Set (X ⧸ Q.D)) * (E : Set (X ⧸ Q.D)) := by
      rw [←hprod]; exact hzA
    have hpzi : z⁻¹ ∈ (B : Set (X ⧸ Q.D)) * (omegaOneAmbient C : Set (X ⧸ Q.D)) * (E : Set (X ⧸ Q.D)) := by
      rw [←hprod]; exact inv_mem hzA
    obtain ⟨_,⟨b,hb,c,hc',rfl⟩,e,he,hzprod⟩ := hpz
    obtain ⟨_,⟨b',hb',c',hc'',rfl⟩,e',he',hzprod'⟩ := hpzi
    change b*c*e = z at hzprod
    change b'*c'*e' = z⁻¹ at hzprod'
    let r := involutoryRootReflection Q split 1 (UnitarySource.actorReflection Q split 1)
    let f := (MulAut.conj (r.val : X ⧸ Q.D)).symm
    have hf (R : Subgroup (X ⧸ Q.D)) : R.map f.toMonoidHom = rightConjugate R (r.val : X ⧸ Q.D) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
    have hrB : B.map f.toMonoidHom = H := by
      rw [hf,rootAt_right Q split 0 (Q.simple 1) (Q.simple 1) r.val r.class_eq,ssq,rootAt_one]
    have hrC : (omegaOneAmbient C).map f.toMonoidHom = omegaOneAmbient G := by
      rw [map_omegaOneAmbient_injective f.toMonoidHom f.injective,hf,
        rootAt_right Q split 1 (Q.simple 0*Q.simple 1) (Q.simple 1) r.val r.class_eq,mul_assoc,ssq,mul_one]
    have hrE : E.map f.toMonoidHom = E := by
      rw [hf,perpendicular_root_stable Q split hm 1 0 (by decide) r.val r.class_eq]
    have hfb : f b ∈ H := hrB ▸ mem_map_of_mem f.toMonoidHom hb
    have hfc : f c ∈ G := omegaOneAmbient_le G (hrC ▸ mem_map_of_mem f.toMonoidHom hc')
    have hfe : f e ∈ E := hrE ▸ mem_map_of_mem f.toMonoidHom he
    have hfix : f z = z := by
      have hr := mem_centralizer_iff.mp hz.2 (r.val : X ⧸ Q.D) r.mem_rankOne
      change (r.val : X ⧸ Q.D)⁻¹*z*r.val = z
      rw [mul_assoc,←hr,inv_mul_cancel_left]
    have hleft : f b * f c * f e = z := by rw [←map_mul,←map_mul,hzprod,hfix]
    have hright : e'⁻¹*c'⁻¹*b'⁻¹ = z := by simpa only [mul_inv_rev,inv_inv,mul_assoc] using congrArg Inv.inv hzprod'
    have hinj : Function.Injective (rootProduct (orderedRoots Q split false 7)) := by
      intro p q heq
      apply (orderedCoordinates Q split false 7 (by omega)).injective
      apply Subtype.ext
      simpa only [orderedCoordinates_apply] using heq
    rw [radical_list Q split hm] at hinj
    have htuple := hinj
      (a₁ := (⟨f b,hfb⟩,⟨f c,hfc⟩,1,⟨f e,hfe⟩,1,1,1,PUnit.unit))
      (a₂ := (1,1,1,⟨e'⁻¹,inv_mem he'⟩,1,⟨c'⁻¹,inv_mem (omegaOneAmbient_le C hc'')⟩,⟨b'⁻¹,inv_mem hb'⟩,PUnit.unit))
      (by simpa only [rootProduct,coe_one,one_mul,mul_one,mul_assoc] using hleft.trans hright.symm)
    have hb1 : f b = 1 := congrArg (fun p => (p.1 : X ⧸ Q.D)) htuple
    have hc1 : f c = 1 := congrArg (fun p => (p.2.1 : X ⧸ Q.D)) htuple
    rw [hb1,hc1,one_mul,one_mul] at hleft
    exact hleft ▸ hfe
  · have hEV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
    refine le_inf hEV ?_
    apply le_centralizer_iff.mpr
    change A ⊔ rootAt Q split 1 (Q.simple 1) ≤ centralizer (E : Set (X ⧸ Q.D))
    refine sup_le (commutator_eq_bot_iff_le_centralizer.mp hAE) ?_
    have hh := congrArg (fun R => rightConjugate R (representative (Q.simple 1) : X ⧸ Q.D)) hAE
    rw [right_comm,right_bot,right_simple,
      perpendicular_root_stable Q split hm 1 0 (by decide) _ (representative_spec _)] at hh
    exact commutator_eq_bot_iff_le_centralizer.mp hh


include ν hC μ hB hn in
/-- The radical center intersects the perpendicular root in exactly Omega, even for Sz(2). -/
theorem source_perpendicular_inf_radical_center
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ⊓
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let V := simpleRemainder Q split 1
  let Z := (center V).map V.subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  have hCZ : Z ≤ centralizer (V : Set (X ⧸ Q.D)) := by
    rintro z ⟨x,hx,rfl⟩
    exact mem_centralizer_iff.mpr (fun v hv => congrArg Subtype.val
      (mem_center_iff.mp hx ⟨v,hv⟩))
  have hNZ : Q.tits.B ⊓ Q.tits.N ≤ normalizer (Z : Set (X ⧸ Q.D)) := by
    apply (show Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set (X ⧸ Q.D)) from
      fun h hh => remainder_parabolic_normalizes Q split 1
        (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
        (Q.tits.B_le_standardParabolic _ hh.1)).trans
    exact normalizer_le_normalizer_characteristic_image V (center V)
  have hnot : ¬ E ≤ Z := by
    intro hEZ
    have hEB : ⁅E,rootAt Q split 0 (Q.simple 1)⁆ =
        omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
      let w := Q.simple 0*Q.simple 1*Q.simple 0
      have hh := congrArg (fun A => rightConjugate A (representative w : X ⧸ Q.D))
        (source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc)
      rw [right_comm,right_simple,right_omega,
        (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.2,
        (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.1] at hh
      exact hh
    have hbV := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1
    have hz : ⁅E,rootAt Q split 0 (Q.simple 1)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hEZ.trans (hCZ.trans (centralizer_le hbV)))
    rw [hEB] at hz
    have hcard := omega_card Q split m μ hB (Q.simple 0*Q.simple 1)
    rw [hz,Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow (by omega : 2*m+1 ≠ 0) (by decide : 1 < 2)).ne hcard
  apply le_antisymm
  · exact suzuki_rootAt_intersection_le_omega_of_not_le Q split 1 m μ hB _ Z hNZ hnot
  · exact le_inf (source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm hcore hc).2
      (omegaOneAmbient_le _)

include ν hC μ hB hn in
/-- The full Suzuki actor fixes exactly the perpendicular Omega in the radical center. -/
theorem source_suzuki_fixed_radical_center
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ⊓
        centralizer (rankOne Q split 1 : Set (X ⧸ Q.D)) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hZV : (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype ≤
      simpleRemainder Q split 1 := map_subtype_le _
  have hCR := source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc
  have hZ := source_perpendicular_inf_radical_center Q split n hn m ν T hC μ hB hm hcore hc
  apply le_antisymm
  · intro z hz
    apply hZ.le
    exact ⟨hz.1,hCR.le ⟨hZV hz.1,hz.2⟩⟩
  · intro z hz
    have he := hZ.ge hz
    exact ⟨he.1,(hCR.ge he.2).2⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
