module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FourRootIntervals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ProductSupport

/-!
# The two-factor bound and Omega centralization before source (6.4)

The four-root interval places [U₂,U₁^(s₂s₁s₂)] in the product
U₁^s₂ U₂^(s₁s₂). Conjugation by s₁s₂s₁ places the entire commutator in
the derived radical and transforms that support to the two-root product
handled by ProductSupport. Consequently every commutator-subgroup element
has square one, and its Suzuki component lies in Omega. The square
commutator identity now gives [Omega₁(U₂),U₁^(s₂s₁s₂)]=1.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the paragraph
ending in (6.4). This proves its second assertion and the preceding bound
by Omega₁(U₂^(s₁s₂)) U₁^s₂. Removing the linear factor in its first
assertion remains a subsequent step; the mixed equality is not claimed.
Independent field orders are retained until the explicit odd-degree
specialization applies the established common-field theorem. All Suzuki
parameters, including zero, are covered. OriginalSixFourSupport applies
these results to the original endpoints and their literal quotient maps.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include ν hC in
private theorem linear_rootAt_square (w : Weyl Q)
    (x : X ⧸ Q.D) (hx : x ∈ rootAt Q split j w) : x^2 = 1 := by
  let e : rootAt Q split j w ≃* Multiplicative F :=
    (RootAction.conjugateEquiv (simpleRoot Q split j) (representative w)).trans
      (linearRootEquiv Q split j ν T hC)
  have hs : (⟨x,hx⟩ : rootAt Q split j w)^2 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (e ⟨x,hx⟩).toAdd = 0
    rw [two_nsmul,CharTwo.add_self_eq_zero]
  exact congrArg Subtype.val hs

include μ hB ν hC in
private theorem middle_pair_commute (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  let n := representative (Q.simple i)
  have hc := adjacent_commutator_eq_bot Q split hm j i hij.symm
    (marked_linear_remainder_le_kernel Q split j ν T hC)
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
  have ht := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (n : X ⧸ Q.D)) hc
  have hconj (A B : Subgroup (X ⧸ Q.D)) :
      rightConjugate ⁅A,B⁆ (n : X ⧸ Q.D) =
        ⁅rightConjugate A (n : X ⧸ Q.D),rightConjugate B (n : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  have hbot : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
  rw [hconj,hbot] at ht
  change ⁅rootAt Q split j (Q.simple i),rightConjugate (rootAt Q split i (Q.simple j)) (n : X ⧸ Q.D)⁆ = ⊥ at ht
  rwa [rootAt_right Q split i (Q.simple j) (Q.simple i) n (representative_spec _)] at ht

include μ hB ν hC in
/-- Every element of the mixed commutator has order at most two, and its
Suzuki factor lies in Omega. This uses the actual reflected derived radical. -/
theorem source_six_four_product
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6)
    (z : X ⧸ Q.D)
    (hz : z ∈ ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆) :
    z^2 = 1 ∧ z ∈
      (omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
  let n := representative (Q.simple j*Q.simple i*Q.simple j)
  let e := (MulAut.conj (n : X ⧸ Q.D)).symm
  have he (A : Subgroup (X ⧸ Q.D)) : A.map e.toMonoidHom = rightConjugate A (n : X ⧸ Q.D) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm']; rfl
  have ht := four_interval_reflection Q split hm i j hij n (representative_spec _)
  have hp := distance_three_commutator_support Q split hm i j hij
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)
    (marked_linear_remainder_le_kernel Q split j ν T hC) z hz
  have hdz : e z ∈ ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
    apply four_interval_reflected_derived Q split hm i j hij n (representative_spec _)
    rw [←he]
    exact ⟨z,hz,rfl⟩
  obtain ⟨b,hb,a,ha,rfl⟩ := hp
  have hea : e a ∈ rootAt Q split i (Q.simple j*Q.simple i) := by
    rw [←ht.2.1,←he]
    exact ⟨a,ha,rfl⟩
  have heb : e b ∈ rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
    rw [←ht.1,←he]
    exact ⟨b,hb,rfl⟩
  have hab : Commute (e a) (e b) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_shifted_pair_commute Q split i j m μ hB ν T hC hm hij) hea) _ heb).symm
  have hprod : e (b*a) ∈ (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) :=
    ⟨e a,hea,e b,heb,hab.eq.trans (map_mul e b a).symm⟩
  have hs := (source_derived_product_support Q split i j m μ hB ν T hC hc hm hij hsize
    (e (b*a)) hdz hprod).1
  have hz2 : (b*a)^2 = 1 := e.injective (by simpa only [map_pow,map_one] using hs)
  have hba : Commute b a :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (middle_pair_commute Q split i j m μ hB ν T hC hm hij) hb) _ ha).symm
  have hb2 := linear_rootAt_square Q split j ν T hC (Q.simple i) b hb
  refine ⟨hz2,a,?_,b,hb,hba.eq.symm⟩
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl a ha
  simpa only [hba.mul_pow,hb2,one_mul] using hz2

include μ hB in
private theorem shifted_omega_square (w : Weyl Q) (x : X ⧸ Q.D)
    (hx : x ∈ omegaOneAmbient (rootAt Q split i w)) :
    ∃ y ∈ rootAt Q split i w, y^2 = x := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split i).map e.toMonoidHom = rootAt Q split i w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hΩ : (omegaOneAmbient (simpleRoot Q split i)).map e.toMonoidHom =
      omegaOneAmbient (rootAt Q split i w) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  rw [←hΩ] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB a).mp ha
  refine ⟨e b,?_,(map_pow e b 2).symm⟩
  rw [←he]
  exact ⟨b,hb,rfl⟩

include μ hB ν hC in
/-- The Omega of the second Suzuki root also centralizes the first root. -/
theorem source_shifted_omega_commute (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ⁅omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)),simpleRoot Q split i⁆ = ⊥ := by
  apply eq_bot_iff.mpr
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := shifted_omega_square Q split i m μ hB _ x hx
  have hb : ⁅a,y⁆ ∈ rootAt Q split j (Q.simple i) := by
    apply (source_six_three Q split i j m μ hB ν T hC hm hij).1
    rw [commutator_comm]
    exact commutator_mem_commutator ha hy
  have hc : Commute a ⁅a,y⁆ :=
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (middle_pair_commute Q split i j m μ hB ν T hC hm hij) hb) _ ha
  have hs := linear_rootAt_square Q split j ν T hC (Q.simple i) ⁅a,y⁆ hb
  rw [mem_bot,pow_two,commutatorElement_mul_left_eq_conj_mul,hc.eq,
    mul_inv_cancel_right,←pow_two,hs]

include μ hB ν hC in
/-- The second assertion of (6.4), including the binary Suzuki endpoint. -/
theorem source_six_four_omega_commute
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card F)^4 < (2^(2*m+1))^6) :
    ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ := by
  apply eq_bot_iff.mpr
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB x).mp hx
  obtain ⟨hs,hp⟩ := source_six_four_product Q split i j m μ hB ν T hC hc hm hij hsize
    ⁅a,y⁆ (commutator_mem_commutator ha hy)
  have hcomm : Commute a ⁅a,y⁆ := by
    obtain ⟨c,hc',b,hb,he⟩ := hp
    rw [←he]
    apply Commute.mul_right
    · exact mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (source_shifted_omega_commute Q split i j m μ hB ν T hC hm hij) hc') _ ha
    · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (adjacent_commutator_eq_bot Q split hm i j hij
          (marked_suzuki_remainder_le_kernel Q split i m μ hB)
          (marked_linear_remainder_le_kernel Q split j ν T hC)) ha) _ hb).symm
  rw [mem_bot,pow_two,commutatorElement_mul_left_eq_conj_mul,hcomm.eq,
    mul_inv_cancel_right,←pow_two,hs]


omit i j m μ hB ν T hC in
/-- The preceding common-field theorem supplies the size obstruction.
Its odd-linear-degree premise remains explicit. This proves the Omega
centralization in (6.4) and the two-factor support used before its first assertion. -/
theorem source_six_four_support_of_odd_degree
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    (∀ z ∈ ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆,
      z^2 = 1 ∧ z ∈
        (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D))) ∧
    ⁅omegaOneAmbient (simpleRoot Q split 1),
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6 := by
    rw [show Nat.card (BinaryGaloisField n) = 2^n from GaloisField.card 2 n hn.pos.ne',he]
    exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide : 4 < 6)
  exact ⟨source_six_four_product Q split 1 0 m μ hB ν T hC hc hm (by decide) hsize,
    source_six_four_omega_commute Q split 1 0 m μ hB ν T hC hc hm (by decide) hsize⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
