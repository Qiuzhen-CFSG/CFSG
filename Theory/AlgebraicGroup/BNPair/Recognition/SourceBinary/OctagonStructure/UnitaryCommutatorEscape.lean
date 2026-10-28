module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineSubgroup
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryPropagation
public import Theory.GroupTheory.EmbeddedCenterMap
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineSubgroup

/-!
# Escape and the next commutator in the unitary octagon

The two shifted radical kernels detect the end coordinates of the middle
five-root subgroup. If the unitary reflection fixes every commutator with
the radical, those end coordinates are central. They therefore lie in the
literal nine-b subgroup X. The contrapositive proves nontrivial action on
the next lower-central term from escape from X.

For degree one, the reflection cannot agree with any full-Borel actor on
that commutator. The odd panel index then excludes a two-group action
image; the SU3(2) three-core bound gives six binary dimensions. For larger
degree the general special-unitary bound applies. This proves the six-b
Frattini bound in every degree, preserving the actual quotient maps,
full Borel and both endpoint orientations.

Source: Fong--Seitz I (6F), printed p.47, last full paragraph, using its
(3G) root geometry and (5D) effectiveness step. Persistence of the stronger
projective eight-b section remains a subsequent source argument. Original
factor and Chapter 12 applications are in the matching CFSG modules.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

private theorem central_coordinate_of_commutators {Y : Type*} [Group Y]
    (A N : Subgroup Y) (hn : A ≤ normalizer (N : Set Y)) (hd : Disjoint A N)
    (x : Y) (hx : x ∈ A ⊔ N) (hc : ∀ a ∈ A, ⁅x,a⁆ ∈ N) :
    x ∈ (center A).map A.subtype ⊔ N := by
  have hp : x ∈ (A : Set Y)*(N : Set Y) := by
    rw [←coe_mul_of_left_le_normalizer_right A N hn]
    exact hx
  obtain ⟨a,ha,n,hN,rfl⟩ := hp
  have hz : (⟨a,ha⟩ : A) ∈ center A := by
    rw [mem_center_iff]
    intro y
    have hny : ⁅n,(y : Y)⁆ ∈ N :=
      le_normalizer_iff_commutator_le_left.mp hn (commutator_mem_commutator hN y.property)
    have hconj : a*⁅n,(y : Y)⁆*a⁻¹ ∈ N := (mem_normalizer_iff.mp (hn ha) _).mp hny
    have hxy := hc y y.property
    rw [commutatorElement_mul_left_eq_conj_mul] at hxy
    have hay : ⁅a,(y : Y)⁆ ∈ N := (N.mul_mem_cancel_left hconj).mp hxy
    have he := disjoint_def.mp hd
      (commutator_le_self A (commutator_mem_commutator ha y.property)) hay
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  exact mul_mem_sup (mem_map_of_mem A.subtype hz) hN

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem shifted_remainder_right (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (v w : Weyl Q) (n : Q.tits.N) (hn : QuotientGroup.mk' _ n=w) :
    rightConjugate (rightConjugate (simpleRemainder Q split j)
      (representative v : X ⧸ Q.D)) (n : X ⧸ Q.D) =
      rightConjugate (simpleRemainder Q split j) (representative (v*w) : X ⧸ Q.D) := by
  rw [←rightConjugate_mul]
  exact rightConjugate_eq_of_quotient_eq _
    (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split j hKj)))
    (representative v*n) (representative (v*w))
    (by rw [map_mul,representative_spec,hn,representative_spec])

private theorem shifted_join_normalizes (j : Fin 2) (w : Weyl Q)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    rootAt Q split j w ⊔ rightConjugate (simpleRemainder Q split j)
      (representative w : X ⧸ Q.D) ≤
    normalizer (rightConjugate (simpleRemainder Q split j)
      (representative w : X ⧸ Q.D) : Set (X ⧸ Q.D)) :=
  sup_le (shifted_root_normalizes Q split j w hKj) (rightConjugate (simpleRemainder Q split j)
    (representative w : X ⧸ Q.D)).le_normalizer

/-- If the unitary reflection fixes the next radical commutator, both
end coordinates of W are central in their literal unitary roots. -/
theorem middleFive_commutator_fixed_centers (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hfix : ∀ z ∈ ⁅W,simpleRemainder Q split j⁆,
      (s.val : X ⧸ Q.D)⁻¹*z*s.val=z) :
    W ≤ ((center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype ⊔
      rightConjugate (simpleRemainder Q split j) (representative (Q.simple i) : X ⧸ Q.D)) ⊓
      ((center (rootAt Q split j (Q.simple i*Q.simple j))).map
        (rootAt Q split j (Q.simple i*Q.simple j)).subtype ⊔
      rightConjugate (simpleRemainder Q split j)
        (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)) := by
  let A := rootAt Q split j (Q.simple i)
  let E := rootAt Q split j (Q.simple i*Q.simple j)
  let N₁ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i) : X ⧸ Q.D)
  let N₂ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)
  let M := middleFive Q split j i
  have hAV : A ≤ simpleRemainder Q split j :=
    (show A ≤ M from le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))).trans
      (middleFive_le_remainder Q split hm j i hij.symm)
  have hEV : E ≤ simpleRemainder Q split j :=
    (show E ≤ M from le_sup_right).trans (middleFive_le_remainder Q split hm j i hij.symm)
  obtain ⟨hB₁,hC₁,hD₁,hE₁,hA₂,hB₂,hC₂,hD₂⟩ := eight_containments Q split hm i j hij
  have hM₁ : M ≤ A ⊔ N₁ :=
    sup_le (sup_le (sup_le (sup_le le_sup_left (hB₁.trans le_sup_right))
      (hC₁.trans le_sup_right)) (hD₁.trans le_sup_right)) (hE₁.trans le_sup_right)
  have hM₂ : M ≤ E ⊔ N₂ :=
    sup_le (sup_le (sup_le (sup_le (hA₂.trans le_sup_right) (hB₂.trans le_sup_right))
      (hC₂.trans le_sup_right)) (hD₂.trans le_sup_right)) le_sup_left
  have hMN₁ : M ≤ normalizer (N₁ : Set (X ⧸ Q.D)) :=
    hM₁.trans (shifted_join_normalizes Q split j _ hKj)
  have hMN₂ : M ≤ normalizer (N₂ : Set (X ⧸ Q.D)) :=
    hM₂.trans (shifted_join_normalizes Q split j _ hKj)
  have hN₁s : rightConjugate N₁ (s.val : X ⧸ Q.D)=N₂ :=
    shifted_remainder_right Q split j hKj _ _ s.val s.class_eq
  have hN₂s : rightConjugate N₂ (s.val : X ⧸ Q.D)=N₁ := by
    have he := shifted_remainder_right Q split j hKj (Q.simple i*Q.simple j)
      (Q.simple j) s.val s.class_eq
    simpa only [mul_assoc,ssq,mul_one] using he
  have carry (N N' : Subgroup (X ⧸ Q.D))
      (he : rightConjugate N (s.val : X ⧸ Q.D)=N')
      (z : X ⧸ Q.D) (hz : z ∈ ⁅W,simpleRemainder Q split j⁆) (hzN : z ∈ N) : z ∈ N' := by
    rw [←he,←hfix z hz]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*z*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ N
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hzN
  intro x hx
  constructor
  · apply central_coordinate_of_commutators A N₁
      (shifted_root_normalizes Q split j _ hKj) (shifted_root_disjoint Q split j _)
      x (hM₁ (hWM hx))
    intro a ha
    exact carry N₂ N₁ hN₂s _ (commutator_mem_commutator hx (hAV ha))
      (le_normalizer_iff_commutator_le_right.mp hMN₂
        (commutator_mem_commutator (hWM hx) (hA₂ ha)))
  · apply central_coordinate_of_commutators E N₂
      (shifted_root_normalizes Q split j _ hKj) (shifted_root_disjoint Q split j _)
      x (hM₂ (hWM hx))
    intro a ha
    exact carry N₁ N₂ hN₁s _ (commutator_mem_commutator hx (hEV ha))
      (le_normalizer_iff_commutator_le_right.mp hMN₁
        (commutator_mem_commutator (hWM hx) (hE₁ ha)))


/-- The literal nine-b subgroup contains every five-root candidate whose
next commutator is fixed by the unitary reflection. -/
theorem middleFive_commutator_fixed_le_nine
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (s : RootReflection Q split j)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hfix : ∀ z ∈ ⁅W,simpleRemainder Q split j⁆,
      (s.val : X ⧸ Q.D)⁻¹*z*s.val=z) : W ≤ unitaryNineSubgroup Q split i j := by
  have hc := middleFive_commutator_fixed_centers Q split hm i j hij hKj s W hWM hfix
  have he (w : Weyl Q) : (center (rootAt Q split j w)).map
      (rootAt Q split j w).subtype = rootFrattiniAt Q split j w := by
    rw [rootFrattiniAt,unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ]
  simp only [he] at hc
  rw [unitaryNineSubgroup_intersection Q split hm i j hij hKj]
  exact le_inf (le_inf hWM (hc.trans inf_le_left)) (hc.trans inf_le_right)

/-- Escape from X forces a nontrivial action on the next literal radical
commutator, for every positive degree and either unitary scalar convention. -/
theorem unitary_commutator_action_of_escape
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split i j) :
    (radicalCommutatorSection Q split j hKj W
      (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR).action ≠ 1 := by
  let d := radicalCommutatorSection Q split j hKj W
    (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR
  let s := UnitarySource.actorReflection Q split j
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  apply hescape
  apply middleFive_commutator_fixed_le_nine Q split J hb hcard hconj hm i j hij hKj μ s W hWM
  intro z hz
  let x : d.numerator := ⟨z,hz⟩
  have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x))
    (show d.action r⁻¹=1 from by rw [he]; rfl)
  rw [d.action_mk] at hh
  have hx : d.numeratorAction r⁻¹ x=x := congrArg QuotientGroup.quotientBot hh
  have hh := congrArg Subtype.val hx
  rw [d.numeratorAction_apply] at hh
  simpa only [r,coe_inv,inv_inv] using hh


private theorem right_embedded_center (A : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ((center A).map A.subtype) n =
      (center (rightConjugate A n)).map (rightConjugate A n).subtype := by
  have he : rightConjugate A n = A.map (MulAut.conj n).symm.toMonoidHom :=
    comap_equiv_eq_map_symm' (MulAut.conj n) A
  rw [he]
  change ((center A).map A.subtype).comap (MulAut.conj n).toMonoidHom = _
  rw [comap_equiv_eq_map_symm']
  exact map_embeddedCenter A (MulAut.conj n).symm.toMonoidHom (MulAut.conj n).symm.injective

/-- Even equality with a Borel actor forces the two end coordinates to
be central. This is the source geometry needed for the solvable degree-one actor. -/
theorem middleFive_commutator_borel_le_nine
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (s : RootReflection Q split j)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ Q.tits.B)
    (hfix : ∀ z ∈ ⁅W,simpleRemainder Q split j⁆,
      (s.val : X ⧸ Q.D)⁻¹*z*s.val=(u : X ⧸ Q.D)⁻¹*z*u) :
    W ≤ unitaryNineSubgroup Q split i j := by
  let A := rootAt Q split j (Q.simple i)
  let E := rootAt Q split j (Q.simple i*Q.simple j)
  let N₁ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i) : X ⧸ Q.D)
  let N₂ := rightConjugate (simpleRemainder Q split j) (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)
  let M := middleFive Q split j i
  obtain ⟨hB₁,hC₁,hD₁,hE₁,hA₂,hB₂,hC₂,hD₂⟩ := eight_containments Q split hm i j hij
  have hM₁ : M ≤ A ⊔ N₁ :=
    sup_le (sup_le (sup_le (sup_le le_sup_left (hB₁.trans le_sup_right))
      (hC₁.trans le_sup_right)) (hD₁.trans le_sup_right)) (hE₁.trans le_sup_right)
  have hM₂ : M ≤ E ⊔ N₂ :=
    sup_le (sup_le (sup_le (sup_le (hA₂.trans le_sup_right) (hB₂.trans le_sup_right))
      (hC₂.trans le_sup_right)) (hD₂.trans le_sup_right)) le_sup_left
  have hMN₁ : M ≤ normalizer (N₁ : Set (X ⧸ Q.D)) :=
    hM₁.trans (shifted_join_normalizes Q split j _ hKj)
  have hEV : E ≤ simpleRemainder Q split j :=
    (show E ≤ M from le_sup_right).trans (middleFive_le_remainder Q split hm j i hij.symm)
  have hrootN₁ : simpleRoot Q split j ≤ N₁ := by
    have hl := octagon_lengths Q i hm j hij
    have hl' := octagon_lengths Q j hm i hij.symm
    have hh := shifted_root_le Q split j j 1 (Q.simple i) (by
      simp only [inv_one,mul_one,hl.1,hl.2.1]) (by
      simp only [inv_one,mul_one,hl'.2.1,hl'.2.2.1])
    simpa only [rootAt_one] using hh
  have huN : (u : X ⧸ Q.D) ∈ normalizer (N₁ : Set (X ⧸ Q.D)) := by
    obtain ⟨a,ha,t,ht,he⟩ := UnitarySource.rootActor_borel_factorization Q split j u.property hu
    rw [he]
    exact mul_mem (N₁.le_normalizer (hrootN₁ ha))
      (torus_normalizes_rightConjugate _
        (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
          (remainder_parabolic_normalizes Q split j hKj))) _ ht.2)
  have hN₁s : rightConjugate N₁ (s.val : X ⧸ Q.D)=N₂ :=
    shifted_remainder_right Q split j hKj _ _ s.val s.class_eq
  have hN₂s : rightConjugate N₂ (s.val : X ⧸ Q.D)=N₁ := by
    have he := shifted_remainder_right Q split j hKj (Q.simple i*Q.simple j)
      (Q.simple j) s.val s.class_eq
    simpa only [mul_assoc,ssq,mul_one] using he
  have hWs : rightConjugate W (s.val : X ⧸ Q.D)=W :=
    rightConjugate_eq_self W (hWR s.mem_rankOne)
  have hEs : rightConjugate E (s.val : X ⧸ Q.D)=A := by
    have he := rootAt_right Q split j (Q.simple i*Q.simple j) (Q.simple j) s.val s.class_eq
    simpa only [mul_assoc,ssq,mul_one] using he
  have hright : W ≤ (center E).map E.subtype ⊔ N₂ := by
    intro x hx
    apply central_coordinate_of_commutators E N₂
      (shifted_root_normalizes Q split j _ hKj) (shifted_root_disjoint Q split j _)
      x (hM₂ (hWM hx))
    intro a ha
    let z := ⁅x,a⁆
    have hz : z ∈ ⁅W,simpleRemainder Q split j⁆ := commutator_mem_commutator hx (hEV ha)
    have hzN : z ∈ N₁ := le_normalizer_iff_commutator_le_right.mp hMN₁
      (commutator_mem_commutator (hWM hx) (hE₁ ha))
    have hc : (s.val : X ⧸ Q.D)⁻¹*z*s.val ∈ N₁ := by
      rw [hfix z hz]
      have huInv : (u : X ⧸ Q.D)⁻¹ ∈ normalizer (N₁ : Set (X ⧸ Q.D)) := inv_mem huN
      simpa only [inv_inv] using (mem_normalizer_iff.mp huInv z).mp hzN
    -- Use the inverse-conjugation membership directly and the second reflection identity.
    have hz' : (s.val : X ⧸ Q.D)⁻¹*z*s.val ∈ rightConjugate N₂ (s.val : X ⧸ Q.D) := by
      rwa [hN₂s]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*z*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ N₂ at hz'
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hz'
  have hleft := comap_mono (f := (MulAut.conj (s.val : X ⧸ Q.D)).toMonoidHom) hright
  change rightConjugate W (s.val : X ⧸ Q.D) ≤
    rightConjugate ((center E).map E.subtype ⊔ N₂) (s.val : X ⧸ Q.D) at hleft
  have hsup : rightConjugate ((center E).map E.subtype ⊔ N₂) (s.val : X ⧸ Q.D) =
      rightConjugate ((center E).map E.subtype) (s.val : X ⧸ Q.D) ⊔
        rightConjugate N₂ (s.val : X ⧸ Q.D) := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_sup]
  rw [hWs,hsup,right_embedded_center,hEs,hN₂s] at hleft
  have he (w : Weyl Q) : (center (rootAt Q split j w)).map
      (rootAt Q split j w).subtype = rootFrattiniAt Q split j w := by
    rw [rootFrattiniAt,unitary_rootAt_frattini_eq_center_all Q split J hb hcard hconj j hKj μ]
  dsimp only [A] at hleft
  dsimp only [E] at hright
  rw [he] at hleft hright
  rw [unitaryNineSubgroup_intersection Q split hm i j hij hKj]
  exact le_inf (le_inf hWM hleft) hright


/-- The small actor's commutator image is not a two-group. The proof uses
its odd panel degree and the full Borel, including its scalar factor. -/
theorem unitary_commutator_action_not_two
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split i j)
    (hpanel : Nat.card (Panel Q j)=9) :
    ¬ IsPGroup 2 (radicalCommutatorSection Q split j hKj W
      (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR).action.range := by
  let d := radicalCommutatorSection Q split j hKj W
    (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR
  let s := UnitarySource.actorReflection Q split j
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  let f := d.action.rangeRestrict
  let B := Q.tits.B.subgroupOf (rankOne Q split j)
  intro ht
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.action.rangeRestrict_surjective
    rwa [rankOne_borel_index Q split j,hpanel] at hh
  obtain ⟨n,hn⟩ := ht.exists_card_eq
  have hidx : (B.map f).index=1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  obtain ⟨u,hu,he⟩ := (show f r ∈ B.map f from index_eq_one.mp hidx ▸ mem_top _)
  have he' : d.action r=d.action u := (congrArg Subtype.val he).symm
  apply hescape
  apply middleFive_commutator_borel_le_nine Q split J hb hcard hconj hm i j hij hKj μ s
    W hWM hWR u hu
  intro z hz
  let x : d.numerator := ⟨z,hz⟩
  have hei : d.action r⁻¹=d.action u⁻¹ := by rw [map_inv,map_inv,he']
  have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) hei
  rw [d.action_mk,d.action_mk] at hh
  have hx : d.numeratorAction r⁻¹ x=d.numeratorAction u⁻¹ x := congrArg QuotientGroup.quotientBot hh
  have hh := congrArg Subtype.val hx
  rw [d.numeratorAction_apply,d.numeratorAction_apply] at hh
  simpa only [r,coe_inv,inv_inv] using hh

private theorem small_cover_section_bound
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hc : Nat.card F=4) (hconj : ∀ x,J.conj x=x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (j : Fin 2) (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (d : RootSection Q split j) (hnot : ¬ IsPGroup 2 d.action.range) :
    64 ≤ Nat.card d.EffectiveCarrier := by
  by_contra! hsmall
  let ρ := d.effectiveRepresentation.comp σ
  have hcV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive d.EffectiveCarrier)
  simp only [Nat.card_zmod] at hcV
  have hd : Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) < 6 := by
    have hh : 2^Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) < 2^6 := hcV ▸ hsmall
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
  have hkill := small_special_three_core_killed J hc hconj hJ ρ hd
  let α := d.action.comp σ
  let N := pCore 3 J.specialSubgroup
  have hk : N ≤ α.ker := by
    intro g hg
    apply d.action_eq_one_of_odd (σ g)
    · have hgorder : orderOf g ∣ 27 := by
        rw [←BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore.special_core_card J hc hconj]
        exact (Subgroup.orderOf_coe (⟨g,hg⟩ : N)) ▸ orderOf_dvd_natCard (⟨g,hg⟩ : N)
      exact ((by decide : Nat.Coprime 27 2).of_dvd_left hgorder).of_dvd_left (orderOf_map_dvd σ g)
    · ext v
      exact Additive.ofMul.injective (congrArg
        (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) => f (Additive.ofMul v)) (hkill hg))
  have hidx : N.index=8 := by
    have hh := N.card_mul_index
    rw [show Nat.card N=27 from BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore.special_core_card J hc hconj,
      BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore.special_group_card J hc hconj] at hh
    omega
  have hα : IsPGroup 2 α.range := IsPGroup.of_card_dvd_pow (p:=2) (n:=3) (by
    have hh := index_dvd_of_le hk
    rwa [hidx,index_ker] at hh)
  have he : α.range=d.action.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hσ,←MonoidHom.range_eq_map]
  exact hnot (he ▸ hα)

/-- The corresponding next lower-central term has at least six binary
 dimensions per field degree when the unitary actor is perfect. -/
private theorem unitary_commutator_frattini_bound_of_escape
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split i j) :
    2^(6*b) ≤ Nat.card ((⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ⧸
      frattini (⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D))) := by
  let d := radicalCommutatorSection Q split j hKj W
    (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR
  have hmove := unitary_commutator_action_of_escape Q split J (by omega) hcard hconj
    hm i j hij hKj μ W hWM hWR hescape
  have hc := unitary_section_card_bound Q split j J hb hcard hconj σ hσ d hmove
  have hd : d.effectiveDenominator=frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(6*b) ≤ d.effectiveDenominator.index at hc
  rw [hd] at hc
  exact hc


/-- The source six-b Frattini bound for the next commutator holds at every
positive degree, including SU3(2) and PSU3(2). -/
theorem unitary_commutator_frattini_bound_all
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split j i)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split i j) :
    2^(6*b) ≤ Nat.card ((⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ⧸
      frattini (⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D))) := by
  by_cases he : b=1
  · have hc : Nat.card F=4 := by simpa only [he,pow_one,Nat.reducePow] using hcard
    have hj : ∀ x,J.conj x=x^2 := by simpa only [he,pow_one] using hconj
    have hr : Nat.card (simpleRoot Q split j)=8 := by simpa only [he,pow_one,Nat.reducePow] using hroot
    have hp : Nat.card (Panel Q j)=9 := by
      have hh := singleton_parabolic_root_index Q split j
      change Nat.card (Panel Q j)=1+Nat.card (simpleRoot Q split j) at hh
      omega
    let d := radicalCommutatorSection Q split j hKj W
      (hWM.trans (middleFive_le_remainder Q split hm j i hij.symm)) hWR
    have hnot := unitary_commutator_action_not_two Q split J hb hcard hconj hm i j hij hKj μ W hWM hWR hescape hp
    have hf : Nat.card {x : F // J.conj x=x}=2 := by
      simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
        (by simpa using hc) (by simpa using hj)
    let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    obtain ⟨C,hC⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis
      J 2 (by simpa using hc) hf
    let es := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC
    have hbound := small_cover_section_bound Q split J₀ hc hj rfl j
      (σ.comp es.symm.toMonoidHom) (hσ.comp es.symm.surjective) d hnot
    have hd : d.effectiveDenominator=frattini d.numerator := by
      rw [d.effectiveDenominator_eq]
      exact sup_bot_eq _
    change 64 ≤ d.effectiveDenominator.index at hbound
    rw [hd] at hbound
    change 64 ≤ Nat.card ((⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ⧸
      frattini (⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D))) at hbound
    simpa only [he,mul_one,Nat.reducePow] using hbound
  · exact unitary_commutator_frattini_bound_of_escape Q split J (by omega) hcard hconj
      hm i j hij hKj μ σ hσ W hWM hWR hescape

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
