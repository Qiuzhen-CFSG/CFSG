module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.MixedCollection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RootCharts

/-!
# The exact U₅ mixed norm from the marked linear Cartan

The SL₂ rank-one word with parameter a⁻¹ is an actual Cartan element.
Conjugating the whole B root by this word gives B(T(p,a)) times an error
in the complementary unitary radical. Cartan normalization and disjointness
of that radical from B force the error to be trivial. Its first natural
SU₃ coordinate then forces T(p,a).second = a*conj(a)*p.second.
Thus both coordinates of the nonabelian Hermitian correction are determined.
The same calculation gives the actual linear coroot action on the whole B
root; reflection supplies the matching action on D.

The natural flag and actor premises are constructed from the original
profiles and generic cover in PositiveApplication. No ordinary-field torus
scalar or exceptional coefficient system is needed: the specified linear
rank-one word works also at q=2 and q=4. These are the mixed norm equations
of Fong--Seitz II (8.24)--(8.31), pp.207--209, proved here from the stronger
already synchronized full natural flag and exact marked rank-one relation.
Full Cartan and Weyl assembly remains separate.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X E K : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
local notation "d" => reflectedUnitaryChart Q split i j s b
local notation "N" => naturalSectionMap Q split j c
variable
  (hA : ∀ a : E, (naturalSectionMap Q split j c
    (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])
  (hC : ∀ a : E, (naturalSectionMap Q split j c
    (inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd a)))).toAdd = ![k*J.conj a,0,0])
  (hD : ∀ p : hermitianUnipotentCoord J, (naturalSectionMap Q split j c
    (inclusion (cross_root_le_own_remainder Q split hm j i hij.symm)
      (reflectedUnitaryChart Q split i j s b p))).toAdd = ![0,k*J.conj p.val.1,0])

variable (hγ : ∀ a : E, (s.val : X ⧸ Q.D)*(γ (.ofAdd a) : X ⧸ Q.D)*s.val = γ (.ofAdd (J.conj a)))
  (T : hermitianUnipotentCoord J → E → hermitianUnipotentCoord J)
  (hT : ∀ p a, (T p a).val.1 = a*p.val.1)
  (hBA : ∀ p a, (b p : X ⧸ Q.D)*alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a)) =
    alignedSimpleParameter Q split i hVi μ s (.ofAdd (ξ a))*(reflectedUnitaryChart Q split i j s b (T p a) : X ⧸ Q.D)*(γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D))

include hm hb hc hk hC hD hγ hT hBA in
omit [Finite E] in
theorem mixed_correction_norm_and_cartan (p : hermitianUnipotentCoord J) (a : E) :
    (T p a).val.2 = a*J.conj a*p.val.2 ∧
      ∀ ha : a ≠ 0,
        let H := alignedTorus Q split i hVi μ s (Units.mk0 (ξ a⁻¹) (by simpa using ha))
        H*(b p : X ⧸ Q.D)*H⁻¹ = b (T p a) := by
  have hss := sourceReflection_sq Q split i hVi μ s
  have hsi : (s.val : X ⧸ Q.D)⁻¹ = s.val := inv_eq_of_mul_eq_one_right hss
  have hAi (z : E) : (A z)⁻¹ = A z := by
    rw [←map_inv]
    change alignedSimpleParameter Q split i hVi μ s (.ofAdd (-ξ z)) = A z
    rw [CharTwo.neg_eq]
  have hconjBA (p : hermitianUnipotentCoord J) (z : E) :
      A z*(b p : X ⧸ Q.D)*A z =
        (d (T p z) : X ⧸ Q.D)*(γ (.ofAdd (z*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
    calc
      _ = (A z)⁻¹*((b p : X ⧸ Q.D)*A z) := by rw [hAi,mul_assoc]
      _ = _ := by rw [hBA]; group
  have hsB (p : hermitianUnipotentCoord J) :
      (s.val : X ⧸ Q.D)*(b p : X ⧸ Q.D)*s.val = d p := by
    rw [reflectedUnitaryChart_apply,hsi]
  have hsD (p : hermitianUnipotentCoord J) :
      (s.val : X ⧸ Q.D)*(d p : X ⧸ Q.D)*s.val = b p := by
    rw [←hsB]
    calc
      _ = ((s.val : X ⧸ Q.D)*s.val)*(b p : X ⧸ Q.D)*(s.val*s.val) := by group
      _ = _ := by rw [hss,one_mul,mul_one]
  have hAD (z : E) (q : hermitianUnipotentCoord J) : Commute (A z) (d q : X ⧸ Q.D) :=
by
      exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (adjacent_roots_commute Q split hm i j hij hVi hVj)
        (alignedSimpleParameter_range Q split i hVi μ s ▸ ⟨.ofAdd (ξ z),rfl⟩))
        _ (d q).property).symm
  have hAsq (z : E) : A z*A z = 1 := by
    calc
      _ = A z*(A z)⁻¹ := congrArg (A z* ·) (hAi z).symm
      _ = 1 := mul_inv_cancel _
  have hADconj (z : E) (q : hermitianUnipotentCoord J) : A z*(d q : X ⧸ Q.D)*A z = d q := by
    rw [(hAD z q).eq,mul_assoc,hAsq,mul_one]
  have hsmul (x y : X ⧸ Q.D) : (s.val : X ⧸ Q.D)*(x*y)*s.val =
      (s.val*x*s.val)*(s.val*y*s.val) := by
    simpa only [MulAut.conj_apply,hsi] using (MulAut.conj (s.val : X ⧸ Q.D)).map_mul x y
  by_cases ha : a = 0
  · have he := hBA p 0
    simp only [map_zero,show (Multiplicative.ofAdd (0:K)) = 1 from rfl,map_one,
      zero_mul,show (Multiplicative.ofAdd (0:E)) = 1 from rfl,OneMemClass.coe_one,
      one_mul,mul_one] at he
    have hd : (d (T p 0) : X ⧸ Q.D) = 1 := mul_right_cancel (he.symm.trans (one_mul _).symm)
    have ht : T p 0 = 1 := (d).injective (Subtype.val_injective (hd.trans (congrArg Subtype.val (d).map_one).symm))
    subst a
    constructor
    · rw [ht]
      change (0:E) = 0*J.conj 0*p.val.2
      simp
    · intro ha
      exact (ha rfl).elim
  let z := a⁻¹
  let r := T p a
  let H := alignedTorus Q split i hVi μ s (Units.mk0 (ξ z) (by simpa [z] using ha))
  have hword : H = A z*(s.val : X ⧸ Q.D)*A a*s.val*A z*s.val := by
    have he := aligned_rankOne_word Q split i hVi μ s (Units.mk0 (ξ z) (by simpa [z] using ha))
    have hz : (ξ z)⁻¹ = ξ a := by simp [z,←map_inv₀]
    simp only [Units.val_mk0,Units.val_inv_eq_inv_val,hz,hsi] at he
    change A z*((s.val : X ⧸ Q.D)*A a*s.val)*A z = H*s.val at he
    calc
      H = H*s.val*s.val := by rw [mul_assoc,hss,mul_one]
      _ = _ := by rw [←he]; group
  have hHmem : H*(b p : X ⧸ Q.D)*H⁻¹ ∈ simpleRoot Q split j :=
    (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split j
      (alignedTorus_mem_cartan Q split i hVi μ s _)) _).mp (b p).property
  have hconj : H*(b p : X ⧸ Q.D)*H⁻¹ =
      A z*((b r : X ⧸ Q.D)*(γ (.ofAdd (J.conj a*p.val.2)) : X ⧸ Q.D)*(d p : X ⧸ Q.D))*A z := by
    calc
      _ = (A z*s.val*A a*s.val)*(A z*(d p : X ⧸ Q.D)*A z)*(s.val*A a*s.val*A z) := by
        rw [hword,←hsB]
        simp only [mul_inv_rev,hAi,hsi]
        group
      _ = (A z*s.val*A a*s.val)*(d p : X ⧸ Q.D)*(s.val*A a*s.val*A z) := by
        rw [hADconj]
      _ = A z*((s.val : X ⧸ Q.D)*(A a*(b p : X ⧸ Q.D)*A a)*s.val)*A z := by
        rw [←hsD]
        group
      _ = _ := by
        rw [hconjBA]
        rw [hsmul,hsmul,hsD,hsB,hγ,map_mul,J.conj_involutive]
  let dv (q : hermitianUnipotentCoord J) := inclusion (cross_root_le_own_remainder Q split hm j i hij.symm) (d q)
  let cv (y : E) := inclusion (opposite_roots_le_remainder Q split i j hij).2 (γ (.ofAdd y))
  let v := dv (T r z)*cv (z*J.conj r.val.2)*
    remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ r))
      (av z*cv (J.conj a*p.val.2)*dv p*(av z)⁻¹)
  have hv : (v : X ⧸ Q.D) = H*(b p : X ⧸ Q.D)*H⁻¹*(b r : X ⧸ Q.D)⁻¹ := by
    change (d (T r z) : X ⧸ Q.D)*(γ (.ofAdd (z*J.conj r.val.2)) : X ⧸ Q.D)*
      (remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ r))
        (av z*cv (J.conj a*p.val.2)*dv p*(av z)⁻¹) : X ⧸ Q.D) = _
    rw [remainderRankOneAction_apply,←hb,hconj]
    change (d (T r z) : X ⧸ Q.D)*(γ (.ofAdd (z*J.conj r.val.2)) : X ⧸ Q.D)*
      ((b r : X ⧸ Q.D)*(A z*(γ (.ofAdd (J.conj a*p.val.2)) : X ⧸ Q.D)*(d p : X ⧸ Q.D)*(A z)⁻¹)*(b r : X ⧸ Q.D)⁻¹) = _
    calc
      _ = ((d (T r z) : X ⧸ Q.D)*(γ (.ofAdd (z*J.conj r.val.2)) : X ⧸ Q.D)*(b r : X ⧸ Q.D))*
          (A z*(γ (.ofAdd (J.conj a*p.val.2)) : X ⧸ Q.D)*(d p : X ⧸ Q.D)*(A z)⁻¹)*(b r : X ⧸ Q.D)⁻¹ := by group
      _ = _ := by
        rw [←hconjBA,hAi z]
        calc
          _ = A z*(b r : X ⧸ Q.D)*(A z*A z)*(γ (.ofAdd (J.conj a*p.val.2)) : X ⧸ Q.D)*(d p : X ⧸ Q.D)*A z*(b r : X ⧸ Q.D)⁻¹ := by group
          _ = _ := by rw [hAsq,mul_one]; group
  have hvone : v = 1 := by
    apply Subtype.ext
    exact (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)).le
      ⟨hv ▸ (simpleRoot Q split j).mul_mem hHmem ((simpleRoot Q split j).inv_mem (b r).property),v.property⟩
  have hcartan : H*(b p : X ⧸ Q.D)*H⁻¹ = b (T p a) := by
    have he : H*(b p : X ⧸ Q.D)*H⁻¹*(b r : X ⧸ Q.D)⁻¹ = 1 :=
      hv.symm.trans (congrArg Subtype.val hvone)
    exact mul_inv_eq_one.mp he
  refine ⟨?_,fun _ => hcartan⟩
  have hact (q : hermitianUnipotentCoord J) (w : simpleRemainder Q split j) :
      (N (remainderRankOneAction Q split j hVj (θ (hermitianUnipotentSU J hJ q)) w)).toAdd =
        Matrix.mulVec (hermitianUnipotentMatrix J q) (N w).toAdd := by
    have he := hc (hermitianUnipotentSU J hJ q) (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w))
    change c (.ofMul (remainderFrattiniAction Q split j hVj (θ (hermitianUnipotentSU J hJ q))
      (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w))) = _ at he
    rw [remainderFrattiniAction_mk] at he
    exact he
  have hzero : (N v).toAdd 0 = 0 := by rw [hvone,map_one]; rfl
  have hvvec : (N v).toAdd 0 =
      k*J.conj (z*J.conj r.val.2) + k*J.conj (J.conj a*p.val.2) + r.val.1*(k*J.conj p.val.1) := by
    change (N (dv (T r z)*cv (z*J.conj r.val.2)*_)).toAdd 0 = _
    rw [map_mul,toAdd_mul,hact]
    have hin : N (av z*cv (J.conj a*p.val.2)*dv p*(av z)⁻¹) =
        N (cv (J.conj a*p.val.2))*N (dv p) := by
      simp only [map_mul,map_inv]
      calc
        _ = (N (av z)*(N (av z))⁻¹)*(N (cv (J.conj a*p.val.2))*N (dv p)) := by ac_rfl
        _ = _ := by rw [mul_inv_cancel,one_mul]
    rw [hin]
    simp only [map_mul,toAdd_mul,dv,cv,hD,hC]
    simp [hermitianUnipotentMatrix]
    ring
  have hp : p.val.2+J.conj p.val.2 = p.val.1*J.conj p.val.1 :=
    (eq_neg_of_add_eq_zero_left p.property).trans (CharTwo.neg_eq _)
  have he : J.conj z*r.val.2 + a*J.conj p.val.2 + a*(p.val.1*J.conj p.val.1) = 0 := by
    apply (mul_eq_zero.mp (show k*(J.conj z*r.val.2+a*J.conj p.val.2+a*(p.val.1*J.conj p.val.1))=0 from ?_)).resolve_left hk
    calc
      _ = (N v).toAdd 0 := by
        rw [hvvec]
        rw [map_mul,map_mul,J.conj_involutive,J.conj_involutive]
        rw [show r.val.1 = a*p.val.1 from hT p a]
        ring
      _ = 0 := hzero
  have haz : J.conj z = (J.conj a)⁻¹ := map_inv₀ J.conj a
  change r.val.2 = _
  rw [haz,←hp] at he
  have hn : J.conj a ≠ 0 := (map_ne_zero J.conj).2 ha
  field_simp [hn] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) he


include hm hb hc hk hC hD hγ hT hBA in
omit [Finite E] in
/-- The constructed mixed correction has the standard full Hermitian norm parameter. -/
theorem mixed_correction_eq_norm (p : hermitianUnipotentCoord J) (a : E) :
    T p a = Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive.normParameter
      (fiveForm J) a p := by
  apply Subtype.ext
  exact Prod.ext (hT p a) (mixed_correction_norm_and_cartan Q split hm i j hij hVi hVj s μ J hJ
    θ b hb γ c hc ξ k hk hC hD hγ T hT hBA p a).1

include hm hb hc hk hC hD hγ hT hBA in
omit [Finite E] in
/-- The specified linear coroot acts on the whole B root by the inverse norm parameter. -/
theorem mixed_linear_cartan_B (u : Eˣ) (p : hermitianUnipotentCoord J) :
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*(b p : X ⧸ Q.D)*H⁻¹ = b
      (Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive.normParameter
        (fiveForm J) (↑u⁻¹ : E) p) := by
  have he := (mixed_correction_norm_and_cartan Q split hm i j hij hVi hVj s μ J hJ
    θ b hb γ c hc ξ k hk hC hD hγ T hT hBA p (↑u⁻¹ : E)).2 (Units.ne_zero u⁻¹)
  rw [mixed_correction_eq_norm Q split hm i j hij hVi hVj s μ J hJ
    θ b hb γ c hc ξ k hk hC hD hγ T hT hBA] at he
  have hu : Units.mk0 (ξ (↑u⁻¹ : E)⁻¹) (by simp) = Units.map ξ.toMonoidHom u := by
    apply Units.ext
    simp
  simpa only [hu] using he

include hm hb hc hk hC hD hγ hT hBA in
omit [Finite E] in
/-- Reflection gives the matching norm action on the entire opposite unitary root. -/
theorem mixed_linear_cartan_D (u : Eˣ) (p : hermitianUnipotentCoord J) :
    let H := alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)
    H*(d p : X ⧸ Q.D)*H⁻¹ = d
      (Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive.normParameter
        (fiveForm J) (u : E) p) := by
  have hsi : (s.val : X ⧸ Q.D)⁻¹ = s.val :=
    inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i hVi μ s)
  have hsB (p : hermitianUnipotentCoord J) :
      (s.val : X ⧸ Q.D)*(b p : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ = d p := by
    rw [reflectedUnitaryChart_apply,hsi]
  have he := congrArg (MulAut.conj (s.val : X ⧸ Q.D))
    (mixed_linear_cartan_B Q split hm i j hij hVi hVj s μ J hJ θ b hb γ c hc ξ k hk
      hC hD hγ T hT hBA u⁻¹ p)
  change (MulAut.conj (s.val : X ⧸ Q.D))
    (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u⁻¹)*(b p : X ⧸ Q.D)*
      (alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u⁻¹))⁻¹) = _ at he
  simp only [map_mul,map_inv,MulAut.conj_apply,hsB,reflection_alignedTorus,inv_inv] at he
  exact he.trans (hsB _)

include hm hb hc hk hA hC hD hγ in
omit [Finite E] in
/-- Full natural flags and the marked linear reflection prove the complete B–A law. -/
theorem mixed_root_norm (p : hermitianUnipotentCoord J) (a : E) :
    (b p : X ⧸ Q.D)*A a = A a*
      (d (Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive.normParameter (fiveForm J) a p) : X ⧸ Q.D)*
      (γ (.ofAdd (a*J.conj p.val.2)) : X ⧸ Q.D)*(b p : X ⧸ Q.D) := by
  obtain ⟨T,hT,hBA⟩ := mixed_root_correction Q split hm i j hij hVi hVj s μ J hJ θ b hb γ c hc ξ k hk hA hC hD
  rw [hBA,mixed_correction_eq_norm Q split hm i j hij hVi hVj s μ J hJ θ b hb γ c hc
    ξ k hk hC hD hγ T hT hBA]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
