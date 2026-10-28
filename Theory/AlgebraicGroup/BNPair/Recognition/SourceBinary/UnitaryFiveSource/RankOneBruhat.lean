module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.FullCartan

/-!
# Both rank-one Bruhat words in the synchronized U₅ source

The determinant-one pair (u,u⁻¹) in the constructed full Cartan is exactly
the aligned SL₂ coroot. Transporting its two-by-two Bruhat identity gives
the A-root presentation equation with the specified source reflection.
That same reflection swaps the entire B and D roots, including centers.

The second simple coroot is the transported SU₃ diagonal. Its actual
three-by-three Weyl element is an involution and satisfies the full B-root
Bruhat formula, with exactly FiveBruhat's two nonabelian root parameters.
This calculation stays in SU₃ before transport and retains scalar kernels.
BruhatApplication supplies both formulas on literal original Q.q words.
The unitary Weyl element's marked-normalizer placement and its other
root and Cartan equations still require the source comparison.
Source: Fong--Seitz II (8C), pp.203–210, through (8.37); Huppert II.10.12
for the Hermitian rank-one Bruhat matrix identity.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative Pointwise
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
variable {X E K : Type*} [Group X] [Field E] [CharP E 2]
  [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) E]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : localGroup Q split i ≃* PSL(2,K))
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (θ : J.specialSubgroup ≃* rankOne Q split j)
  (b : hermitianUnipotentCoord J ≃* simpleRoot Q split j)
  (hb : ∀ p, (b p : X ⧸ Q.D) = θ (hermitianUnipotentSU J hJ p))
  (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
    ≃ₗ[ZMod 2] (Fin 3 → E))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2)
    (remainderFrattiniAction Q split j hVj) (θ a) v) = Matrix.mulVec a.val.val (c v))
  (ξ : E ≃+* K) (k : E) (hk : k ≠ 0)
local notation "A" => fun a : E => alignedSimpleParameter Q split i hVi μ s (Multiplicative.ofAdd (ξ a))
local notation "av" => fun a : E => linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a)
variable (hA : ∀ a : E, (naturalSectionMap Q split j c
  (linearRootInUnitaryRadical Q split i j hij hVi s μ (ξ a))).toAdd = ![0,0,k*J.conj a])


local notation "H" => fullUnitaryCartan Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA

include hb hc hk hA in
omit [CharP E 2] in
/-- The linear coroot in the full source Cartan has determinant-one pair (u,u⁻¹). -/
theorem fullUnitaryCartan_coroot (u : Eˣ) :
    H (u,u⁻¹) = alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u) := by
  have hp : unitaryCartanParameter J (u,u⁻¹) = 1 := by
    simp [unitaryCartanParameter]
  change alignedTorus Q split i hVi μ s (Units.map ξ.toMonoidHom u)*
    unitaryTorus Q split j J hJ θ (unitaryCartanParameter J (u,u⁻¹)) = _
  rw [hp,map_one,mul_one]

include hb hc hk hA in
omit [CharP E 2] in
/-- The specified linear reflection satisfies the exact nonzero rank-one
Bruhat equation with the constructed two-parameter Cartan. -/
theorem fullUnitaryCartan_linear_bruhat (a : E) (ha : a ≠ 0) :
    (s.val : X ⧸ Q.D)*A a*s.val =
      A a⁻¹*H (FiveBruhat.aTorus a ha)*s.val*A a⁻¹ := by
  have htor : H (FiveBruhat.aTorus a ha) =
      alignedTorus Q split i hVi μ s (Units.mk0 (ξ a) ((map_ne_zero ξ).mpr ha))⁻¹ := by
    change H ((Units.mk0 a ha)⁻¹,Units.mk0 a ha) = _
    have hh := fullUnitaryCartan_coroot Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA (Units.mk0 a ha)⁻¹
    simp only [inv_inv] at hh
    rw [hh]
    congr 1
    apply Units.ext
    simp
  rw [htor,←alignedPinningHom_weyl Q split i hVi μ s]
  simp only [alignedSimpleParameter_apply,alignedTorus,map_inv₀,←map_mul]
  apply congrArg (alignedPinningHom Q split i hVi μ s)
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,(map_ne_zero ξ).mpr ha,CharTwo.add_self_eq_zero]

variable (γ : Multiplicative E ≃* rootAt Q split i (Q.simple j))
local notation "R" => synchronizedRoots Q split i j hVi s μ J b γ ξ

omit [CharP E 2] [Algebra (ZMod 2) E] in
/-- The specified linear reflection interchanges both entire unitary roots,
so the equations hold on their centers as well. -/
theorem synchronizedRoots_linear_reflection :
    (s.val : X ⧸ Q.D)*s.val = 1 ∧
    (∀ p, (s.val : X ⧸ Q.D)*(R).B p*s.val = (R).D p) ∧
    ∀ p, (s.val : X ⧸ Q.D)*(R).D p*s.val = (R).B p := by
  have hs := sourceReflection_sq Q split i hVi μ s
  have hsi : (s.val : X ⧸ Q.D)⁻¹ = s.val := inv_eq_of_mul_eq_one_right hs
  refine ⟨hs,?_,?_⟩
  · intro p
    change _ = (reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)
    erw [reflectedUnitaryChart_apply,hsi]
    rfl
  · intro p
    change (s.val : X ⧸ Q.D)*(reflectedUnitaryChart Q split i j s b p : X ⧸ Q.D)*s.val = (b p : X ⧸ Q.D)
    erw [reflectedUnitaryChart_apply,hsi]
    calc
      _ = ((s.val : X ⧸ Q.D)*s.val)*(b p : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*s.val) := by group
      _ = _ := by rw [hs,one_mul,mul_one]


/-- The unitary rank-one Weyl element in the same element-preserving actor. -/
def unitaryWeyl : X ⧸ Q.D := θ (hermitianWeylSU J hJ)

omit [CharP E 2] [Algebra (ZMod 2) E] in
theorem unitaryWeyl_square :
    unitaryWeyl Q split j J hJ θ * unitaryWeyl Q split j J hJ θ = 1 := by
  have hw : hermitianWeylSU J hJ * hermitianWeylSU J hJ = 1 := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro x y
    change ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) E) * hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) E) x y = (1 : Matrix (Fin 3) (Fin 3) E) x y
    fin_cases x <;> fin_cases y <;> simp [hermitianWeylMatrix,Matrix.mul_apply,Fin.sum_univ_three]
  change (θ (hermitianWeylSU J hJ) : X ⧸ Q.D)*(θ (hermitianWeylSU J hJ) : X ⧸ Q.D) = 1
  rw [←coe_mul,←map_mul,hw,map_one,coe_one]

include hb hc hk hA in
omit [CharP E 2] in
/-- The unitary rank-one torus is the second simple coroot in the full Cartan. -/
theorem fullUnitaryCartan_unitary (u : Eˣ) :
    H (1,(Units.map J.conj.toMonoidHom u)⁻¹) = unitaryTorus Q split j J hJ θ u := by
  have hp : unitaryCartanParameter J (1,(Units.map J.conj.toMonoidHom u)⁻¹) = u := by
    apply Units.ext
    simp only [unitaryCartanParameter,MonoidHom.coe_mk,OneHom.coe_mk,Units.val_inv_eq_inv_val,
      Units.coe_map,one_mul,map_inv]
    change (J.conj (J.conj (u:E)))⁻¹⁻¹ = (u:E)
    rw [J.conj_involutive,inv_inv]
  change alignedTorusHom Q split i hVi μ s (Units.map ξ.toMonoidHom 1)*
    unitaryTorus Q split j J hJ θ (unitaryCartanParameter J (1,(Units.map J.conj.toMonoidHom u)⁻¹)) = _
  rw [hp,map_one,map_one,one_mul]

omit [CharP E 2] [Algebra (ZMod 2) E] in
private theorem unitary_bruhat_matrix (p : hermitianUnipotentCoord J) (hp : p.val.2 ≠ 0) :
    hermitianWeylSU J hJ * hermitianUnipotentSU J hJ p * hermitianWeylSU J hJ =
      hermitianUnipotentSU J hJ (hermitianBruhatLeft J p hp) *
        hermitianTorusSU J hJ (Units.mk0 p.val.2 hp) * hermitianWeylSU J hJ *
          hermitianUnipotentSU J hJ (hermitianBruhatRight J p hp) := by
  have hcp : J.conj p.val.2 ≠ 0 := (map_ne_zero J.conj).mpr hp
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  change (hermitianWeylMatrix * hermitianUnipotentMatrix J p * hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) E) x y =
    (hermitianUnipotentMatrix J (hermitianBruhatLeft J p hp) * hermitianTorusMatrix J (Units.mk0 p.val.2 hp) *
      hermitianWeylMatrix * hermitianUnipotentMatrix J (hermitianBruhatRight J p hp) : Matrix (Fin 3) (Fin 3) E) x y
  fin_cases x <;> fin_cases y <;>
    simp [hermitianWeylMatrix,hermitianUnipotentMatrix,hermitianTorusMatrix,
      hermitianBruhatLeft,hermitianBruhatRight,Matrix.mul_apply,Fin.sum_univ_three]
  all_goals field_simp [hp,hcp]
  all_goals try rw [J.conj_involutive]
  all_goals try linear_combination p.val.2 * p.property
  all_goals try (ring_nf; done)
  simpa [add_comm,add_left_comm,add_assoc] using p.property.symm

include hb hc hk hA in
/-- The full nonabelian B-root Bruhat equation in the original SU₃ actor,
with exactly the full-Cartan and root parameters of the U₅ presentation. -/
theorem fullUnitaryCartan_unitary_bruhat (p : hermitianUnipotentCoord J) (hp : p.val.2 ≠ 0) :
    unitaryWeyl Q split j J hJ θ * (b p : X ⧸ Q.D) * unitaryWeyl Q split j J hJ θ =
      (b (FiveBruhat.leftParameter (fiveForm J) p hp) : X ⧸ Q.D) *
        H (FiveBruhat.bTorus (fiveForm J) p hp) * unitaryWeyl Q split j J hJ θ *
          (b (FiveBruhat.rightParameter (fiveForm J) p hp) : X ⧸ Q.D) := by
  have hl : FiveBruhat.leftParameter (fiveForm J) p hp = hermitianBruhatLeft J p hp := by
    apply Subtype.ext
    change (p.val.1/J.conj p.val.2,p.val.2⁻¹) = (-p.val.1/J.conj p.val.2,p.val.2⁻¹)
    rw [CharTwo.neg_eq]
  have hr : FiveBruhat.rightParameter (fiveForm J) p hp = hermitianBruhatRight J p hp := by
    apply Subtype.ext
    change (p.val.1/p.val.2,p.val.2⁻¹) = (-p.val.1/p.val.2,p.val.2⁻¹)
    rw [CharTwo.neg_eq]
  have ht : H (FiveBruhat.bTorus (fiveForm J) p hp) =
      unitaryTorus Q split j J hJ θ (Units.mk0 p.val.2 hp) :=
    fullUnitaryCartan_unitary Q split i j hij hVi hVj s μ J hJ θ b hb c hc ξ k hk hA _
  rw [hl,hr,ht,hb,hb,hb]
  simpa [unitaryWeyl,unitaryTorus] using congrArg (fun g : J.specialSubgroup => (θ g : X ⧸ Q.D))
    (unitary_bruhat_matrix J hJ p hp)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
