module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The actual source Suzuki Omega and root quotient

The source root square is `(a,b)^2 = (0,a*pi(a))`. Hence its elements
of order dividing two are precisely the second-coordinate subgroup.
That additive subgroup is the literal ambient Omega, is central in the
root, and has order q. The first-coordinate homomorphism has exactly
this kernel and gives the marked quotient by Omega as the additive field.

These statements include q = 2, where the root is cyclic of order four
and its center is strictly larger than Omega. The source bar notation
in Fong–Seitz II §10, (10.4)–(10.6), pp.221–222, refers to this quotient;
it does not replace it by a quotient by the full center. The source
multiplication is the formula preceding (10.32), p.230. No natural action
on the later four-dimensional layer is assumed or claimed here.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

private theorem matrixRootPoint_zero : matrixRootPoint m 0 0 = 1 :=
  Subtype.ext (Subtype.ext (BenderSuzuki.External.suzukiRootGL_zero_zero m))

theorem suzukiParameter_zero : suzukiParameter Q split i m μ hB 0 0 = 1 := by
  rw [suzukiParameter, matrixRootPoint_zero, map_one]

theorem suzukiParameter_eq_one_iff (a b : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB a b = 1 ↔ a = 0 ∧ b = 0 := by
  rw [← suzukiParameter_zero Q split i m μ hB]
  have hinj := (suzukiParameter_bijective Q split i m μ hB).injective
  simpa only [Prod.mk.injEq] using (hinj.eq_iff (a := (a,b)) (b := (0,0)))

theorem suzukiParameter_square (a b : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB a b ^ 2 =
      suzukiParameter Q split i m μ hB 0 (a*suzukiTits m a) := by
  rw [pow_two, suzukiParameter_mul]
  simp only [CharTwo.add_self_eq_zero, zero_add]

theorem suzukiParameter_square_eq_one_iff (a b : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB a b ^ 2 = 1 ↔ a = 0 := by
  rw [suzukiParameter_square, suzukiParameter_eq_one_iff]
  simp only [true_and, mul_eq_zero, (suzukiTits m).map_eq_zero_iff, or_self]

def suzukiOmegaParameter : Multiplicative (BinaryGaloisField (2*m+1)) →* X ⧸ Q.D where
  toFun b := suzukiParameter Q split i m μ hB 0 b.toAdd
  map_one' := congrArg Subtype.val (suzukiParameter_zero Q split i m μ hB)
  map_mul' b d := by
    change (suzukiParameter Q split i m μ hB 0 (b.toAdd+d.toAdd) : X ⧸ Q.D) = _
    rw [← Subgroup.coe_mul, suzukiParameter_mul]
    simp only [zero_mul, add_zero]

theorem suzukiOmegaParameter_injective : Function.Injective (suzukiOmegaParameter Q split i m μ hB) := by
  intro a b hab
  have he := (suzukiParameter_bijective Q split i m μ hB).injective
    (a₁ := (0,a.toAdd)) (a₂ := (0,b.toAdd))
    (show suzukiParameter Q split i m μ hB 0 a.toAdd =
      suzukiParameter Q split i m μ hB 0 b.toAdd from Subtype.ext hab)
  exact congrArg Multiplicative.ofAdd (congrArg Prod.snd he)

/-- The source Omega is the second coordinate, including the cyclic root at q = 2. -/
theorem suzukiOmegaParameter_range :
    (suzukiOmegaParameter Q split i m μ hB).range = omegaOneAmbient (simpleRoot Q split i) := by
  apply le_antisymm
  · rintro x ⟨b,rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
      (suzukiParameter Q split i m μ hB 0 b.toAdd).property
    exact congrArg Subtype.val
      ((suzukiParameter_square_eq_one_iff Q split i m μ hB 0 b.toAdd).mpr rfl)
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hsq
    obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective ⟨x,hx⟩
    change suzukiParameter Q split i m μ hB a b = ⟨x,hx⟩ at hp
    have ha : a = 0 := (suzukiParameter_square_eq_one_iff Q split i m μ hB a b).mp
      (by rw [hp]; exact Subtype.ext hsq)
    subst a
    exact ⟨Multiplicative.ofAdd b, congrArg Subtype.val hp⟩

include μ hB in
theorem suzukiOmega_centralizes :
    omegaOneAmbient (simpleRoot Q split i) ≤ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  rw [← suzukiOmegaParameter_range Q split i m μ hB]
  rintro x ⟨b,rfl⟩
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨⟨c,d⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective ⟨y,hy⟩
  change suzukiParameter Q split i m μ hB c d = ⟨y,hy⟩ at hp
  have he : suzukiParameter Q split i m μ hB c d * suzukiParameter Q split i m μ hB 0 b.toAdd =
      suzukiParameter Q split i m μ hB 0 b.toAdd * suzukiParameter Q split i m μ hB c d := by
    rw [suzukiParameter_mul, suzukiParameter_mul]
    simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add, add_comm d]
  have hh := congrArg Subtype.val he
  rw [hp] at hh
  exact hh

include μ hB in
theorem suzukiOmega_card :
    Nat.card (omegaOneAmbient (simpleRoot Q split i)) = 2 ^ (2*m+1) := by
  rw [← suzukiOmegaParameter_range Q split i m μ hB,
    ← Nat.card_congr (MonoidHom.ofInjective (suzukiOmegaParameter_injective Q split i m μ hB)).toEquiv,
    Nat.card_congr Multiplicative.ofAdd.symm]
  exact GaloisField.card 2 (2*m+1) (by omega)

/-- Recover the first coordinate in the natural faithful quotient chart. -/
def suzukiFirstCoordinate : simpleRoot Q split i →* Multiplicative (BinaryGaloisField (2*m+1)) where
  toFun x := Multiplicative.ofAdd
    ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm x).1
  map_one' := by
    rw [← suzukiParameter_zero Q split i m μ hB]
    change Multiplicative.ofAdd
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
        ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)) (0,0))).1 = 1
    rw [Equiv.symm_apply_apply]
    rfl
  map_mul' x y := by
    obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
    obtain ⟨⟨c,d⟩,hq⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective y
    change suzukiParameter Q split i m μ hB a b = x at hp
    change suzukiParameter Q split i m μ hB c d = y at hq
    rw [← hp, ← hq, suzukiParameter_mul]
    change Multiplicative.ofAdd
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
        ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB))
          (a+c,b+d+a*suzukiTits m c))).1 =
      Multiplicative.ofAdd
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
        ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)) (a,b))).1 *
      Multiplicative.ofAdd
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
        ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)) (c,d))).1
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl

@[simp] theorem suzukiFirstCoordinate_parameter (a b : BinaryGaloisField (2*m+1)) :
    suzukiFirstCoordinate Q split i m μ hB (suzukiParameter Q split i m μ hB a b) =
      Multiplicative.ofAdd a := by
  change Multiplicative.ofAdd
    ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)).symm
      ((Equiv.ofBijective _ (suzukiParameter_bijective Q split i m μ hB)) (a,b))).1 = _
  rw [Equiv.symm_apply_apply]

theorem suzukiFirstCoordinate_surjective :
    Function.Surjective (suzukiFirstCoordinate Q split i m μ hB) :=
  fun a => ⟨suzukiParameter Q split i m μ hB a.toAdd 0,
    suzukiFirstCoordinate_parameter Q split i m μ hB a.toAdd 0⟩

/-- The bar in the source is quotient by Omega, including q = 2. -/
theorem suzukiFirstCoordinate_kernel : (suzukiFirstCoordinate Q split i m μ hB).ker =
    (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i) := by
  ext x
  obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
  change suzukiParameter Q split i m μ hB a b = x at hp
  rw [← hp, MonoidHom.mem_ker, suzukiFirstCoordinate_parameter]
  constructor
  · intro ha
    have ha' : a = 0 := congrArg Multiplicative.toAdd ha
    subst a
    change (suzukiParameter Q split i m μ hB 0 b : X ⧸ Q.D) ∈ omegaOneAmbient _
    rw [← suzukiOmegaParameter_range Q split i m μ hB]
    exact ⟨Multiplicative.ofAdd b,rfl⟩
  · intro hx
    change (suzukiParameter Q split i m μ hB a b : X ⧸ Q.D) ∈ omegaOneAmbient _ at hx
    rw [← suzukiOmegaParameter_range Q split i m μ hB] at hx
    obtain ⟨c,hc⟩ := hx
    have he := (suzukiParameter_bijective Q split i m μ hB).injective
      (a₁ := (0,c.toAdd)) (a₂ := (a,b)) (Subtype.ext hc)
    exact congrArg Multiplicative.ofAdd (congrArg Prod.fst he).symm

instance rootOmega_normal :
    ((omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i)).Normal := by
  have he : (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i) =
      omega₁ (simpleRoot Q split i) (p := 2) := by
    change ((omega₁ (simpleRoot Q split i) (p := 2)).map (simpleRoot Q split i).subtype).comap
      (simpleRoot Q split i).subtype = _
    rw [comap_map_eq, ker_subtype, sup_bot_eq]
  rw [he]
  let := omega₁_characteristic (simpleRoot Q split i) (p := 2)
  infer_instance

def suzukiOmegaQuotientEquiv :
    (simpleRoot Q split i ⧸
      (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i)) ≃*
        Multiplicative (BinaryGaloisField (2*m+1)) := by
  exact (QuotientGroup.quotientMulEquivOfEq (suzukiFirstCoordinate_kernel Q split i m μ hB).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (suzukiFirstCoordinate Q split i m μ hB)
      (suzukiFirstCoordinate_surjective Q split i m μ hB))

@[simp] theorem suzukiOmegaQuotientEquiv_parameter (a b : BinaryGaloisField (2*m+1)) :
    suzukiOmegaQuotientEquiv Q split i m μ hB
      (QuotientGroup.mk (suzukiParameter Q split i m μ hB a b)) = Multiplicative.ofAdd a :=
  suzukiFirstCoordinate_parameter Q split i m μ hB a b

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
