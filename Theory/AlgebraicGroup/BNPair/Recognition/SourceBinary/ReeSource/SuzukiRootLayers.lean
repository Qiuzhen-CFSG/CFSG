module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiOmega
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.Frattini.SquareImage
public import Theory.Frattini.OmegaProducts
public import Theory.SpecificGroups.Suzuki.RootOmega
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates

/-!
# The source Suzuki root layers, including the binary root

The explicit inverse b ↦ π(b)/b of a ↦ aπ(a) makes every element of the
actual source Omega a square. The elementary first-coordinate quotient
then identifies its kernel with the entire Frattini subgroup for all m.
The resulting quotient chart retains the literal parameter representatives
and gives the same dimension on every N-conjugate root.

Internal commutators are computed in the source cocycle convention. For
m > 0 the existing matrix-root theorem identifies the derived subgroup
and center with this Frattini subgroup. At m = 0 the distinguished root
element has order four and generates the whole cyclic root; its center
is therefore strictly larger than its Frattini subgroup and its derived
subgroup is trivial. No binary simplicity or perfectness is used.

Source: Fong--Seitz I (1973), proof of (6H), pp.52--56, where squares
control the Omega commutators; II (1974), §10, pp.221--222, where the bar
means quotient by root Omega, and the root law preceding (10.32), p.230.
OriginalRootLayers applies the charts to the same original marked quotient.
These intrinsic root results do not assert the remaining mixed relations.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

theorem tits_norm_inverse (m : ℕ) (b : BinaryGaloisField (2*m+1)) :
    (suzukiTits m b / b) * suzukiTits m (suzukiTits m b / b) = b := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [map_div₀, suzukiTits_sq]
    have ht : suzukiTits m b ≠ 0 := (map_ne_zero _).mpr hb
    field_simp

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

theorem suzukiParameter_inv (a b : BinaryGaloisField (2*m+1)) :
    (suzukiParameter Q split i m μ hB a b)⁻¹ =
      suzukiParameter Q split i m μ hB a (b+a*suzukiTits m a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [suzukiParameter_mul]
  simp only [CharTwo.add_self_eq_zero, ← add_assoc, zero_add]
  exact suzukiParameter_zero Q split i m μ hB

open scoped commutatorElement

theorem suzukiParameter_commutator (a b c d : BinaryGaloisField (2*m+1)) :
    ⁅suzukiParameter Q split i m μ hB a b, suzukiParameter Q split i m μ hB c d⁆ =
      suzukiParameter Q split i m μ hB 0 (a*suzukiTits m c+c*suzukiTits m a) := by
  rw [commutatorElement_def, suzukiParameter_inv, suzukiParameter_inv,
    suzukiParameter_mul, suzukiParameter_mul, suzukiParameter_mul]
  congr 1
  · calc
      a+c+a+c = (a+a)+(c+c) := by abel
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  · have htwo : (2 : BinaryGaloisField (2*m+1)) = 0 := CharP.cast_eq_zero _ 2
    ring_nf
    have hthree : (3 : BinaryGaloisField (2*m+1)) = 1 := by
      calc
        (3 : BinaryGaloisField (2*m+1)) = 2+1 := by norm_num
        _ = 1 := by rw [htwo, zero_add]
    simp only [htwo, hthree, mul_zero, zero_add, add_zero, mul_one]

theorem suzukiParameter_commute_iff (a b c d : BinaryGaloisField (2*m+1)) :
    Commute (suzukiParameter Q split i m μ hB a b) (suzukiParameter Q split i m μ hB c d) ↔
      a*suzukiTits m c = c*suzukiTits m a := by
  rw [← commutatorElement_eq_one_iff_commute, suzukiParameter_commutator,
    suzukiParameter_eq_one_iff]
  simp only [true_and, CharTwo.add_eq_zero]

/-- The paper uses the right commutator x⁻¹y⁻¹xy; here its value agrees
with the computed elementary central commutator. -/
theorem suzukiParameter_right_commutator (a b c d : BinaryGaloisField (2*m+1)) :
    (suzukiParameter Q split i m μ hB a b)⁻¹ * (suzukiParameter Q split i m μ hB c d)⁻¹ *
      suzukiParameter Q split i m μ hB a b * suzukiParameter Q split i m μ hB c d =
        suzukiParameter Q split i m μ hB 0 (a*suzukiTits m c+c*suzukiTits m a) := by
  have hh := suzukiParameter_commutator Q split i m μ hB a (b+a*suzukiTits m a)
    c (d+c*suzukiTits m c)
  rw [← suzukiParameter_inv, ← suzukiParameter_inv] at hh
  simpa only [commutatorElement_def, inv_inv] using hh

theorem suzukiParameter_square_root (b : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB (suzukiTits m b / b) 0 ^ 2 =
      suzukiParameter Q split i m μ hB 0 b := by
  rw [suzukiParameter_square, tits_norm_inverse]

theorem suzukiParameter_pow_four (a b : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB a b ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, suzukiParameter_square,
    suzukiParameter_square]
  simpa only [zero_mul] using suzukiParameter_zero Q split i m μ hB

theorem suzukiParameter_generator_order :
    orderOf (suzukiParameter Q split i m μ hB 1 0) = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one, suzukiParameter_square_eq_one_iff] using
      (one_ne_zero : (1 : BinaryGaloisField (2*m+1)) ≠ 0)
  · exact suzukiParameter_pow_four Q split i m μ hB 1 0

include μ hB in
theorem suzukiOmega_mem_iff_square (x : X ⧸ Q.D) :
    x ∈ omegaOneAmbient (simpleRoot Q split i) ↔
      ∃ y ∈ simpleRoot Q split i, y^2 = x := by
  constructor
  · intro hx
    rw [← suzukiOmegaParameter_range Q split i m μ hB] at hx
    obtain ⟨b,rfl⟩ := hx
    exact ⟨_, (suzukiParameter Q split i m μ hB (suzukiTits m b.toAdd / b.toAdd) 0).property,
      congrArg Subtype.val (suzukiParameter_square_root Q split i m μ hB b.toAdd)⟩
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective ⟨y,hy⟩
    change suzukiParameter Q split i m μ hB a b = ⟨y,hy⟩ at hp
    rw [← suzukiOmegaParameter_range Q split i m μ hB]
    refine ⟨Multiplicative.ofAdd (a*suzukiTits m a), ?_⟩
    exact congrArg Subtype.val ((suzukiParameter_square Q split i m μ hB a b).symm.trans
      (congrArg (fun z => z^2) hp))

include μ hB in
theorem suzuki_frattini_eq_omega :
    frattini (simpleRoot Q split i) =
      (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i) := by
  let : Fact (IsPGroup 2 (simpleRoot Q split i)) := ⟨split.isTwo.to_le (simpleRoot_le Q split i)⟩
  apply le_antisymm
  · rw [← suzukiFirstCoordinate_kernel Q split i m μ hB]
    apply Theory.GroupTheory.frattini_le_ker_of_square_image
    intro a
    change 2 • (suzukiFirstCoordinate Q split i m μ hB a).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  · intro x hx
    obtain ⟨y,hy,he⟩ := (suzukiOmega_mem_iff_square Q split i m μ hB x).mp hx
    have he' : (⟨y,hy⟩ : simpleRoot Q split i)^2 = x := Subtype.ext he
    rw [← he']
    exact pth_power_mem_frattini_of_isPGroup (p := 2) _

include μ hB in
theorem suzuki_frattini_image :
    (frattini (simpleRoot Q split i)).map (simpleRoot Q split i).subtype =
      omegaOneAmbient (simpleRoot Q split i) := by
  rw [suzuki_frattini_eq_omega Q split i m μ hB, map_subgroupOf_eq_of_le (omegaOneAmbient_le _)]

def suzukiFrattiniQuotientEquiv :
    (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) ≃*
      Multiplicative (BinaryGaloisField (2*m+1)) :=
  (QuotientGroup.quotientMulEquivOfEq (suzuki_frattini_eq_omega Q split i m μ hB)).trans
    (suzukiOmegaQuotientEquiv Q split i m μ hB)

@[simp] theorem suzukiFrattiniQuotientEquiv_parameter (a b : BinaryGaloisField (2*m+1)) :
    suzukiFrattiniQuotientEquiv Q split i m μ hB
      (QuotientGroup.mk (suzukiParameter Q split i m μ hB a b)) = Multiplicative.ofAdd a :=
  suzukiFirstCoordinate_parameter Q split i m μ hB a b

include μ hB in
theorem suzuki_frattini_quotient_card :
    Nat.card (simpleRoot Q split i ⧸ frattini (simpleRoot Q split i)) = 2^(2*m+1) := by
  rw [Nat.card_congr (suzukiFrattiniQuotientEquiv Q split i m μ hB).toEquiv,
    Nat.card_congr Multiplicative.ofAdd.symm]
  exact GaloisField.card 2 (2*m+1) (by omega)

include μ hB in
theorem suzuki_rootAt_frattini_quotient_card (w : Weyl Q) :
    Nat.card (HexagonStructure.rootAt Q split i w ⧸
      frattini (HexagonStructure.rootAt Q split i w)) = 2^(2*m+1) := by
  unfold HexagonStructure.rootAt
  rw [Nat.card_congr (QuotientGroup.congr _ _
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w))
    (frattini_map_equiv _)).toEquiv]
  exact suzuki_frattini_quotient_card Q split i m μ hB

include μ hB in
theorem suzuki_frattini_eq_center (hm : 0 < m) :
    frattini (simpleRoot Q split i) = center (simpleRoot Q split i) := by
  rw [suzuki_frattini_eq_omega Q split i m μ hB]
  ext x
  have hΩ : x ∈ (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i) ↔
      x^2 = 1 := by
    obtain ⟨⟨a,b⟩,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
    change suzukiParameter Q split i m μ hB a b = x at hp
    rw [← suzukiFirstCoordinate_kernel Q split i m μ hB, ← hp, MonoidHom.mem_ker,
      suzukiFirstCoordinate_parameter, suzukiParameter_square_eq_one_iff]
    exact Multiplicative.ofAdd.injective.eq_iff
  rw [hΩ]
  let e := suzukiRootEquiv Q split i m μ hB
  have hc : e x ∈ center (SuzukiRootSubgroup m) ↔ x ∈ center (simpleRoot Q split i) := by
    constructor
    · intro hx
      have hh : e.symm (e x) ∈ center (simpleRoot Q split i) :=
        ((centerCongr e).symm ⟨e x,hx⟩).property
      simpa only [e.symm_apply_apply] using hh
    · intro hx
      exact (centerCongr e ⟨x,hx⟩).property
  rw [← hc, ← suzukiRootSubgroup_square_iff_center m hm, ← map_pow, ← map_one e]
  exact e.injective.eq_iff.symm

include μ hB in
theorem suzuki_derived_eq_frattini (hm : 0 < m) :
    _root_.commutator (simpleRoot Q split i) = frattini (simpleRoot Q split i) := by
  rw [suzuki_frattini_eq_center Q split i m μ hB hm]
  let e := suzukiRootEquiv Q split i m μ hB
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  change _root_.commutator (SuzukiRootSubgroup m) = _
  rw [SchurCover.Family.root_commutator_eq_center m hm]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, ((centerCongr e).symm ⟨x,hx⟩).property, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property

variable (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include μ₀ hB₀ in
theorem binary_suzuki_root_cyclic : IsCyclic (simpleRoot Q split i) := by
  apply isCyclic_of_orderOf_eq_card (suzukiParameter Q split i 0 μ₀ hB₀ 1 0)
  rw [suzukiParameter_generator_order, Nat.card_congr (suzukiRootEquiv Q split i 0 μ₀ hB₀).toEquiv,
    matrixRoot_card]
  norm_num

include μ₀ hB₀ in
theorem binary_suzuki_root_center : center (simpleRoot Q split i) = ⊤ := by
  let := binary_suzuki_root_cyclic Q split i μ₀ hB₀
  exact center_eq_top

include μ₀ hB₀ in
theorem binary_suzuki_root_derived : _root_.commutator (simpleRoot Q split i) = ⊥ := by
  let := binary_suzuki_root_cyclic Q split i μ₀ hB₀
  rw [_root_.commutator_def]
  exact commutator_eq_bot_iff_le_centralizer.mpr (by rw [coe_top, centralizer_univ, center_eq_top])

include μ₀ hB₀ in
theorem binary_suzuki_frattini_lt_center :
    frattini (simpleRoot Q split i) < center (simpleRoot Q split i) := by
  rw [binary_suzuki_root_center Q split i μ₀ hB₀]
  apply lt_top_iff_ne_top.mpr
  intro ht
  have hg : suzukiParameter Q split i 0 μ₀ hB₀ 1 0 ∈ frattini (simpleRoot Q split i) := by
    rw [ht]; trivial
  rw [suzuki_frattini_eq_omega Q split i 0 μ₀ hB₀,
    ← suzukiFirstCoordinate_kernel Q split i 0 μ₀ hB₀, MonoidHom.mem_ker,
    suzukiFirstCoordinate_parameter] at hg
  exact one_ne_zero (congrArg (fun z : Multiplicative (BinaryGaloisField 1) => z.toAdd) hg)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
