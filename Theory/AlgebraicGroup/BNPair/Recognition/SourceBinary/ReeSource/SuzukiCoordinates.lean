module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneCoordinates
public import Theory.SpecificGroups.Suzuki.SmallInvolutionPair
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Suzuki coordinates on the actual source simple root, including Sz(2)

The natural faithful panel degree is one more than the Sylow root order.
For positive parameters this follows from the ovoid action. At parameter
zero, Sylow subgroups have order four and are not normal: otherwise the
known order-five product of two involutions would belong to one of them.
Their normalizer therefore has index five.

The literal matrix root chart has multiplication
`(a,b)(c,d) = (a+c,b+d+a*pi(c))`. The entry computation is adapted from
the private calculation in `BenderSuzuki.External.Huppert.XI.lemma_3_1`;
its public packaged structure theorem excludes zero, whereas this
calculation does not. The panel-kernel theorem then puts this complete
chart on the same source simple root, preserving the exact faithful
quotient marking and the whole Borel normalizer.

Source: Fong–Seitz I (2A), pp.7–8, and II §10, pp.221–222 and the
multiplication formula preceding (10.32), p.230. A natural faithful
rank-one quotient marking is an earlier catalogue input. This module
does not select the Ree row, synchronize the two root fields, or prove
the mixed relations. No perfectness hypothesis or positive-parameter
restriction is imposed.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private def binaryRootSylow : Sylow 2 (SuzukiMatrixGroup 0) := by
  have hcard := suzukiZeroRootSubgroup_card
  have hp : IsPGroup 2 suzukiZeroRootSubgroup := IsPGroup.of_card (n := 2) hcard
  have hi : suzukiZeroRootSubgroup.index = 5 := by
    have he := suzukiZeroRootSubgroup.card_mul_index
    rw [hcard, suzukiZero_card] at he
    omega
  exact hp.toSylow (by rw [hi]; decide)

private theorem binary_sylow_card (T : Sylow 2 (SuzukiMatrixGroup 0)) : Nat.card T = 4 := by
  rw [Nat.card_congr (T.equiv binaryRootSylow).toEquiv]
  exact suzukiZeroRootSubgroup_card

private theorem binary_sylow_not_normal (T : Sylow 2 (SuzukiMatrixGroup 0)) :
    ¬ (T : Subgroup (SuzukiMatrixGroup 0)).Normal := by
  intro hn
  let := hn
  have hmem {x : SuzukiMatrixGroup 0} (hx : orderOf x = 2) : x ∈ T := by
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, hx]; rfl)
    have he := hp.inf_normalizer_sylow T
    change zpowers x ⊓ normalizer ((T : Subgroup (SuzukiMatrixGroup 0)) : Set _) = _ at he
    rw [normalizer_eq_top, inf_top_eq] at he
    exact (le_of_inf_eq he.symm) (mem_zpowers x)
  have hu := hmem suzukiZeroInvolution_order
  have hv := hmem (suzukiWeyl_orderOf 0)
  have hdiv := orderOf_dvd_natCard (⟨suzukiZeroInvolution * suzukiWeyl 0, T.mul_mem hu hv⟩ : T)
  have ho := orderOf_injective (T : Subgroup (SuzukiMatrixGroup 0)).subtype
    (T : Subgroup (SuzukiMatrixGroup 0)).subtype_injective
    (⟨suzukiZeroInvolution * suzukiWeyl 0, T.mul_mem hu hv⟩ : T)
  change orderOf (suzukiZeroInvolution * suzukiWeyl 0) =
    orderOf (⟨suzukiZeroInvolution * suzukiWeyl 0, T.mul_mem hu hv⟩ : T) at ho
  rw [← ho, suzukiZeroInvolution_mul_weyl_order] at hdiv
  change 5 ∣ Nat.card (T : Subgroup (SuzukiMatrixGroup 0)) at hdiv
  rw [binary_sylow_card T] at hdiv
  norm_num at hdiv

private theorem binary_normalizer_index (T : Sylow 2 (SuzukiMatrixGroup 0)) :
    (normalizer (T : Set (SuzukiMatrixGroup 0))).index = 5 := by
  have hcard : T.index = 5 := by
    have hh := (T : Subgroup (SuzukiMatrixGroup 0)).card_mul_index
    rw [binary_sylow_card, suzukiZero_card] at hh
    omega
  have hd : (normalizer (T : Set (SuzukiMatrixGroup 0))).index ∣ 5 := by
    rw [← hcard]
    exact index_dvd_of_le (le_normalizer (H := (T : Subgroup (SuzukiMatrixGroup 0))))
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
  · have ht : normalizer (T : Set (SuzukiMatrixGroup 0)) = ⊤ := index_eq_one.mp h
    exact False.elim (binary_sylow_not_normal T (normalizer_eq_top_iff.mp ht))
  · exact h

/-- The natural Suzuki panel degree, for every parameter including the Frobenius group Sz(2). -/
theorem suzuki_normalizer_index (m : ℕ) (T : Sylow 2 (SuzukiMatrixGroup m)) :
    (normalizer (T : Set (SuzukiMatrixGroup m))).index = 1 + Nat.card T := by
  by_cases hm : m = 0
  · subst m
    rw [binary_normalizer_index, binary_sylow_card]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  obtain ⟨A,hA⟩ := suzukiRootSubgroup_isSylow m hmpos
  have hc : Nat.card T = Nat.card A := Nat.card_congr (T.equiv A).toEquiv
  have hi : (normalizer (T : Set (SuzukiMatrixGroup m))).index =
      (normalizer (A : Set (SuzukiMatrixGroup m))).index := by
    rw [← T.card_eq_index_normalizer, ← A.card_eq_index_normalizer]
  rw [hi, hc]
  change (normalizer ((A : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))).index =
    1 + Nat.card (A : Subgroup (SuzukiMatrixGroup m))
  rw [hA, suzukiRootSubgroup_normalizer m hmpos, suzukiBorelSubgroup_eq_stabilizer m hmpos]
  rw [index_eq_card]
  rw [suzukiRootSubgroup_card m hmpos]
  have hb : Function.Bijective (MulAction.ofQuotientStabilizer (SuzukiMatrixGroup m)
      (suzukiOvoidInfinity m)) := by
    refine ⟨MulAction.injective_ofQuotientStabilizer _ _, ?_⟩
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) (suzukiOvoidInfinity m) y
    exact ⟨QuotientGroup.mk g,hg⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hb), suzukiOvoid_card, Nat.add_comm]


open BenderSuzuki.PFAppendixIII

def matrixRootPoint (m : ℕ) (a b : BinaryGaloisField (2*m+1)) : SuzukiRootSubgroup m :=
  ⟨⟨SuzukiRootGL m a b, subset_closure (Or.inl ⟨a,b,rfl⟩)⟩,
    (mem_suzukiRootSubgroup_iff m _).mpr ⟨a,b,rfl⟩⟩

private theorem rootMatrix_mul (m : ℕ) (a b c d : BinaryGaloisField (2*m+1)) :
    SuzukiRootGL m a b * SuzukiRootGL m c d =
      SuzukiRootGL m (a+c) (b+d+a*suzukiTits m c) := by
  have hpow (x : BinaryGaloisField (2*m+1)) :
      x ^ (2^(m+1)) = suzukiTits m x := (suzukiTits_apply m x).symm
  have hpow_one (x : BinaryGaloisField (2*m+1)) :
      x ^ (1+2^(m+1)) = x*suzukiTits m x := by rw [pow_add, hpow, pow_one]
  have hpow_two (x : BinaryGaloisField (2*m+1)) :
      x ^ (2+2^(m+1)) = x^2*suzukiTits m x := by rw [pow_add, hpow]
  have htwo : (2 : BinaryGaloisField (2*m+1)) = 0 := CharP.cast_eq_zero _ 2
  have hthree : (3 : BinaryGaloisField (2*m+1)) = 1 := by
    calc
      (3 : BinaryGaloisField (2*m+1)) = 2+1 := by norm_num
      _ = 1 := by rw [htwo, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, CharTwo.add_self_eq_zero]
  all_goals try simp only [hpow, hpow_one, hpow_two, map_add, map_mul, suzukiTits_sq]
  all_goals ring_nf
  all_goals simp [htwo, hthree]

theorem matrixRootPoint_mul (m : ℕ) (a b c d : BinaryGaloisField (2*m+1)) :
    matrixRootPoint m a b * matrixRootPoint m c d =
      matrixRootPoint m (a+c) (b+d+a*suzukiTits m c) :=
  Subtype.ext (Subtype.ext (rootMatrix_mul m a b c d))

theorem matrixRootPoint_bijective (m : ℕ) : Function.Bijective
    (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) => matrixRootPoint m p.1 p.2) := by
  constructor
  · intro p q h
    apply Prod.ext
    · exact congrArg (fun x : SuzukiRootSubgroup m => x.val.val (0 : Fin 4) (1 : Fin 4)) h
    · exact congrArg (fun x : SuzukiRootSubgroup m => x.val.val (0 : Fin 4) (2 : Fin 4)) h
  · intro x
    obtain ⟨a,b,hab⟩ := (mem_suzukiRootSubgroup_iff m x.val).mp x.property
    exact ⟨(a,b), Subtype.ext (Subtype.ext hab.symm)⟩

/-- The standard matrix root has q² elements also when m = 0. -/
theorem matrixRoot_card (m : ℕ) :
    Nat.card (SuzukiRootSubgroup m) = (2 ^ (2*m+1)) ^ 2 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (matrixRootPoint_bijective m)), Nat.card_prod]
  have hc : Nat.card (BinaryGaloisField (2*m+1)) = 2 ^ (2*m+1) :=
    GaloisField.card 2 (2*m+1) (by omega)
  rw [hc, pow_two]

/-- A standard Sylow with its actual matrix-root carrier, including Sz(2). -/
def matrixRootSylow (m : ℕ) : Sylow 2 (SuzukiMatrixGroup m) := by
  by_cases hm : m = 0
  · subst m
    have hc : Nat.card (SuzukiRootSubgroup 0) = 4 := by simpa using matrixRoot_card 0
    have hp : IsPGroup 2 (SuzukiRootSubgroup 0) := IsPGroup.of_card (n := 2) hc
    have hi : (SuzukiRootSubgroup 0).index = 5 := by
      have hh := (SuzukiRootSubgroup 0).card_mul_index
      rw [hc, suzukiZero_card] at hh
      omega
    exact hp.toSylow (by rw [hi]; decide)
  · exact (suzukiRootSubgroup_isSylow m (Nat.pos_of_ne_zero hm)).choose

theorem matrixRootSylow_carrier (m : ℕ) :
    (matrixRootSylow m : Subgroup (SuzukiMatrixGroup m)) = SuzukiRootSubgroup m := by
  unfold matrixRootSylow
  split_ifs with hm
  · subst m; rfl
  · exact (suzukiRootSubgroup_isSylow m (Nat.pos_of_ne_zero hm)).choose_spec

open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Coordinates on the actual source root, with the natural matrix-root marking. -/
def suzukiRootEquiv : simpleRoot Q split i ≃* SuzukiRootSubgroup m :=
  (modelRootEquiv Q split i μ (matrixRootSylow m)
    (by
      change (quotientBorel Q i).map μ.toMonoidHom =
        normalizer ((matrixRootSylow m : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
      rw [matrixRootSylow_carrier]
      exact hB)
    (suzuki_normalizer_index m (matrixRootSylow m))).trans
    (MulEquiv.subgroupCongr (matrixRootSylow_carrier m))

@[simp] theorem suzukiRootEquiv_model (r : simpleRoot Q split i) :
    (suzukiRootEquiv Q split i m μ hB r : SuzukiMatrixGroup m) =
      μ (rootProjection Q split i r) := rfl

/-- The source Suzuki parameter belongs to the literal simple intersection. -/
def suzukiParameter (a b : BinaryGaloisField (2*m+1)) : simpleRoot Q split i :=
  (suzukiRootEquiv Q split i m μ hB).symm (matrixRootPoint m a b)

theorem suzukiParameter_bijective : Function.Bijective
    (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) =>
      suzukiParameter Q split i m μ hB p.1 p.2) :=
  (suzukiRootEquiv Q split i m μ hB).symm.bijective.comp (matrixRootPoint_bijective m)

theorem suzukiParameter_mul (a b c d : BinaryGaloisField (2*m+1)) :
    suzukiParameter Q split i m μ hB a b * suzukiParameter Q split i m μ hB c d =
      suzukiParameter Q split i m μ hB (a+c) (b+d+a*suzukiTits m c) := by
  simp only [suzukiParameter, ← map_mul, matrixRootPoint_mul]

/-- The projection retains both source coordinates and their order. -/
theorem suzukiParameter_projection (a b : BinaryGaloisField (2*m+1)) :
    μ (rootProjection Q split i (suzukiParameter Q split i m μ hB a b)) =
      (matrixRootPoint m a b : SuzukiMatrixGroup m) := by
  rw [← suzukiRootEquiv_model Q split i m μ hB, suzukiParameter, MulEquiv.apply_symm_apply]

theorem suzukiParameter_range : Set.range
    (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) =>
      (suzukiParameter Q split i m μ hB p.1 p.2 : X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact (suzukiParameter Q split i m μ hB p.1 p.2).property
  · intro hx
    obtain ⟨p,hp⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective ⟨x,hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
