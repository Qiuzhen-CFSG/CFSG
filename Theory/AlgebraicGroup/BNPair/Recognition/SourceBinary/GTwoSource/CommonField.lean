module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RootPairing
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.LongRootModule

/-!
# A common field for the actual middle pairing

Nonsingularity of the middle pairing puts the long-root commutator EB in A.
The existing long rank-one calculation then supplies EB multiplication and
its natural Cartan action without a normalized DC premise. Every element of
the full Cartan acts by a scalar in each rank-one labeling: it commutes with
the own-root square scalars, which exhaust the finite characteristic-two field.

Conjugating DC by the long Cartan consequently gives scalar covariance of its
actual coefficient. Nonsingularity makes the two unit groups correspond
bijectively. Biadditivity and symmetry then construct a field automorphism
σ and a nonzero κ with DC coefficient κ σ(dc). No classification of tensor
representations is assumed, and both q=2 and q=4 are included.

UnitCoefficient forces κ=1, and CommonFieldPinning transports σ through
the whole long rank-one pinning. Arbitrarily supplied independent local labels are
not asserted to satisfy normalized DC. The selected-orientation source
application is CommonFieldApplication.

Source: Fong--Seitz II (9.8)--(9.14), printed pp.212--216. The argument
uses the actual rank-one words and left commutators on the marked quotient;
it supplies the common-field part of the module-label comparison directly.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hm : rotationOrder Q = 6)
  (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)

private theorem root_mem (i : Fin 6) (a : F) : (alignedSourceRoots Q split hK μ n short).x i a ∈ positiveCarrier Q split short i := by
  rw [← alignedSourceRoots_range Q split hK μ n short i]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (i : Fin 6) : Function.Injective ((alignedSourceRoots Q split hK μ n short).x i) :=
  (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective

private theorem root_commute (i : Fin 6) (a b : F) : Commute ((alignedSourceRoots Q split hK μ n short).x i a) ((alignedSourceRoots Q split hK μ n short).x i b) := by
  change (alignedSourceRoots Q split hK μ n short).x i a * (alignedSourceRoots Q split hK μ n short).x i b = (alignedSourceRoots Q split hK μ n short).x i b * (alignedSourceRoots Q split hK μ n short).x i a
  rw [← (alignedSourceRoots Q split hK μ n short).x_add,← (alignedSourceRoots Q split hK μ n short).x_add,add_comm]

include hm hne in
/-- The middle Heisenberg group has no extra vectors fixed by both C and D.
This uses nondegeneracy of the actual additive pairing, before field normalization. -/
theorem middle_centralizer_of_pairing (x : X ⧸ Q.D)
    (hx : x ∈ middleRoots Q split (1-short) short)
    (hC : ∀ t, Commute x ((alignedSourceRoots Q split hK μ n short).x 2 t)) (hD : ∀ t, Commute x ((alignedSourceRoots Q split hK μ n short).x 3 t)) :
    x ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range := by
  have hij : (1-short : Fin 2) ≠ short := by fin_cases short <;> decide
  have hx' : x ∈ (middleRoots Q split (1-short) short : Set (X ⧸ Q.D)) := hx
  rw [middleRoots_product Q split hm (1-short) short hij] at hx'
  obtain ⟨da,⟨d,hd,a,ha,rfl⟩,c,hc,rfl⟩ := hx'
  change d ∈ positiveCarrier Q split short 3 at hd
  change a ∈ positiveCarrier Q split short 0 at ha
  change c ∈ positiveCarrier Q split short 2 at hc
  rw [← alignedSourceRoots_range Q split hK μ n short 3] at hd
  rw [← alignedSourceRoots_range Q split hK μ n short 0] at ha
  rw [← alignedSourceRoots_range Q split hK μ n short 2] at hc
  obtain ⟨d,rfl⟩ := hd
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨c,rfl⟩ := hc
  change (alignedSourceRoots Q split hK μ n short).x 3 d.toAdd *
    (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd *
    (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd ∈ _
  change ∀ t, Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd * (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd * (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 t) at hC
  change ∀ t, Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd * (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd * (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 t) at hD
  let R := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hAC (t : F) : Commute ((alignedSourceRoots Q split hK μ n short).x 0 a.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 t) := (R.ca _ _).symm
  have hCC (t : F) := root_commute Q split hK μ n short 2 c.toAdd t
  have hDC (t : F) : Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 t) := by
    have hh := (hC t).mul_left ((hAC t).mul_left (hCC t)).inv_left
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have hd0 : d.toAdd = 0 := by
    apply (middleCoefficient_nondegenerate Q split hK μ n short hm hne d.toAdd).mp
    intro t
    rw [middleCoefficient_symmetric Q split hK μ n short hm hne t d.toAdd]
    apply root_inj Q split hK μ n short 0
    rw [←middleCoefficient_spec Q split hK μ n short hm,PositiveRoots.x_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hDC t).eq
  simp only [hd0,(alignedSourceRoots Q split hK μ n short).x_zero,one_mul] at hD ⊢
  have hAD (t : F) : Commute ((alignedSourceRoots Q split hK μ n short).x 0 a.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 t) := (R.da _ _).symm
  have hCD (t : F) : Commute ((alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 t) := by
    have hh := (hAD t).inv_left.mul_left (hD t)
    simpa only [inv_mul_cancel_left] using hh
  have hc0 : c.toAdd = 0 := by
    apply (middleCoefficient_nondegenerate Q split hK μ n short hm hne c.toAdd).mp
    intro t
    apply root_inj Q split hK μ n short 0
    rw [←middleCoefficient_spec Q split hK μ n short hm,PositiveRoots.x_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hCD t).symm.eq
  simpa only [hc0,(alignedSourceRoots Q split hK μ n short).x_zero,mul_one,PositiveRoots.x,ofAdd_toAdd] using
    (show (alignedSourceRoots Q split hK μ n short).root 0 a ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range from ⟨a,rfl⟩)

include hm hne in
/-- Radical containment and the DC pairing put EB in the actual highest root. -/
theorem aligned_eb_mem_of_pairing (b e : F) : ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,(alignedSourceRoots Q split hK μ n short).x 1 b⁆ ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hE : (alignedSourceRoots Q split hK μ n short).x 4 e ∈ simpleRemainder Q split short :=
    simpleRoot_le_other_remainder Q split hm (1-short) short hij.symm
      (root_mem Q split hK μ n short 4 e)
  have hB : (alignedSourceRoots Q split hK μ n short).x 1 b ∈ simpleRemainder Q split short :=
    (exchanged_roots_le_remainder Q split hm (1-short) short hij.symm).1
      (root_mem Q split hK μ n short 1 b)
  have hx := radical_commutator_le_middle_of_linear Q split hm (1-short) short hij.symm
    (hK (1-short)) (μ (1-short)) (commutator_mem_commutator hE hB)
  let R := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  apply middle_centralizer_of_pairing Q split hK μ n short hm hne _ hx
  · intro t
    have he : Commute ((alignedSourceRoots Q split hK μ n short).x 4 e) ((alignedSourceRoots Q split hK μ n short).x 2 t) := R.ec _ _
    have hb : Commute ((alignedSourceRoots Q split hK μ n short).x 1 b) ((alignedSourceRoots Q split hK μ n short).x 2 t) := (R.cb _ _).symm
    exact ((he.mul_left hb).mul_left he.inv_left).mul_left hb.inv_left
  · intro t
    have he : Commute ((alignedSourceRoots Q split hK μ n short).x 4 e) ((alignedSourceRoots Q split hK μ n short).x 3 t) := R.ed _ _
    have hb : Commute ((alignedSourceRoots Q split hK μ n short).x 1 b) ((alignedSourceRoots Q split hK μ n short).x 3 t) := (R.db _ _).symm
    exact ((he.mul_left hb).mul_left he.inv_left).mul_left hb.inv_left


include hm hne in
/-- The actual nonzero middle pairing gives the full natural long-root action,
before either local field labeling has been changed. -/
theorem aligned_long_natural_action_of_pairing :
    (∀ e b : F, (alignedSourceRoots Q split hK μ n short).x 4 e *
      (alignedSourceRoots Q split hK μ n short).x 1 b =
        (alignedSourceRoots Q split hK μ n short).x 0 (b*e) *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 4 e) ∧
    ∀ (a : Fˣ) (b : F), MulAut.conj
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)
      ((alignedSourceRoots Q split hK μ n short).x 0 b) =
        (alignedSourceRoots Q split hK μ n short).x 0 ((a : F)*b) :=
  aligned_long_natural_action_of_commutator_mem Q split hK μ n short hm
    (aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne)
    (aligned_eb_mem_of_pairing Q split hK μ n short hm hne)

/-- Every element of the full Cartan acts by a scalar in each actual
rank-one labeling. This follows from commuting with all own-root squares. -/
theorem exists_cartan_root_scalar (i : Fin 2) {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N) :
    ∃ b : Fˣ, ∀ c : F,
      MulAut.conj t (alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd c)) =
        alignedSimpleParameter Q split i (hK i) (μ i) (n i) (.ofAdd ((b : F)*c)) := by
  let U := alignedSimpleParameter Q split i (hK i) (μ i) (n i)
  let T := alignedTorusHom Q split i (hK i) (μ i) (n i)
  have hinj : Function.Injective (fun c : F => U (.ofAdd c)) :=
    (alignedSimpleParameter_injective Q split i (hK i) (μ i) (n i)).comp
      Multiplicative.ofAdd.injective
  have hmem : MulAut.conj t (U (.ofAdd (1 : F))) ∈ simpleRoot Q split i :=
    (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split i ht) _).mp
      (alignedSimpleParameter_range Q split i (hK i) (μ i) (n i) ▸ ⟨.ofAdd 1,rfl⟩)
  rw [←alignedSimpleParameter_range Q split i (hK i) (μ i) (n i)] at hmem
  obtain ⟨b,hb⟩ := hmem
  have hval : MulAut.conj t (U (.ofAdd (1 : F))) = U (.ofAdd b.toAdd) := hb.symm
  have hb0 : b.toAdd ≠ 0 := by
    intro hz
    have he : MulAut.conj t (U (.ofAdd (1 : F))) = MulAut.conj t (U (.ofAdd (0 : F))) := by
      simpa only [hz,ofAdd_zero,map_one] using hval
    exact one_ne_zero (hinj ((MulAut.conj t).injective he))
  refine ⟨Units.mk0 b.toAdd hb0, ?_⟩
  intro c
  by_cases hc : c = 0
  · simp only [hc,mul_zero,ofAdd_zero,map_one]
  obtain ⟨a,ha⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := F))) c
  change a^2=c at ha
  have ha0 : a ≠ 0 := by intro hz; apply hc; rw [←ha,hz]; simp
  let a' := Units.mk0 a ha0
  have hcomm : Commute t (T a') := by
    let := split.abelian
    exact congrArg Subtype.val (mul_comm
      (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
      (⟨_,alignedTorus_mem_cartan Q split i (hK i) (μ i) (n i) a'⟩ :
        ↥(Q.tits.B ⊓ Q.tits.N)))
  have hfix : MulAut.conj t (T a') = T a' := by
    change t*T a'*t⁻¹=T a'
    rw [hcomm.eq,mul_assoc,mul_inv_cancel,mul_one]
  have hown := alignedTorus_root Q split i (hK i) (μ i) (n i) a' 1
  change T a' * U (.ofAdd (1 : F)) * (T a')⁻¹ = U (.ofAdd ((a : F)^2*1)) at hown
  rw [mul_one,ha] at hown
  have he := congrArg (MulAut.conj t) hown
  rw [map_mul,map_mul,map_inv,hfix,hval] at he
  have hscale := alignedTorus_root Q split i (hK i) (μ i) (n i) a' b.toAdd
  change T a' * U (.ofAdd b.toAdd) * (T a')⁻¹ = U (.ofAdd (a^2*b.toAdd)) at hscale
  rw [hscale,ha] at he
  simpa only [Units.val_mk0,mul_comm c b.toAdd] using he.symm

include hm hne in
/-- The long Cartan acts on one middle input by an actual short-field scalar
and on the highest-root output by its original long-field parameter. -/
theorem middleCoefficient_scalar_covariance :
    ∃ θ : Fˣ → Fˣ, ∀ (a : Fˣ) (d c : F),
      middleCoefficient Q split hK μ n short hm ((θ a : F)*d) c =
        (a : F)*middleCoefficient Q split hK μ n short hm d c := by
  classical
  let L := alignedSourceRoots Q split hK μ n short
  let T := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  let r : X ⧸ Q.D := (n (1-short)).val
  let R := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hex (a : Fˣ) := exists_cartan_root_scalar Q split hK μ n short
    (alignedTorus_mem_cartan Q split (1-short) (hK (1-short)) (μ (1-short))
      (n (1-short)) a⁻¹)
  choose θ hθ using hex
  refine ⟨θ,?_⟩
  intro a d c
  have hF (v : F) : MulAut.conj (T a⁻¹) (L.x 5 v) = L.x 5 ((θ a : F)*v) := hθ a v
  have hrF (v : F) : MulAut.conj r (L.x 5 v) = L.x 3 v :=
    sourceBorelWeyl_rF Q split hK μ n short split.abelian v
  have ht : MulAut.conj r (T a⁻¹) = T a := by
    change (n (1-short)).val * alignedTorus Q split (1-short) (hK (1-short))
      (μ (1-short)) (n (1-short)) a⁻¹ * ((n (1-short)).val : X ⧸ Q.D)⁻¹ =
        alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a
    simpa only [inv_inv] using
      reflection_alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a⁻¹
  have hD : MulAut.conj (T a) (L.x 3 d) = L.x 3 ((θ a : F)*d) := by
    have he := congrArg (MulAut.conj r) (hF d)
    change MulAut.conj r (T a⁻¹ * L.x 5 d * (T a⁻¹)⁻¹) = _ at he
    rw [map_mul,map_mul,ht,hrF,hrF,map_inv,ht] at he
    exact he
  have hC : MulAut.conj (T a) (L.x 2 c) = L.x 2 c := by
    have hh := aligned_long_centralizes Q split hK μ n short hm R
      (show T a ∈ rankOne Q split (1-short) from
        (show T a ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split (1-short) from
          (alignedTorusHom_range Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))) ▸ ⟨a,rfl⟩).2)
    change T a*L.x 2 c*(T a)⁻¹=L.x 2 c
    rw [←mem_centralizer_iff.mp hh _ (root_mem Q split hK μ n short 2 c),
      mul_assoc,mul_inv_cancel,mul_one]
  have hA := (aligned_long_natural_action_of_pairing Q split hK μ n short hm hne).2 a
  have he := congrArg (MulAut.conj (T a))
    (middleCoefficient_spec Q split hK μ n short hm d c)
  rw [map_commutatorElement,hD,hC,hA,middleCoefficient_spec Q split hK μ n short hm] at he
  exact root_inj Q split hK μ n short 0 he

private theorem field_equiv_of_pairing_covariance {K : Type*} [Field K] [Finite K]
    (g : K → K → K)
    (hadd : ∀ d e c, g (d+e) c=g d c+g e c)
    (hz : ∀ c, g 0 c=0)
    (hsym : ∀ d c, g d c=g c d)
    (hnd : ∀ c, (∀ d, g d c=0) ↔ c=0)
    (θ : Kˣ → Kˣ) (hθ : ∀ (a : Kˣ) d c, g ((θ a : K)*d) c=(a : K)*g d c) :
    ∃ (κ : K) (σ : K ≃+* K), κ ≠ 0 ∧ ∀ d c, g d c=κ*σ (d*c) := by
  classical
  have hex : ∃ d c, g d c ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero ((hnd 1).mp (fun d => h d 1))
  obtain ⟨d₀,c₀,h₀⟩ := hex
  have hinj : Function.Injective θ := by
    intro a b hab
    apply Units.ext
    apply mul_right_cancel₀ h₀
    exact (hθ a d₀ c₀).symm.trans ((congrArg (fun t : Kˣ => g ((t : K)*d₀) c₀) hab).trans
      (hθ b d₀ c₀))
  have hsurj := Finite.surjective_of_injective hinj
  have hκ : g 1 1 ≠ 0 := by
    intro hzero
    apply (one_ne_zero : (1 : K) ≠ 0)
    apply (hnd 1).mp
    intro d
    by_cases hd : d=0
    · simpa only [hd] using hz 1
    obtain ⟨a,ha⟩ := hsurj (Units.mk0 d hd)
    have hh := hθ a 1 1
    simpa only [ha,Units.val_mk0,mul_one,hzero,mul_zero] using hh
  have hprod (d c : K) : g d c*g 1 1=g d 1*g c 1 := by
    by_cases hd : d=0
    · simp only [hd,hz,zero_mul]
    obtain ⟨a,ha⟩ := hsurj (Units.mk0 d hd)
    have hdc := hθ a 1 c
    have hd1 := hθ a 1 1
    simp only [ha,Units.val_mk0,mul_one] at hdc hd1
    rw [hdc,hd1,hsym 1 c]
    ring
  have hmul (d c : K) : g (d*c) 1*g 1 1=g d 1*g c 1 := by
    by_cases hd : d=0
    · simp only [hd,hz,zero_mul]
    obtain ⟨a,ha⟩ := hsurj (Units.mk0 d hd)
    have hdc := hθ a c 1
    have hd1 := hθ a 1 1
    simp only [ha,Units.val_mk0,mul_one] at hdc hd1
    rw [hdc,hd1]
    ring
  let f : K →+* K :=
    { toFun := fun d => g d 1 / g 1 1
      map_zero' := by simp only [hz,zero_div]
      map_one' := div_self hκ
      map_add' := by intro d c; rw [hadd,add_div]
      map_mul' := by
        intro d c
        field_simp
        exact hmul d c }
  let σ : K ≃+* K := RingEquiv.ofBijective f
    ⟨f.injective,Finite.surjective_of_injective f.injective⟩
  refine ⟨g 1 1,σ,hκ,?_⟩
  intro d c
  change g d c=g 1 1*(g (d*c) 1/g 1 1)
  rw [mul_div_cancel₀ _ hκ]
  exact mul_right_cancel₀ hκ ((hprod d c).trans (hmul d c).symm)

include hm hne in
/-- The actual middle pairing has one common field automorphism, up to its
nonzero unit coefficient. This includes q=2 and q=4, without classifying a
four-dimensional tensor representation. The unit coefficient and whole-pinning
transport are separate remaining steps. -/
theorem exists_middleCoefficient_field_equiv :
    ∃ (κ : F) (σ : F ≃+* F), κ ≠ 0 ∧ ∀ d c : F,
      middleCoefficient Q split hK μ n short hm d c=κ*σ (d*c) := by
  obtain ⟨θ,hθ⟩ := middleCoefficient_scalar_covariance Q split hK μ n short hm hne
  exact field_equiv_of_pairing_covariance
    (middleCoefficient Q split hK μ n short hm)
    (middleCoefficient_add_left Q split hK μ n short hm)
    (middleCoefficient_zero_left Q split hK μ n short hm)
    (middleCoefficient_symmetric Q split hK μ n short hm hne)
    (middleCoefficient_nondegenerate Q split hK μ n short hm hne) θ hθ

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
