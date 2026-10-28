module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual coordinates from the higher central commutator

A scalar character of the literal central commutator yields a homomorphism
in each argument. It descends through the supplied doubled natural section.
Evaluation on three basis vectors in a nonzero factor constructs the dual
coordinate homomorphism with the SAME source marking. The nonzero dual orbit
proves surjectivity; the relative index bound identifies its kernel exactly.

The scalar character is constructed using the elementary abelian subgroup;
it is not an extra source assumption. The geometric commutator bounds and
the doubled natural section remain explicit. The source application is in
`Quotients/Source.lean`.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (4.5.4)(v), p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients
open DistanceFour.Linear
private abbrev F := ZMod 2
private abbrev T := Multiplicative F
private abbrev VectorGroup := Multiplicative W

private def coordinates (f : VectorGroup →* T) : W :=
  fun i => (f (Multiplicative.ofAdd (Pi.single i 1))).toAdd

private theorem coordinates_eval (f : VectorGroup →* T) (v : W) :
    (f (Multiplicative.ofAdd v)).toAdd = dotProduct (coordinates f) v := by
  let l : W →ₗ[F] F := (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2
  have hv : v = ∑ i : Fin 3, v i • Pi.single i (1 : F) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  change l v = _
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul, coordinates, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

private theorem coordinates_action (f h : VectorGroup →* T) (g : S)
    (he : ∀ v : W, h (Multiplicative.ofAdd (g.val.mulVec v)) = f (Multiplicative.ofAdd v)) :
    coordinates h = dual g (coordinates f) := by
  funext i
  have hh := he ((g⁻¹).val.mulVec (Pi.single i 1))
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at hh
  have hh' := congrArg Multiplicative.toAdd hh
  change coordinates h i = _ at hh'
  rw [coordinates_eval] at hh'
  change coordinates h i = dual g (coordinates f) i
  rw [hh', dual, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp

variable {M : Type*} [Group M] {R L : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} {common : CommonFacts R source geometry}

private def pairingCoordinates {A : Subgroup (FreeAmalgam R)}
    (b : A →* (VectorGroup →* T)) : A →* VectorGroup where
  toFun x := Multiplicative.ofAdd (coordinates (b x))
  map_one' := by ext i; simp [coordinates]
  map_mul' x y := by ext i; simp [coordinates]

private theorem equivariant_onto {A : Subgroup (FreeAmalgam R)}
    (hn : Mbar R ≤ normalizer A) (q : A →* VectorGroup)
    (hact : ∀ (m : M) (x y : A),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      (q y).toAdd = dual (common.natural.marking (source.projection m)) (q x).toAdd)
    (hne : ∃ x, q x ≠ 1) : Function.Surjective q := by
  obtain ⟨x, hx⟩ := hne
  have hx' : (q x).toAdd ≠ 0 := fun h => hx (Multiplicative.toAdd.injective h)
  intro v
  by_cases hv : v = 1
  · exact ⟨1, by simpa using hv.symm⟩
  have hv' : v.toAdd ≠ 0 := fun h => hv (Multiplicative.toAdd.injective h)
  obtain ⟨g, hg⟩ := dual_orbit hx' hv'
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp hn _ ⟨m,rfl⟩ _ x.property⟩
  refine ⟨y, Multiplicative.toAdd.injective ?_⟩
  rw [hact m x y rfl, hmg]
  exact hg


/-- An invariant scalar pairing constructs dual coordinates, with the exact
kernel certified by the size of the actual relative quotient. -/
private theorem dualSection_of_scalar_pairing [Finite M]
    {A N : Subgroup (FreeAmalgam R)}
    (hlocal : A ≤ stabilizer R (alpha R)) (hle : N ≤ A)
    (hA : Mbar R ≤ normalizer A) (hN : Mbar R ≤ normalizer N)
    (b : A →* (VectorGroup →* T))
    (hzero : ∀ x : A, (x : FreeAmalgam R) ∈ N → b x = 1)
    (hact : ∀ (m : M) (x y : A),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W, b y (Multiplicative.ofAdd
        ((common.natural.marking (source.projection m)).val.mulVec v)) =
          b x (Multiplicative.ofAdd v))
    (hne : ∃ (x : A) (v : W), b x (Multiplicative.ofAdd v) ≠ 1)
    (hcard : N.relIndex A ≤ 8) :
    Nonempty (MarkedDualSection source common A N) := by
  let q := pairingCoordinates b
  have hqact : ∀ (m : M) (x y : A),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      (q y).toAdd = dual (common.natural.marking (source.projection m)) (q x).toAdd := by
    intro m x y hy
    exact coordinates_action _ _ _ (hact m x y hy)
  have hqne : ∃ x, q x ≠ 1 := by
    obtain ⟨x, v, hx⟩ := hne
    refine ⟨x, fun hh => hx (Multiplicative.toAdd.injective ?_)⟩
    have hh' : coordinates (b x) = 0 := congrArg Multiplicative.toAdd hh
    rw [coordinates_eval, hh', zero_dotProduct]
    rfl
  have honto := equivariant_onto hA q hqact hqne
  have hkill : N.subgroupOf A ≤ q.ker := by
    intro x hx
    change Multiplicative.ofAdd (coordinates (b x)) = 1
    rw [hzero x hx]
    rfl
  have hAM : A ≤ Mbar R := by
    simpa only [alpha, stabilizer_m_base] using hlocal
  let : (N.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer (hAM.trans hN)
  let : Finite (Mbar R) := Finite.of_surjective (embedM R).rangeRestrict (embedM R).rangeRestrict_surjective
  let : Finite A := Finite.of_injective (inclusion hAM) (inclusion_injective _)
  let f := QuotientGroup.lift (N.subgroupOf A) q hkill
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,hx⟩ := honto v
    exact ⟨QuotientGroup.mk x,hx⟩
  have hinj : Function.Injective f := (hf.bijective_of_nat_card_le (by
    change (N.subgroupOf A).index ≤ Nat.card VectorGroup
    simpa [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, ZMod.card, Subgroup.relIndex] using hcard)).1
  have hker : q.ker = N.subgroupOf A := by
    apply le_antisymm ?_ hkill
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply hinj
    exact (MonoidHom.mem_ker.mp hx).trans f.map_one.symm
  exact ⟨⟨hlocal, hle, hA, q, honto, hker, hqact⟩⟩

private def factorEmbedding (i : Bool) : VectorGroup →* Multiplicative (W × W) where
  toFun v := Multiplicative.ofAdd (if i then (v.toAdd, 0) else (0, v.toAdd))
  map_one' := by cases i <;> rfl
  map_mul' v w := by cases i <;> rfl

private def restrictPairing {A : Subgroup (FreeAmalgam R)}
    (b : A →* (Multiplicative (W × W) →* T)) (i : Bool) : A →* (VectorGroup →* T) where
  toFun x := (b x).comp (factorEmbedding i)
  map_one' := by ext v; simp
  map_mul' x y := by ext v; simp

/-- Either factor of a nonzero scalar pairing with two natural copies gives
surjective dual coordinates. No choice of a new SL3 marking is made. -/
private theorem dualSection_of_pair_scalar_pairing [Finite M]
    {A N : Subgroup (FreeAmalgam R)}
    (hlocal : A ≤ stabilizer R (alpha R)) (hle : N ≤ A)
    (hA : Mbar R ≤ normalizer A) (hN : Mbar R ≤ normalizer N)
    (b : A →* (Multiplicative (W × W) →* T))
    (hzero : ∀ x : A, (x : FreeAmalgam R) ∈ N → b x = 1)
    (hact : ∀ (m : M) (x y : A),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W × W, b y (Multiplicative.ofAdd
        ((common.natural.marking (source.projection m)).val.mulVec v.1,
         (common.natural.marking (source.projection m)).val.mulVec v.2)) =
          b x (Multiplicative.ofAdd v))
    (hne : ∃ (x : A) (v : W × W), b x (Multiplicative.ofAdd v) ≠ 1)
    (hcard : N.relIndex A ≤ 8) :
    Nonempty (MarkedDualSection source common A N) := by
  classical
  have hn : ∃ (i : Bool) (x : A) (v : W),
      restrictPairing b i x (Multiplicative.ofAdd v) ≠ 1 := by
    by_contra hn
    push Not at hn
    obtain ⟨x, v, hx⟩ := hne
    have hv : Multiplicative.ofAdd v =
        factorEmbedding true (Multiplicative.ofAdd v.1) *
          factorEmbedding false (Multiplicative.ofAdd v.2) := by
      apply Multiplicative.toAdd.injective
      simp [factorEmbedding]
    apply hx
    rw [hv, map_mul]
    exact (congrArg₂ (· * ·) (hn true x v.1) (hn false x v.2)).trans (one_mul 1)
  obtain ⟨i,x,v,hx⟩ := hn
  refine dualSection_of_scalar_pairing hlocal hle hA hN (restrictPairing b i) ?_ ?_
    ⟨x,v,hx⟩ hcard
  · intro x hx
    apply MonoidHom.ext
    intro v
    change b x (factorEmbedding i v) = 1
    rw [hzero x hx]
    rfl
  · intro m x y hy v
    have hh := hact m x y hy (factorEmbedding i (Multiplicative.ofAdd v)).toAdd
    cases i <;> simpa only [restrictPairing, MonoidHom.coe_mk, OneHom.coe_mk,
      MonoidHom.comp_apply, factorEmbedding, Bool.false_eq_true, Bool.true_eq,
      reduceIte, toAdd_ofAdd, Matrix.mulVec_zero] using hh

open scoped commutatorElement IsMulCommutative

private def centralCharacterRow {A B : Subgroup (FreeAmalgam R)}
    (hB : B ≤ Mbar R)
    (hc : ⁅A,B⁆ ≤ centralizer (Mbar R : Set (FreeAmalgam R)))
    (χ : (⁅A,B⁆ : Subgroup (FreeAmalgam R)) →* T) (a : A) : B →* T where
  toFun b := χ ⟨⁅(a : FreeAmalgam R), (b : FreeAmalgam R)⁆,
    commutator_mem_commutator a.property b.property⟩
  map_one' := by
    exact (congrArg χ (Subtype.ext (by simp))).trans χ.map_one
  map_mul' b c := by
    rw [← map_mul]
    apply congrArg χ
    apply Subtype.ext
    change ⁅(a : FreeAmalgam R), (b : FreeAmalgam R) * (c : FreeAmalgam R)⁆ =
      ⁅(a : FreeAmalgam R), (b : FreeAmalgam R)⁆ * ⁅(a : FreeAmalgam R), (c : FreeAmalgam R)⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅(a : FreeAmalgam R), (b : FreeAmalgam R)⁆ (b : FreeAmalgam R),
      hc (commutator_mem_commutator a.property c.property) b (hB b.property)]
    group

private def centralCharacterPairing {A B : Subgroup (FreeAmalgam R)}
    (hA : A ≤ Mbar R) (hB : B ≤ Mbar R)
    (hc : ⁅A,B⁆ ≤ centralizer (Mbar R : Set (FreeAmalgam R)))
    (χ : (⁅A,B⁆ : Subgroup (FreeAmalgam R)) →* T) : A →* (B →* T) where
  toFun a := centralCharacterRow hB hc χ a
  map_one' := by
    apply MonoidHom.ext
    intro b
    change χ ⟨⁅(1 : FreeAmalgam R), (b : FreeAmalgam R)⁆, _⟩ = 1
    exact (congrArg χ (Subtype.ext (by simp))).trans χ.map_one
  map_mul' a c := by
    apply MonoidHom.ext
    intro b
    change χ _ = χ _ * χ _
    rw [mul_comm, ← map_mul]
    apply congrArg χ
    apply Subtype.ext
    change ⁅(a : FreeAmalgam R) * (c : FreeAmalgam R), (b : FreeAmalgam R)⁆ =
      ⁅(c : FreeAmalgam R), (b : FreeAmalgam R)⁆ * ⁅(a : FreeAmalgam R), (b : FreeAmalgam R)⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      hc (commutator_mem_commutator c.property b.property) a (hA a.property)]
    group

private theorem centralCharacterPairing_conjugation {A B : Subgroup (FreeAmalgam R)}
    (hA : A ≤ Mbar R) (hB : B ≤ Mbar R)
    (hc : ⁅A,B⁆ ≤ centralizer (Mbar R : Set (FreeAmalgam R)))
    (χ : (⁅A,B⁆ : Subgroup (FreeAmalgam R)) →* T) (m : M) (a c : A) (b d : B)
    (ha : (c : FreeAmalgam R) = embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹)
    (hb : (d : FreeAmalgam R) = embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹) :
    centralCharacterPairing hA hB hc χ c d = centralCharacterPairing hA hB hc χ a b := by
  apply congrArg χ
  apply Subtype.ext
  change ⁅(c : FreeAmalgam R), (d : FreeAmalgam R)⁆ =
    ⁅(a : FreeAmalgam R), (b : FreeAmalgam R)⁆
  rw [ha, hb, ← conjugate_commutatorElement,
    hc (commutator_mem_commutator a.property b.property) _ ⟨m,rfl⟩,
    mul_inv_cancel_right]

private noncomputable def descendPairing {A B C : Type*} [Group A] [Group B] [Group C]
    (q : B →* C) (hq : Function.Surjective q) (b : A →* (B →* T))
    (hkill : ∀ a, q.ker ≤ (b a).ker) : A →* (C →* T) where
  toFun a := q.liftOfSurjective hq ⟨b a, hkill a⟩
  map_one' := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y,rfl⟩ := hq x
    simp only [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply,
      map_one, MonoidHom.one_apply]
  map_mul' a c := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y,rfl⟩ := hq x
    simp only [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply,
      map_mul, MonoidHom.mul_apply]

private theorem descendPairing_apply {A B C : Type*} [Group A] [Group B] [Group C]
    (q : B →* C) (hq : Function.Surjective q) (b : A →* (B →* T))
    (hkill : ∀ a, q.ker ≤ (b a).ker) (a : A) (x : B) :
    descendPairing q hq b hkill a (q x) = b a x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The actual central commutator, followed by a binary character, gives
the marked dual quotient. Both denominator commutators are literal. -/
private theorem dualSection_of_central_commutators [Finite M]
    {A N B D : Subgroup (FreeAmalgam R)}
    (hlocal : A ≤ stabilizer R (alpha R)) (hle : N ≤ A)
    (hA : Mbar R ≤ normalizer A) (hN : Mbar R ≤ normalizer N)
    (n : MarkedPairSection source common B D false)
    (hc : ⁅A,B⁆ ≤ centralizer (Mbar R : Set (FreeAmalgam R)))
    (χ : (⁅A,B⁆ : Subgroup (FreeAmalgam R)) →* T)
    (hAD : ⁅A,D⁆ = ⊥) (hNB : ⁅N,B⁆ = ⊥)
    (hne : ∃ (a : A) (b : B),
      χ ⟨⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆,
        commutator_mem_commutator a.property b.property⟩ ≠ 1)
    (hcard : N.relIndex A ≤ 8) :
    Nonempty (MarkedDualSection source common A N) := by
  have hAM : A ≤ Mbar R := by simpa only [alpha, stabilizer_m_base] using hlocal
  have hBM : B ≤ Mbar R := by simpa only [alpha, stabilizer_m_base] using n.local_group
  let b := centralCharacterPairing hAM hBM hc χ
  have hkill : ∀ a, n.quotient.ker ≤ (b a).ker := by
    intro a d hd
    rw [n.kernel] at hd
    have he : ⁅(a : FreeAmalgam R),(d : FreeAmalgam R)⁆ = 1 := by
      have hh := commutator_mem_commutator a.property hd
      rw [hAD] at hh
      exact hh
    change χ ⟨⁅(a : FreeAmalgam R),(d : FreeAmalgam R)⁆,_⟩ = 1
    exact (congrArg χ (Subtype.ext he)).trans χ.map_one
  let β := descendPairing n.quotient n.onto b hkill
  have hβ (a : A) (x : B) : β a (n.quotient x) = b a x :=
    descendPairing_apply _ _ _ _ _ _
  refine dualSection_of_pair_scalar_pairing hlocal hle hA hN β ?_ ?_ ?_ hcard
  · intro a ha
    apply MonoidHom.ext
    intro v
    obtain ⟨x,rfl⟩ := n.onto v
    rw [hβ]
    have he : ⁅(a : FreeAmalgam R),(x : FreeAmalgam R)⁆ = 1 := by
      have hh := commutator_mem_commutator ha x.property
      rw [hNB] at hh
      exact hh
    change χ ⟨⁅(a : FreeAmalgam R),(x : FreeAmalgam R)⁆,_⟩ = 1
    exact (congrArg χ (Subtype.ext he)).trans χ.map_one
  · intro m a c ha v
    obtain ⟨x,hx⟩ := n.onto (Multiplicative.ofAdd v)
    let y : B := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp n.normalized _ ⟨m,rfl⟩ _ x.property⟩
    have hy : n.quotient y = Multiplicative.ofAdd
        ((common.natural.marking (source.projection m)).val.mulVec v.1,
         (common.natural.marking (source.projection m)).val.mulVec v.2) := by
      apply Multiplicative.toAdd.injective
      simpa only [Bool.false_eq_true, reduceIte, hx, toAdd_ofAdd] using n.action m x y rfl
    rw [← hy, ← hx, hβ, hβ]
    exact centralCharacterPairing_conjugation hAM hBM hc χ m a c x y ha rfl
  · obtain ⟨a,x,hx⟩ := hne
    refine ⟨a,(n.quotient x).toAdd,?_⟩
    rw [ofAdd_toAdd, hβ]
    exact hx

/-- A nontrivial central commutator with a binary elementary subgroup
supplies the scalar character as well as the marked dual coordinates. -/
theorem dualSection_of_commutator_bounds [Finite M]
    {A N B D : Subgroup (FreeAmalgam R)}
    (hlocal : A ≤ stabilizer R (alpha R)) (hle : N ≤ A)
    (hA : Mbar R ≤ normalizer A) (hN : Mbar R ≤ normalizer N)
    (hE : IsElementaryAbelian 2 A)
    (n : MarkedPairSection source common B D false)
    (hc : ⁅A,B⁆ ≤ centralizer (Mbar R : Set (FreeAmalgam R)))
    (hAD : ⁅A,D⁆ = ⊥) (hNB : ⁅N,B⁆ = ⊥)
    (hne : ⁅A,B⁆ ≠ ⊥) (hcard : N.relIndex A ≤ 8) :
    Nonempty (MarkedDualSection source common A N) := by
  classical
  have hBM : B ≤ Mbar R := by simpa only [alpha, stabilizer_m_base] using n.local_group
  have hcommA : ⁅A,B⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp (hBM.trans hA)
  let C := (⁅A,B⁆ : Subgroup (FreeAmalgam R))
  let := hE
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hcommA
  obtain ⟨a, b, hab⟩ : ∃ (a : A) (b : B),
      ⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆ ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro a ha b hb
    exact h ⟨a,ha⟩ ⟨b,hb⟩
  let x : C := ⟨⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆,
    commutator_mem_commutator a.property b.property⟩
  have hx : Additive.ofMul x ≠ 0 := fun he => hab (congrArg Subtype.val he)
  obtain ⟨f,hf⟩ : ∃ f : Module.Dual F (Additive C), f (Additive.ofMul x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff F (Additive.ofMul x)).mp h)
  let χ : C →* T := f.toAddMonoidHom.toMultiplicativeRight
  apply dualSection_of_central_commutators hlocal hle hA hN n hc χ hAD hNB _ hcard
  refine ⟨a,b,fun he => hf ?_⟩
  exact congrArg Multiplicative.toAdd he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients
