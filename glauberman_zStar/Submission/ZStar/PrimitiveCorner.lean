import Submission.ZStar.BlockPrimitivity
import Submission.ZStar.AugmentationScratch
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Data.Finsupp.Fintype
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite primitive corners are local

A centrally primitive idempotent cuts out a commutative corner in the center
with no nontrivial idempotents.  Over a finite ring this corner is Artinian,
and the idempotent separators of distinct maximal ideals therefore show that
the corner is local.  Consequently every augmentation-zero element of a
primitive principal corner is nilpotent.

This is the ring-theoretic input used in the principal special case of the
Brauer-correspondence argument: a transferred nonprincipal local factor has
augmentation zero, hence cannot survive as a nonzero idempotent modulo a ring
homomorphism.
-/

noncomputable section

namespace Submission.ZStar
namespace PrimitiveCorner

universe u v

/-- A finite nontrivial commutative ring with only trivial idempotents is
local. -/
theorem isLocalRing_of_finite_of_isIdempotentElem_eq_zero_or_one
    (A : Type u) [CommRing A] [Finite A] [Nontrivial A]
    (hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1) :
    IsLocalRing A := by
  letI : IsArtinianRing A := isArtinian_of_finite
  by_contra hlocal
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    (IsLocalRing.not_isLocalRing_tfae.out 0 2).mp hlocal
  letI : p.IsPrime := hp.isPrime
  obtain ⟨r, hrp, hridem, hrq⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne p
  rcases hidem r hridem with rfl | rfl
  · exact hrp p.zero_mem
  · have hone : (1 : A) ∈ q := hrq q hq.isPrime hpq.symm
    exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr hone)

/-- In a finite local commutative ring, the nonunits are exactly the
nilpotent elements. -/
theorem isNilpotent_iff_not_isUnit_of_finite_local
    (A : Type u) [CommRing A] [Finite A] [Nontrivial A] [IsLocalRing A]
    (x : A) :
    IsNilpotent x ↔ ¬ IsUnit x := by
  letI : IsArtinianRing A := isArtinian_of_finite
  have hbase : Ring.KrullDimLE 0 A ∧ IsLocalRing A :=
    ⟨inferInstance, inferInstance⟩
  have hall : ∀ y : A, IsNilpotent y ↔ ¬ IsUnit y :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 0 2).mp
      hbase
  exact hall x

/-- The central corner cut out by a centrally primitive idempotent in a
finite ring is local. -/
theorem centrallyPrimitive_centerCorner_isLocalRing
    {A : Type u} [Ring A] [Finite A]
    (e : A) (he : BlockPrimitivity.IsCentrallyPrimitive e) :
    let Z := Subring.center A
    let eZ : Z := ⟨e, he.1⟩
    let heZ : IsIdempotentElem eZ := by
      exact Subtype.ext he.2.1.eq
    IsLocalRing heZ.Corner := by
  let Z := Subring.center A
  let eZ : Z := ⟨e, he.1⟩
  have heZ : IsIdempotentElem eZ := by
    exact Subtype.ext he.2.1.eq
  let C := heZ.Corner
  letI : Finite Z :=
    Finite.of_injective (fun z : Z => (z : A)) Subtype.val_injective
  letI : Finite C :=
    Finite.of_injective (fun x : C => ((x.1 : Z) : A)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  have hne : (1 : C) ≠ 0 := by
    intro h
    apply he.2.2.1
    have h' := congrArg (fun x : C => ((x.1 : Z) : A)) h
    change e = 0 at h'
    exact h'
  letI : Nontrivial C := ⟨⟨1, 0, hne⟩⟩
  apply isLocalRing_of_finite_of_isIdempotentElem_eq_zero_or_one C
  intro x hx
  by_cases hxzero : ((x.1 : Z) : A) = 0
  · left
    apply Subtype.ext
    apply Subtype.ext
    exact hxzero
  · right
    have hxidem : IsIdempotentElem ((x.1 : Z) : A) := by
      exact congrArg (fun y : C => ((y.1 : Z) : A)) hx
    have hxcorner := (Subsemigroup.mem_corner_iff heZ).mp x.property
    have hxfactor : ((x.1 : Z) : A) * e = ((x.1 : Z) : A) := by
      exact congrArg (fun y : Z => (y : A)) hxcorner.2
    have hxe : ((x.1 : Z) : A) = e :=
      he.2.2.2 ((x.1 : Z) : A) x.1.property hxidem hxfactor hxzero
    apply Subtype.ext
    apply Subtype.ext
    exact hxe

/-- In a finite ring, an element in a centrally primitive corner that is
killed by a unital map to a nontrivial commutative ring is nilpotent. -/
theorem isNilpotent_of_centrallyPrimitive_of_map_eq_zero
    {A : Type u} [Ring A] [Finite A]
    {K : Type v} [CommRing K] [Nontrivial K]
    (eps : A →+* K) (e a : A)
    (he : BlockPrimitivity.IsCentrallyPrimitive e)
    (haCenter : a ∈ Set.center A)
    (hfactor : a * e = a)
    (hepsE : eps e = 1)
    (hepsA : eps a = 0) :
    IsNilpotent a := by
  let Z := Subring.center A
  let eZ : Z := ⟨e, he.1⟩
  have heZ : IsIdempotentElem eZ := by
    exact Subtype.ext he.2.1.eq
  let C := heZ.Corner
  letI : Finite Z :=
    Finite.of_injective (fun z : Z => (z : A)) Subtype.val_injective
  letI : Finite C :=
    Finite.of_injective (fun x : C => ((x.1 : Z) : A)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  have hne : (1 : C) ≠ 0 := by
    intro h
    apply he.2.2.1
    have h' := congrArg (fun x : C => ((x.1 : Z) : A)) h
    change e = 0 at h'
    exact h'
  letI : Nontrivial C := ⟨⟨1, 0, hne⟩⟩
  letI : IsLocalRing C :=
    centrallyPrimitive_centerCorner_isLocalRing e he
  let aZ : Z := ⟨a, haCenter⟩
  have hea : e * a = a := by
    exact (Semigroup.mem_center_iff.mp he.1 a).symm.trans hfactor
  have haCorner : aZ ∈ Subsemigroup.corner eZ := by
    exact (Subsemigroup.mem_corner_iff heZ).2
      ⟨Subtype.ext hea, Subtype.ext hfactor⟩
  let aC : C := ⟨aZ, haCorner⟩
  let epsC : C →+* K :=
    { toFun := fun x => eps ((x.1 : Z) : A)
      map_one' := by
        change eps e = 1
        exact hepsE
      map_mul' := by
        intro x y
        exact map_mul eps ((x.1 : Z) : A) ((y.1 : Z) : A)
      map_zero' := map_zero eps
      map_add' := by
        intro x y
        exact map_add eps ((x.1 : Z) : A) ((y.1 : Z) : A) }
  have haCnonunit : ¬ IsUnit aC := by
    intro haUnit
    have hmapUnit : IsUnit (epsC aC) := haUnit.map epsC
    have hzero : epsC aC = 0 := by
      simpa [epsC, aC, aZ] using hepsA
    rw [hzero] at hmapUnit
    exact not_isUnit_zero hmapUnit
  have hnilC : IsNilpotent aC :=
    (isNilpotent_iff_not_isUnit_of_finite_local C aC).2 haCnonunit
  rcases hnilC with ⟨n, hn⟩
  rcases n with _ | n
  · simp at hn
  refine ⟨n + 1, ?_⟩
  have hcoe_pow_succ : ∀ m : ℕ,
      ((((aC ^ Nat.succ m).1 : Z) : A)) = a ^ Nat.succ m := by
    intro m
    induction m with
    | zero =>
        simp only [pow_one]
        rfl
    | succ m ih =>
        calc
          ((((aC ^ Nat.succ (Nat.succ m)).1 : Z) : A)) =
              ((((aC ^ Nat.succ m * aC).1 : Z) : A)) := by rw [pow_succ]
          _ = ((((aC ^ Nat.succ m).1 : Z) : A)) * a := rfl
          _ = a ^ Nat.succ m * a := by rw [ih]
          _ = a ^ Nat.succ (Nat.succ m) := by
            simp only [pow_succ]
  calc
    a ^ (n + 1) = ((((aC ^ (n + 1)).1 : Z) : A)) :=
      (hcoe_pow_succ n).symm
    _ = (((0 : C).1 : Z) : A) :=
      congrArg (fun x : C => ((x.1 : Z) : A)) hn
    _ = 0 := rfl

attribute [local instance] Fintype.ofFinite

private theorem principalResidueField_finite
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) := by
  have hprime_ne_bot : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver
      d.primeIdeal d.primeIdeal_liesOverTwo
    have hzero : (2 : Representation.cyclotomicOrder d.eta) = 0 := by
      simpa [hbot] using htwo
    exact two_ne_zero hzero
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime_ne_bot

/-- Every augmentation-zero central element in the reduced principal-block
corner is nilpotent. -/
theorem reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0) :
    IsNilpotent a := by
  letI : Finite (BrauerBlockReduction.principalResidueField d) :=
    principalResidueField_finite d
  letI : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  letI : Fintype (BrauerBlockReduction.principalResidueField d) :=
    Fintype.ofFinite (BrauerBlockReduction.principalResidueField d)
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  letI : Finite
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) := by
    change Finite
      (G →₀ BrauerBlockReduction.principalResidueField d)
    infer_instance
  exact isNilpotent_of_centrallyPrimitive_of_map_eq_zero
    (AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) G)
    (BrauerBlockReduction.reducedPrincipalBlockElement d) a
    (BlockPrimitivity.reducedPrincipalBlockElement_isCentrallyPrimitive d)
    haCenter hfactor
    (AugmentationScratch.reducedPrincipalBlockElement_augmentation_eq_one d)
    haug

/-- An augmentation-zero witness in the ambient principal corner cannot have
Brauer restriction acting as the identity on a nonzero local factor.

This is the exact ring-theoretic endpoint needed by a relative-transfer
argument.  Once a central transfer witness `a` satisfies
`Br_z(a) * f = f`, primitive-corner nilpotence makes `Br_z(a)` nilpotent,
and hence forces `f = 0`. -/
theorem eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z a * f = f) :
    f = 0 := by
  have hnilA : IsNilpotent a :=
    reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
      d a haCenter hfactor haug
  let aZ : Subring.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    ⟨a, haCenter⟩
  have hnilZ : IsNilpotent aZ := by
    rcases hnilA with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  let br := BrauerMapScratch.centralizerRestrictionCenterHom
    (BrauerBlockReduction.principalResidueField d) z hz
  have hnilBr : IsNilpotent (br aZ) := hnilZ.map br
  let x : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) := br aZ
  have hxmul : x * f = f := by
    simpa [x, br, aZ] using hrestrict
  have hxpow : ∀ n : ℕ, x ^ n * f = f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_assoc, hxmul, ih]
  rcases hnilBr with ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    exact congrArg
      (fun y : Subring.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G))) =>
          (y : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)))) hn
  calc
    f = x ^ n * f := (hxpow n).symm
    _ = 0 := by rw [hxn, zero_mul]

/-- Principal Brauer equality follows from a single augmentation-zero
relative-transfer witness for the extra local factor. -/
theorem involutionPrincipalBrauerEquality_of_transferWitness
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : AugmentationScratch.augmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      BrauerMapScratch.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z a *
          (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.centralizer ({z} : Set G))) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G))) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  have hzero :
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) = 0 :=
    eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
      d z hz a
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)))
      haCenter hfactor haug hrestrict
  change
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  exact (sub_eq_zero.mp hzero).symm

end PrimitiveCorner
end Submission.ZStar
