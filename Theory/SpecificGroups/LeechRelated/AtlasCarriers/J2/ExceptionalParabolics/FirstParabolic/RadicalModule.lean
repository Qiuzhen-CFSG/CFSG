module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.IntrinsicStructure
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The literal Hall--Janko radical as the projective A₅ augmentation module

Coordinates on the certified 32-element radical give a surjective homomorphism
onto the even-weight binary five-coordinate space. Generator transitions prove
multiplicativity; its zero fiber is exactly the marked central involution and
identity. Three centralizer-generator checks, extended by subgroup generation,
prove equivariance for the original five-block action `innerAction`.

The first isomorphism theorem identifies the literal radical quotient. Its
representation satisfies the conjugation formula on every quotient
representative, and the resulting equivalence over the binary A₅ group algebra
transfers the proved projectivity of the augmentation module.

Source: Aschbacher--Smith I.2.2(5), printed pp.411--412 / PDF pp.422--423.
The permutations are the retained ATLAS J2G1-p100B0 data, with the attribution
of `RadicalStructure`. The original Apache-2.0 discovery script in
`RadicalModule/source/discover.py` proposes the finite tables; every identity
used here is checked in Lean's kernel.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped BigOperators
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.RadicalModule
open GeneratorPair Seed RadicalStructureData QuotientActions
open GeneratorPair.SecondOrbitCertificate

def coordinates : Fin 32 → Fin 5 → ZMod 2 :=
  ![![0, 0, 0, 0, 0], ![0, 1, 1, 1, 1], ![1, 1, 1, 0, 1], ![1, 1, 1, 1, 0], ![1, 1, 0, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1], ![1, 0, 1, 1, 1], ![1, 0, 0, 1, 0], ![0, 0, 0, 1, 1], ![0, 0, 1, 0, 1], ![1, 0, 0, 0, 1], ![0, 0, 0, 1, 1], ![0, 0, 1, 1, 0], ![1, 0, 1, 1, 1], ![0, 0, 0, 0, 0], ![1, 1, 1, 0, 1], ![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 1, 1, 1, 0], ![0, 1, 1, 0, 0], ![0, 1, 0, 0, 1], ![1, 1, 0, 0, 0], ![0, 1, 1, 1, 1], ![0, 1, 0, 1, 0], ![1, 1, 0, 1, 1], ![0, 1, 0, 0, 1], ![1, 1, 0, 1, 1], ![0, 0, 1, 0, 1], ![1, 0, 1, 0, 0], ![0, 0, 1, 1, 0], ![1, 0, 1, 0, 0]]

def conjugateIndex : Fin 3 → Fin 32 → Fin 32 :=
  ![![0, 19, 25, 23, 21, 10, 11, 7, 28, 29, 5, 6, 31, 30, 14, 15, 27, 24, 20, 1, 18, 4, 26, 3, 17, 2, 22, 16, 8, 9, 13, 12], ![0, 3, 23, 14, 10, 6, 21, 27, 11, 4, 24, 26, 22, 5, 25, 15, 1, 13, 31, 7, 30, 17, 28, 19, 29, 16, 20, 2, 18, 9, 8, 12], ![0, 16, 27, 1, 9, 13, 5, 19, 30, 29, 4, 8, 31, 17, 3, 15, 25, 21, 28, 23, 26, 6, 12, 2, 10, 14, 11, 7, 22, 24, 20, 18]]

private theorem coordinates_mem : ∀ i, coordinates i ∈ BinaryPermutation.core (Fin 5) := by
  change ∀ i, ∑ j, coordinates i j = 0
  decide +kernel

def vector (i : Fin 32) : BinaryPermutation.core (Fin 5) :=
  ⟨coordinates i, by exact coordinates_mem i⟩

/-- Multiplication of enumeration indices, evaluated from the certified words. -/
def wordIndex : List (Fin 4) → Fin 32 → Fin 32
  | [], j => j
  | i :: w, j => step i (wordIndex w j)

set_option maxRecDepth 100000 in
private theorem step_check : ∀ j i,
    generatorTable j * RadicalStructureData.tablePerm i =
      RadicalStructureData.tablePerm (step j i) := by
  apply allFin
  decide +kernel

private theorem element_step (j : Fin 4) (i : Fin 32) :
    radicalGenerator j * radicalElement i = radicalElement (step j i) := by
  apply inclusion_injective
  rw [map_mul, radicalGenerator_inclusion, radicalElement_inclusion, radicalElement_inclusion]
  exact step_check j i

private theorem word_mul (w : List (Fin 4)) (j : Fin 32) :
    evalWord radicalGenerator w * radicalElement j = radicalElement (wordIndex w j) := by
  induction w with
  | nil => simp [evalWord, wordIndex]
  | cons i w ih =>
    rw [evalWord, mul_assoc, ih, element_step]
    rfl

private theorem vector_mul : ∀ i j,
    vector (wordIndex (word i) j) = vector i + vector j := by
  intro i j
  apply Subtype.ext
  exact (show ∀ i j, coordinates (wordIndex (word i) j) = coordinates i + coordinates j by
    decide +kernel) i j

/-- The enumeration in the literal intrinsic core. -/
def enum (i : Fin 32) : pCore 2 l₁ :=
  ⟨⟨radicalElement i, radical_le_l₁ (radicalElement_mem i)⟩, by
    rw [l₁_core_eq]
    exact radicalElement_mem i⟩

theorem enum_bijective : Function.Bijective enum := by
  constructor
  · intro i j h
    exact radicalElement_injective (congrArg (fun x : pCore 2 l₁ => x.val.val) h)
  · intro x
    have hx : x.val.val ∈ radical := by
      exact (le_of_eq l₁_core_eq) x.property
    obtain ⟨i, hi⟩ := exists_radicalElement hx
    exact ⟨i, Subtype.ext (Subtype.ext hi)⟩

private theorem enum_mul (i j : Fin 32) :
    enum i * enum j = enum (wordIndex (word i) j) :=
  Subtype.ext (Subtype.ext (word_mul (word i) j))

noncomputable def index : pCore 2 l₁ ≃ Fin 32 :=
  (Equiv.ofBijective enum enum_bijective).symm

@[simp] theorem index_enum (i : Fin 32) : index (enum i) = i :=
  (Equiv.ofBijective enum enum_bijective).symm_apply_apply i

/-- Coordinates of the literal radical in the five-coordinate augmentation kernel. -/
noncomputable def b : pCore 2 l₁ →* Multiplicative (BinaryPermutation.core (Fin 5)) where
  toFun x := Multiplicative.ofAdd (vector (index x))
  map_one' := by
    change vector (index (enum 0)) = 0
    rw [index_enum]
    apply Subtype.ext
    decide +kernel
  map_mul' x y := by
    obtain ⟨i, rfl⟩ := enum_bijective.surjective x
    obtain ⟨j, rfl⟩ := enum_bijective.surjective y
    change vector (index (enum i * enum j)) = vector (index (enum i)) + vector (index (enum j))
    rw [enum_mul, index_enum, index_enum, index_enum]
    exact vector_mul i j

@[simp] theorem b_enum (i : Fin 32) : (b (enum i)).toAdd = vector i := by
  change vector (index (enum i)) = vector i
  rw [index_enum]

theorem b_surjective : Function.Surjective b := by
  have hc : ∀ v : Fin 5 → ZMod 2, (∑ i, v i) = 0 → ∃ j, coordinates j = v := by
    decide +kernel
  intro v
  obtain ⟨i, hi⟩ := hc v.toAdd.val v.toAdd.property
  refine ⟨enum i, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [b_enum]
  exact Subtype.ext hi

/-- The marked involution, as an element of its literal centralizer. -/
def marked : l₁ := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

private theorem enum_fifteen : (enum 15).val = marked := by
  apply Subtype.ext
  apply inclusion_injective
  rw [show (enum 15).val.val = radicalElement 15 from rfl, radicalElement_inclusion]
  change RadicalStructureData.tablePerm 15 = inclusion z
  rw [show inclusion z = FirstFusion.tPerm from FirstFusion.inclusion_t]
  decide +kernel

theorem b_ker : b.ker = (zpowers marked).subgroupOf (pCore 2 l₁) := by
  have hz : ∀ i, coordinates i = 0 ↔ i = 0 ∨ i = 15 := by decide +kernel
  apply le_antisymm
  · intro x hx
    obtain ⟨i, rfl⟩ := enum_bijective.surjective x
    have hi : coordinates i = 0 := congrArg Subtype.val (b_enum i |>.symm.trans hx)
    rcases (hz i).mp hi with rfl | rfl
    · exact one_mem _
    · change (enum 15).val ∈ zpowers marked
      rw [enum_fifteen]
      exact mem_zpowers _
  · have hkill : b (enum 15) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [b_enum]
      apply Subtype.ext
      decide +kernel
    intro x hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    have he : x = enum 15 ^ n := by
      apply Subtype.ext
      change x.val = (enum 15).val ^ n
      rw [enum_fifteen]
      exact hn.symm
    rw [he, MonoidHom.mem_ker, map_zpow, hkill, one_zpow]

private def letter (s : Fin 3) : l₁ :=
  ⟨FirstFusion.centralizerLetter s, FirstFusion.centralizerLetter_mem s⟩

private theorem action_letter (s : Fin 3) : innerAction (letter s) = evenLetter s := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have h := innerAction_spec (letter s) (basePoint i)
  have h' := letter_color_check s (basePoint i)
  change color (inclusion (FirstFusion.centralizerLetter s) (basePoint i)) = _ at h
  rw [← FirstFusion.LocalCertificate.localLetterValue_eq] at h
  change (innerAction (letter s)).val i = letterPerm s i
  simpa only [color_basePoint, Option.map_some, Option.some.injEq] using h.symm.trans h'

set_option maxRecDepth 100000 in
private theorem conjugation_check : ∀ s i x,
    FirstFusion.LocalCertificate.localLetterValue s (RadicalStructureData.tablePerm i x) =
      RadicalStructureData.tablePerm (conjugateIndex s i)
        (FirstFusion.LocalCertificate.localLetterValue s x) := by
  apply allFin
  decide +kernel

private theorem conj_enum (s : Fin 3) (i : Fin 32) :
    MulAut.conjNormal (letter s) (enum i) = enum (conjugateIndex s i) := by
  apply Subtype.ext
  apply Subtype.ext
  change FirstFusion.centralizerLetter s * radicalElement i *
    (FirstFusion.centralizerLetter s)⁻¹ = radicalElement (conjugateIndex s i)
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply inclusion_injective
  simp only [map_mul, radicalElement_inclusion]
  apply Equiv.ext
  intro x
  simpa only [Equiv.Perm.mul_apply, ← FirstFusion.LocalCertificate.localLetterValue_eq]
    using conjugation_check s i x

private theorem vector_conj : ∀ s i,
    vector (conjugateIndex s i) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) (evenLetter s) (vector i) := by
  intro s i
  apply Subtype.ext
  exact (show ∀ s i, coordinates (conjugateIndex s i) =
    fun j => coordinates i ((letterPerm s).symm j) by decide +kernel) s i

/-- Pointwise equivariance for every element of the literal centralizer. -/
theorem b_equivariant (h : l₁) (x : pCore 2 l₁) :
    (b (MulAut.conjNormal h x)).toAdd =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) (innerAction h) (b x).toAdd := by
  let ρ := (BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp innerAction
  let good : Subgroup l₁ := {
    carrier := {g | ∀ x : pCore 2 l₁, (b (MulAut.conjNormal g x)).toAdd = ρ g (b x).toAdd}
    one_mem' := by intro x; simp
    mul_mem' := by
      intro g k hg hk x
      change (b ((MulAut.conjNormal (g * k)) x)).toAdd = _
      rw [map_mul, MulAut.mul_apply, hg, hk, map_mul, Module.End.mul_apply]
    inv_mem' := by
      intro g hg x
      have he := hg (MulAut.conjNormal g⁻¹ x)
      have hc : MulAut.conjNormal g (MulAut.conjNormal g⁻¹ x) = x := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [hc] at he
      exact ((Representation.inv_apply_eq_iff ρ).mpr he).symm }
  have hle : l₁ ≤ good.map l₁.subtype := by
    change FirstFusion.centralizer ≤ _
    rw [FirstFusion.LocalCertificate.centralizer_eq_closure_letters]
    apply (closure_le _).mpr
    rintro _ ⟨s, rfl⟩
    refine ⟨letter s, ?_, rfl⟩
    intro x
    obtain ⟨i, rfl⟩ := enum_bijective.surjective x
    change (b (MulAut.conjNormal (letter s) (enum i))).toAdd =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5)
        (innerAction (letter s)) (b (enum i)).toAdd
    rw [conj_enum, b_enum, b_enum, action_letter]
    exact vector_conj s i
  obtain ⟨g, hg, he⟩ := hle h.property
  have he' : g = h := Subtype.ext he
  exact he' ▸ hg x

instance quotientKernel_normal : ((zpowers marked).subgroupOf (pCore 2 l₁)).Normal := by
  rw [← b_ker]
  infer_instance

/-- The first isomorphism theorem with the literal marked central subgroup. -/
noncomputable def quotientEquiv :
    ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁)) ≃*
      Multiplicative (BinaryPermutation.core (Fin 5)) :=
  (QuotientGroup.quotientMulEquivOfEq b_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective b b_surjective)

@[simp] theorem quotientEquiv_mk (x : pCore 2 l₁) :
    quotientEquiv (QuotientGroup.mk' ((zpowers marked).subgroupOf (pCore 2 l₁)) x) = b x := rfl

instance quotient_elementary : IsElementaryAbelian 2
    ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁)) where
  is_comm := ⟨fun x y => quotientEquiv.injective (by
    rw [map_mul, map_mul, mul_comm])⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply quotientEquiv.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (quotientEquiv x).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul])

open scoped IsMulCommutative

/-- Additive coordinates on the literal quotient, before extending scalars. -/
noncomputable def quotientAddEquiv :
    Additive ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁)) ≃+
      BinaryPermutation.core (Fin 5) where
  toFun x := (quotientEquiv x.toMul).toAdd
  invFun v := Additive.ofMul (quotientEquiv.symm (Multiplicative.ofAdd v))
  left_inv x := quotientEquiv.left_inv x.toMul
  right_inv v := quotientEquiv.right_inv (Multiplicative.ofAdd v)
  map_add' x y := quotientEquiv.map_mul x.toMul y.toMul

/-- Linear coordinates on the literal radical modulo the marked involution. -/
noncomputable def linearEquiv :
    Additive ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁)) ≃ₗ[ZMod 2]
      BinaryPermutation.core (Fin 5) :=
  { quotientAddEquiv with map_smul' := ZMod.map_smul quotientAddEquiv }

/-- The actual conjugation module, expressed through the checked five-block A₅
quotient. The formula `representation_conjugation` certifies the action. -/
noncomputable def representation : Representation (ZMod 2) (alternatingGroup (Fin 5))
    (Additive ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁))) where
  toFun g := linearEquiv.symm.toLinearMap ∘ₗ
    BinaryPermutation.alternatingCoreRepresentation (Fin 5) g ∘ₗ linearEquiv.toLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by
    ext v
    simp [map_mul, Module.End.mul_apply]

@[simp] theorem linearEquiv_representation (g : alternatingGroup (Fin 5))
    (v : Additive ((pCore 2 l₁) ⧸ (zpowers marked).subgroupOf (pCore 2 l₁))) :
    linearEquiv (representation g v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) g (linearEquiv v) := by
  exact linearEquiv.apply_symm_apply _

/-- The represented action is literal conjugation on every quotient representative. -/
theorem representation_conjugation (h : l₁) (x : pCore 2 l₁) :
    representation (innerAction h)
      (Additive.ofMul (QuotientGroup.mk' ((zpowers marked).subgroupOf (pCore 2 l₁)) x)) =
    Additive.ofMul (QuotientGroup.mk' ((zpowers marked).subgroupOf (pCore 2 l₁))
      (MulAut.conjNormal h x)) := by
  apply linearEquiv.injective
  rw [linearEquiv_representation]
  exact (b_equivariant h x).symm

/-- Identification as modules over the group algebra, including the action. -/
noncomputable def moduleEquiv : representation.asModule ≃ₗ[
    MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5))]
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)).asModule := by
  let f : representation.IntertwiningMap
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) := {
    toLinearMap := linearEquiv.toLinearMap
    isIntertwining' := fun g => LinearMap.ext (linearEquiv_representation g) }
  exact LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f) linearEquiv.bijective

/-- The literal radical quotient is projective for the actual A₅ action.
This is the projectivity used on printed p.412 of Aschbacher--Smith. -/
theorem representation_projective :
    Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      representation.asModule := by
  let := BinaryPermutation.alternatingFive_core_projective
  exact Module.Projective.of_equiv moduleEquiv.symm

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.RadicalModule
