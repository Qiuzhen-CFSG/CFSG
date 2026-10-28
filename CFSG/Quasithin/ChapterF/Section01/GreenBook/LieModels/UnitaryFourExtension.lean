module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointRadicalSpecial
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
/-!
# The actual projective unitary-four extension

The entrywise q-Frobenius involution of SU₄ descends along the injective
projective map. It is outer and constructs an extension of PSU₄ by C₂,
with exact degree two. Both marked flag stabilizers are extended using
this same action. Their whole overlap and compatible amalgam maps are
transported through one isomorphism. The local quotient action is literal
conjugation by the marked σ, identified with q-powering on SL₂(GF(q²)).

The requested intermediate identity in Aschbacher--Smith F.1.12, printed
p.264 (PDF page 275), is obstructed: U⟨σ⟩ is not normal in the whole
extended overlap. `twoCore_ne_extendedUpper` proves its failure for every
n ≥ 1; the n = 2 specialization lies within that paragraph's q > 2 range.
The Theory module identifies S ∩ L₁ with U and places the offending torus
in B₂ = N_{L₂}(U ∩ L₂), so the definition B = B₁B₂S on printed p.260
cannot remove it. A source correction must replace the core assertion,
or explicitly specify a different subgroup with its own justification.
This module does not claim F.1.12, classify all proper extensions, or
replace that identity by an assumed premise. The q = 2 obstruction is
kept separate from the source's restriction to q > 2 in this paragraph.

The word graph follows the source's GLS convention (Notation 16.1.3,
printed p.1171); the concrete automorphism here is entrywise q-Frobenius.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
variable (n : ℕ) (hn : 1 ≤ n)
local notation "F" => MatrixField n
local notation "σ" => fieldConj n
local notation "hσ" => fieldConj_involutive n hn

abbrev MatrixExtension := UnitaryFourOuter.Extension F σ hσ
abbrev matrixAut : MulAut (MatrixGroup n hn) := UnitaryFourOuter.matrixAut F σ hσ

def projectEquiv : MatrixGroup n hn ≃* ProjectiveGroup n hn :=
  MulEquiv.ofBijective (projection n hn)
    ⟨projection_injective n hn, project_surjective _ _⟩

def projectiveAut : MulAut (ProjectiveGroup n hn) :=
  ((projectEquiv n hn).symm.trans (matrixAut n hn)).trans (projectEquiv n hn)

theorem projectiveAut_project (a : MatrixGroup n hn) :
    projectiveAut n hn (projectEquiv n hn a) = projectEquiv n hn (matrixAut n hn a) := by
  change projectEquiv n hn (matrixAut n hn ((projectEquiv n hn).symm (projectEquiv n hn a))) = _
  rw [(projectEquiv n hn).symm_apply_apply]

theorem projectiveAut_sq : projectiveAut n hn ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a,rfl⟩ := (projectEquiv n hn).surjective x
  change projectiveAut n hn (projectiveAut n hn (projectEquiv n hn a)) = _
  rw [projectiveAut_project, projectiveAut_project]
  exact congrArg (projectEquiv n hn) (UnitaryFourOuter.matrixHom_involutive F σ hσ a)

theorem projectiveAut_ne_inner (g : ProjectiveGroup n hn) :
    projectiveAut n hn ≠ MulAut.conj g := by
  intro h
  have hnon : matrixAut n hn ≠ MulAut.conj ((projectEquiv n hn).symm g) :=
    UnitaryFourOuter.matrixAut_ne_inner F σ hσ (PointLocal.fieldConj_nontrivial n hn) _
  apply hnon
  apply MulEquiv.ext
  intro a
  apply (projectEquiv n hn).injective
  have ha := congrArg (fun f : MulAut (ProjectiveGroup n hn) => f (projectEquiv n hn a)) h
  rw [projectiveAut_project] at ha
  simpa only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] using ha

def projectiveAction : UnitaryFourOuter.C2 →* MulAut (ProjectiveGroup n hn) :=
  QuaternionGroup.cyclicPowerHom 2 (projectiveAut n hn) (projectiveAut_sq n hn)

theorem projectiveAction_generator : projectiveAction n hn UnitaryFourOuter.generator = projectiveAut n hn :=
  QuaternionGroup.cyclicPowerHom_one _ _ _

abbrev ProjectiveExtension := ProjectiveGroup n hn ⋊[projectiveAction n hn] UnitaryFourOuter.C2

def extensionProjection : MatrixExtension n hn →* ProjectiveExtension n hn :=
  SemidirectProduct.map (projectEquiv n hn).toMonoidHom (MonoidHom.id _) (by
    intro c
    apply MonoidHom.ext
    intro a
    change projectEquiv n hn (UnitaryFourOuter.action F σ hσ c a) =
      projectiveAction n hn c (projectEquiv n hn a)
    rcases UnitaryFourOuter.c2_cases c with hc | hc
    · simp [hc]
    · rw [hc, UnitaryFourOuter.action_generator, projectiveAction_generator]
      exact (projectiveAut_project n hn a).symm)

theorem extensionProjection_injective : Function.Injective (extensionProjection n hn) := by
  intro a b h
  exact SemidirectProduct.ext ((projectEquiv n hn).injective
    (congrArg SemidirectProduct.left h)) (congrArg (fun x : ProjectiveExtension n hn => x.right) h)

theorem extensionProjection_surjective : Function.Surjective (extensionProjection n hn) := by
  intro x
  refine ⟨⟨(projectEquiv n hn).symm x.left,x.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact (projectEquiv n hn).apply_symm_apply x.left
  · rfl

def extensionEquiv : MatrixExtension n hn ≃* ProjectiveExtension n hn :=
  MulEquiv.ofBijective (extensionProjection n hn)
    ⟨extensionProjection_injective n hn, extensionProjection_surjective n hn⟩

def sigma : ProjectiveExtension n hn := SemidirectProduct.inr UnitaryFourOuter.generator

theorem extensionProjection_sigma : extensionProjection n hn (UnitaryFourOuter.sigma F σ hσ) = sigma n hn :=
  SemidirectProduct.map_inr _ _ _ _

theorem sigma_sq : sigma n hn ^ 2 = 1 := by
  rw [← extensionProjection_sigma, ← map_pow, UnitaryFourOuter.sigma_sq, map_one]

theorem sigma_ne_one : sigma n hn ≠ 1 := by
  rw [← extensionProjection_sigma, ← map_one (extensionProjection n hn)]
  exact fun h => UnitaryFourOuter.sigma_ne_one F σ hσ (extensionProjection_injective n hn h)

def point : Subgroup (ProjectiveExtension n hn) :=
  (UnitaryFourOuter.point F σ hσ).map (extensionProjection n hn)
def plane : Subgroup (ProjectiveExtension n hn) :=
  (UnitaryFourOuter.plane F σ hσ).map (extensionProjection n hn)
def overlap : Subgroup (ProjectiveExtension n hn) :=
  (UnitaryFourOuter.overlap F σ hσ).map (extensionProjection n hn)
def extendedUpper : Subgroup (ProjectiveExtension n hn) :=
  (UnitaryFourOuter.extendedUpper F σ hσ).map (extensionProjection n hn)

theorem mem_point (x : ProjectiveExtension n hn) :
    x ∈ point n hn ↔ x.left ∈ pointParabolic n hn := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.left,ha,rfl⟩
  · rintro ⟨a,ha,he⟩
    refine ⟨⟨a,x.right⟩,ha,?_⟩
    exact SemidirectProduct.ext he rfl

theorem mem_plane (x : ProjectiveExtension n hn) :
    x ∈ plane n hn ↔ x.left ∈ planeParabolic n hn := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.left,ha,rfl⟩
  · rintro ⟨a,ha,he⟩
    refine ⟨⟨a,x.right⟩,ha,?_⟩
    exact SemidirectProduct.ext he rfl

theorem exact_overlap : point n hn ⊓ plane n hn = overlap n hn :=
  (Subgroup.map_inf _ _ (extensionProjection n hn) (extensionProjection_injective n hn)).symm

def matrixAmalgam : Theory.GroupTheory.RankTwoAmalgam
    (UnitaryFourOuter.point F σ hσ) (UnitaryFourOuter.overlap F σ hσ) (UnitaryFourOuter.plane F σ hσ) :=
  Theory.GroupTheory.RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

def amalgam : Theory.GroupTheory.RankTwoAmalgam (point n hn) (overlap n hn) (plane n hn) :=
  Theory.GroupTheory.RankTwoAmalgam.ofSubgroups _ _ _
    (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

def projectIso : Theory.GroupTheory.RankTwoAmalgam.Iso (matrixAmalgam n hn) (amalgam n hn) :=
  Theory.GroupTheory.RankTwoAmalgam.ofSubgroupsMapIso (extensionProjection n hn)
    (extensionProjection_injective n hn) _ _ _ inf_le_left inf_le_right

/-- The extended candidate is not even relatively normal in the full projective overlap. -/
theorem extendedUpper_not_normal :
    ¬ ((extendedUpper n hn).subgroupOf (overlap n hn)).Normal := by
  intro hN
  apply UnitaryFourOuter.extendedUpper_not_normal F σ hσ (PointLocal.fieldConj_nontrivial n hn)
  constructor
  intro a ha b
  let f := extensionProjection n hn
  let a' : overlap n hn := ⟨f a.val, ⟨a.val,a.property,rfl⟩⟩
  let b' : overlap n hn := ⟨f b.val, ⟨b.val,b.property,rfl⟩⟩
  have ha' : a' ∈ (extendedUpper n hn).subgroupOf (overlap n hn) :=
    ⟨a.val,ha,rfl⟩
  have hc := hN.conj_mem a' ha' b'
  obtain ⟨y,hy,he⟩ := hc
  change f y = f b.val * f a.val * (f b.val)⁻¹ at he
  have he' : f y = f (b.val * a.val * b.val⁻¹) := by
    simpa only [map_mul, map_inv] using he
  have hy' := extensionProjection_injective n hn he'
  change b.val * a.val * b.val⁻¹ ∈ UnitaryFourOuter.extendedUpper F σ hσ
  rw [← hy']
  exact hy

/-- The literal printed identity is false in the requested full-overlap model. -/
theorem twoCore_ne_extendedUpper : pCore 2 (overlap n hn) ≠
    (extendedUpper n hn).subgroupOf (overlap n hn) := by
  intro he
  apply extendedUpper_not_normal n hn
  rw [← he]
  infer_instance

/-- The smallest field retains the same obstruction. -/
theorem twoCore_ne_extendedUpper_two : pCore 2 (overlap 1 (by decide)) ≠
    (extendedUpper 1 (by decide)).subgroupOf (overlap 1 (by decide)) :=
  twoCore_ne_extendedUpper 1 (by decide)


/-- A concrete counterexample in the q > 2 range used on printed p.264. -/
theorem twoCore_ne_extendedUpper_four : pCore 2 (overlap 2 (by decide)) ≠
    (extendedUpper 2 (by decide)).subgroupOf (overlap 2 (by decide)) :=
  twoCore_ne_extendedUpper 2 (by decide)

instance matrixImage_normal :
    (SemidirectProduct.inl : ProjectiveGroup n hn →* ProjectiveExtension n hn).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The quotient above the actual projective matrix group is C₂. -/
def quotientEquivC2 : (ProjectiveExtension n hn ⧸
    (SemidirectProduct.inl : ProjectiveGroup n hn →* ProjectiveExtension n hn).range) ≃*
      UnitaryFourOuter.C2 :=
  (QuotientGroup.quotientMulEquivOfEq SemidirectProduct.range_inl_eq_ker_rightHom).trans
    (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
      SemidirectProduct.rightHom_surjective)

theorem extension_degree_two : Nat.card (ProjectiveExtension n hn ⧸
    (SemidirectProduct.inl : ProjectiveGroup n hn →* ProjectiveExtension n hn).range) = 2 := by
  rw [Nat.card_congr (quotientEquivC2 n hn).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : UnitaryFourOuter.C2 ≃ ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]

abbrev L2MatrixAut : MulAut (L2Matrix n hn) :=
  UnitaryFourOuter.planeLocalAut F σ hσ

/-- The automorphism of the actual projective plane factor. -/
def L2Aut : MulAut (L2 n hn) :=
  ((L2ProjectIso n hn).symm.trans
    (L2MatrixAut n hn)).trans (L2ProjectIso n hn)

theorem L2Aut_val (g : L2 n hn) : (L2Aut n hn g).val = projectiveAut n hn g.val := by
  obtain ⟨a,rfl⟩ := (L2ProjectIso n hn).surjective g
  change (L2ProjectIso n hn (L2MatrixAut n hn
    ((L2ProjectIso n hn).symm (L2ProjectIso n hn a)))).val = _
  rw [(L2ProjectIso n hn).symm_apply_apply]
  exact (projectiveAut_project n hn a.val).symm

/-- The local action is literal conjugation by the marked extension element. -/
theorem L2Aut_conjugation (g : L2 n hn) :
    (SemidirectProduct.inl (L2Aut n hn g).val : ProjectiveExtension n hn) =
      sigma n hn * SemidirectProduct.inl g.val * (sigma n hn)⁻¹ := by
  rw [L2Aut_val, ← projectiveAction_generator]
  simpa only [sigma, map_inv] using
    (SemidirectProduct.inl_aut (φ := projectiveAction n hn) UnitaryFourOuter.generator g.val)

def L2QuotientAut : MulAut (L2 n hn ⧸ pCore 2 (L2 n hn)) :=
  QuotientGroup.congr _ _ (L2Aut n hn) (pCore_map_iso 2 _)

/-- Use the literal matrix field, without changing its Galois-field index convention. -/
def L2QuotientEquivMatrixSL2 : (L2 n hn ⧸ pCore 2 (L2 n hn)) ≃*
    Matrix.SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq (L2Radical_eq_twoCore n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (L2Restriction n hn)
      (L2Restriction_surjective n hn))

/-- The field automorphism assertion of F.1.12 on the actual projective quotient. -/
theorem L2QuotientAut_field (x : L2 n hn ⧸ pCore 2 (L2 n hn)) :
    L2QuotientEquivMatrixSL2 n hn (L2QuotientAut n hn x) =
      Matrix.SpecialLinearGroup.map (fieldConj n).toRingHom
        (L2QuotientEquivMatrixSL2 n hn x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a,rfl⟩ := (L2ProjectIso n hn).surjective g
    change L2Restriction n hn (L2ProjectIso n hn (L2MatrixAut n hn
      ((L2ProjectIso n hn).symm (L2ProjectIso n hn a)))) =
      Matrix.SpecialLinearGroup.map (fieldConj n).toRingHom
        (L2Restriction n hn (L2ProjectIso n hn a))
    rw [(L2ProjectIso n hn).symm_apply_apply, L2Restriction_project, L2Restriction_project]
    exact UnitaryFourOuter.planeQuotientAut_field F σ hσ (QuotientGroup.mk a)

/-- The entrywise exponent is q, and the quotient field has order q². -/
theorem L2QuotientAut_entry (x : L2 n hn ⧸ pCore 2 (L2 n hn)) (i j : Fin 2) :
    (L2QuotientEquivMatrixSL2 n hn (L2QuotientAut n hn x)).val i j =
      (L2QuotientEquivMatrixSL2 n hn x).val i j ^ (2 ^ n) := by
  exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val i j)
    (L2QuotientAut_field n hn x)

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
