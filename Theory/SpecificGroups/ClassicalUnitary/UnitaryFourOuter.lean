module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Torus
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Structure
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.SpecificGroups.Quaternion.PresentationHom
/-!
# The involutory unitary-four extension and its Borel obstruction

Entrywise Hermitian conjugation preserves SU₄ and both coordinate flag
stabilizers. It gives an involution and a semidirect product by C₂. Its action
on the actual plane-factor two-core quotient is the field automorphism of SL₂.
It is outer: an inner implementer would normalize the upper-unitriangular
Sylow group, lie in the Borel, and act trivially on the diagonal quotient.

There is a source obstruction to Aschbacher--Smith F.1.12, printed p.264:
for the full extended flag overlap the subgroup U⟨σ⟩ is not normal, hence
cannot equal O₂(B). The diagonal d = diag(a,a⁻¹,σ(a),σ(a)⁻¹) belongs even
to B₂ = N_{L₂}(U ∩ L₂), and dσd⁻¹ has first diagonal entry a/σ(a).
Thus the obstruction also survives the source definition B = B₁B₂S from
F.1.3. This does not refute the classification alternatives of F.1.12;
it prevents using that printed intermediate core identity for this model.
The caller must supply a corrected source argument. No replacement core
identity is assumed here. The calculation includes the matrix field GF(4).
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
variable (F : Type*) [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "G" => SU F J
private theorem map_gram : (gram F).map σ = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram]
private theorem map_conjTranspose (A : Matrix (Fin 4) (Fin 4) F) :
    ((J).conjTranspose A).map σ = (J).conjTranspose (A.map σ) := by rfl

def matrixHom : G →* G where
  toFun a := ⟨GeneralLinearGroup.map σ.toRingHom a.val, by
    constructor
    · have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A.map σ) a.property.1
      change (((J).conjTranspose a.val.val * gram F * a.val.val).map σ) = (gram F).map σ at h
      rw [Matrix.map_mul, Matrix.map_mul, map_gram, map_conjTranspose] at h
      exact h
    · change GeneralLinearGroup.det (GeneralLinearGroup.map σ.toRingHom a.val) = 1
      rw [GeneralLinearGroup.map_det, a.property.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem matrixHom_apply (a : G) (i j : Fin 4) :
    (matrixHom F σ hσ a).val.val i j = σ (a.val.val i j) := rfl

theorem matrixHom_involutive : Function.Involutive (matrixHom F σ hσ) := by
  intro a
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact hσ _

def matrixAut : MulAut G := MulEquiv.ofBijective (matrixHom F σ hσ)
  (matrixHom_involutive F σ hσ).bijective

theorem matrixAut_apply (a : G) (i j : Fin 4) :
    (matrixAut F σ hσ a).val.val i j = σ (a.val.val i j) := rfl

theorem matrixAut_sq : matrixAut F σ hσ ^ 2 = 1 := by
  apply MulEquiv.ext
  intro a
  exact matrixHom_involutive F σ hσ a

open UnitaryFourSylow
abbrev C2 := Multiplicative (ZMod 2)
def generator : C2 := Multiplicative.ofAdd 1
theorem c2_cases (c : C2) : c = 1 ∨ c = generator := by
  have h : c.toAdd = 0 ∨ c.toAdd = 1 := by
    generalize c.toAdd = x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact h

def action : C2 →* MulAut G :=
  QuaternionGroup.cyclicPowerHom 2 (matrixAut F σ hσ) (matrixAut_sq F σ hσ)

theorem action_generator : action F σ hσ generator = matrixAut F σ hσ :=
  QuaternionGroup.cyclicPowerHom_one _ _ _

abbrev Extension := G ⋊[action F σ hσ] C2

def sigma : Extension F σ hσ := SemidirectProduct.inr generator

theorem sigma_sq : sigma F σ hσ ^ 2 = 1 := by
  rw [sigma, ← map_pow]
  have h : generator ^ 2 = 1 := by decide
  rw [h, map_one]

theorem sigma_ne_one : sigma F σ hσ ≠ 1 := by
  intro h
  have := congrArg SemidirectProduct.right h
  exact (by decide : generator ≠ 1) this

variable [Finite F]

theorem matrixAut_mem_point (a : G) :
    matrixAut F σ hσ a ∈ pointParabolicSU F J ↔ a ∈ pointParabolicSU F J := by
  simp [mem_pointParabolicSU, matrixAut_apply]

theorem matrixAut_mem_plane (a : G) :
    matrixAut F σ hσ a ∈ planeParabolicSU F J ↔ a ∈ planeParabolicSU F J := by
  simp [mem_planeParabolicSU, matrixAut_apply]

/-- Extend any invariant matrix subgroup by the marked involution. -/
def extendSubgroup (H : Subgroup G)
    (hH : ∀ a, matrixAut F σ hσ a ∈ H ↔ a ∈ H) : Subgroup (Extension F σ hσ) where
  carrier := {g | g.left ∈ H}
  one_mem' := H.one_mem
  mul_mem' := by
    intro a b ha hb
    change a.left * action F σ hσ a.right b.left ∈ H
    apply H.mul_mem ha
    rcases c2_cases a.right with hr | hr
    · simpa [hr] using hb
    · simpa [hr, action_generator, hH] using hb
  inv_mem' := by
    intro a ha
    change action F σ hσ a.right⁻¹ a.left⁻¹ ∈ H
    rcases c2_cases a.right⁻¹ with hr | hr
    · simpa [hr] using H.inv_mem ha
    · simpa [hr, action_generator, hH] using H.inv_mem ha

def point : Subgroup (Extension F σ hσ) :=
  extendSubgroup F σ hσ (pointParabolicSU F J) (matrixAut_mem_point F σ hσ)
def plane : Subgroup (Extension F σ hσ) :=
  extendSubgroup F σ hσ (planeParabolicSU F J) (matrixAut_mem_plane F σ hσ)
def overlap : Subgroup (Extension F σ hσ) := point F σ hσ ⊓ plane F σ hσ

theorem mem_overlap (g : Extension F σ hσ) :
    g ∈ overlap F σ hσ ↔ g.left ∈ borelSU F J := Iff.rfl

theorem sigma_mem_overlap : sigma F σ hσ ∈ overlap F σ hσ := by
  exact (borelSU F J).one_mem

variable [CharP F 2]
omit [Finite F] in
theorem matrixAut_mem_upper (a : G) :
    matrixAut F σ hσ a ∈ upper F σ hσ ↔ a ∈ upper F σ hσ := by
  simp [mem_upper_iff_entries, matrixAut_apply]

/-- The candidate S₁⟨σ⟩ in the ambient extension. -/
def extendedUpper : Subgroup (Extension F σ hσ) :=
  extendSubgroup F σ hσ (upper F σ hσ) (matrixAut_mem_upper F σ hσ)

omit [Finite F] [CharP F 2] in
private theorem conjugate_sigma_left (a : G) :
    (SemidirectProduct.inl a * sigma F σ hσ * (SemidirectProduct.inl a)⁻¹).left =
      a * matrixAut F σ hσ a⁻¹ := by
  simp [sigma, action_generator]

/-- Conjugating σ by the literal diagonal torus leaves the candidate S₁⟨σ⟩. -/
theorem torus_conjugate_sigma_not_mem (a : Fˣ) (ha : σ (a : F) ≠ a) :
    let d := (torusLift F σ hσ a 1).val
    SemidirectProduct.inl d * sigma F σ hσ * (SemidirectProduct.inl d)⁻¹ ∉
      extendedUpper F σ hσ := by
  intro d h
  change (SemidirectProduct.inl d * sigma F σ hσ *
    (SemidirectProduct.inl d)⁻¹).left ∈ upper F σ hσ at h
  rw [conjugate_sigma_left] at h
  have he := ((mem_upper_iff_entries F σ hσ _).mp h).2 0
  have hb : d ∈ borelSU F J := (torusLift F σ hσ a 1).property
  let b : borelSU F J := ⟨d, hb⟩
  let b' : borelSU F J := ⟨matrixAut F σ hσ d⁻¹, by
    exact ⟨(matrixAut_mem_point F σ hσ _).mpr ((borelSU F J).inv_mem hb).1,
      (matrixAut_mem_plane F σ hσ _).mpr ((borelSU F J).inv_mem hb).2⟩⟩
  have hm := congrArg (fun x : Fˣ × (FixedField F σ)ˣ => (x.1 : F))
    (map_mul (torusCharacter F σ hσ) b b')
  simp only [Prod.fst_mul, Units.val_mul, torusCharacter_fst_val] at hm
  change (d * matrixAut F σ hσ d⁻¹).val.val 0 0 =
    d.val.val 0 0 * σ (d⁻¹.val.val 0 0) at hm
  have hi := congrArg (fun x : Fˣ × (FixedField F σ)ˣ => (x.1 : F))
    (map_inv (torusCharacter F σ hσ) b)
  simp only [Prod.fst_inv, Units.val_inv_eq_inv_val, torusCharacter_fst_val] at hi
  change d⁻¹.val.val 0 0 = (d.val.val 0 0)⁻¹ at hi
  have hd : d.val.val 0 0 = (a : F) := by
    rw [← torusCharacter_fst_val F σ hσ (torusLift F σ hσ a 1), torusCharacter_lift]
  rw [hm, hi, hd, map_inv₀] at he
  exact ha ((mul_inv_eq_one₀ (by simp : σ (a : F) ≠ 0)).mp he).symm

/-- The proposed subgroup is not normal even relative to the whole extended overlap. -/
theorem extendedUpper_not_normal (hne : ∃ x : F, σ x ≠ x) :
    ¬ ((extendedUpper F σ hσ).subgroupOf (overlap F σ hσ)).Normal := by
  obtain ⟨x, hx⟩ := hne
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let a := Units.mk0 x hx0
  let d : overlap F σ hσ := ⟨SemidirectProduct.inl (torusLift F σ hσ a 1).val,
    (torusLift F σ hσ a 1).property⟩
  let s : overlap F σ hσ := ⟨sigma F σ hσ, sigma_mem_overlap F σ hσ⟩
  intro hN
  have hs : s ∈ (extendedUpper F σ hσ).subgroupOf (overlap F σ hσ) :=
    (upper F σ hσ).one_mem
  have hc := hN.conj_mem s hs d
  exact torus_conjugate_sigma_not_mem F σ hσ a hx hc


/-- Consequently the printed candidate cannot be the two-core of the full overlap. -/
theorem twoCore_ne_extendedUpper (hne : ∃ x : F, σ x ≠ x) :
    pCore 2 (overlap F σ hσ) ≠
      (extendedUpper F σ hσ).subgroupOf (overlap F σ hσ) := by
  intro he
  apply extendedUpper_not_normal F σ hσ hne
  rw [← he]
  infer_instance

/-- The field involution is outer: an inner implementer would normalize U,
lie in B, and therefore act trivially on the abelian diagonal quotient. -/
theorem matrixAut_ne_inner (hne : ∃ x : F, σ x ≠ x) (g : G) :
    matrixAut F σ hσ ≠ MulAut.conj g := by
  intro he
  have hg : g ∈ Subgroup.normalizer (upper F σ hσ : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro a
    have hm := matrixAut_mem_upper F σ hσ a
    rw [he] at hm
    exact hm.symm
  rw [normalizer_upper] at hg
  obtain ⟨x,hx⟩ := hne
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let a := Units.mk0 x hx0
  let d := torusLift F σ hσ a 1
  let b : borelSU F J := ⟨g,hg⟩
  have hm := congrArg (fun t : Fˣ × (FixedField F σ)ˣ => (t.1 : F))
    (show torusCharacter F σ hσ (b * d * b⁻¹) = torusCharacter F σ hσ d by
      simp)
  simp only [torusCharacter_fst_val] at hm
  change (g * d.val * g⁻¹).val.val 0 0 = d.val.val.val 0 0 at hm
  have hact := congrArg (fun f : MulAut G => (f d.val).val.val 0 0) he
  change σ (d.val.val.val 0 0) = (g * d.val * g⁻¹).val.val 0 0 at hact
  have hd : d.val.val.val 0 0 = x := by
    rw [← torusCharacter_fst_val F σ hσ d, torusCharacter_lift]
    rfl
  exact hx (by simpa only [hd] using hact.trans hm)


open UnitaryFourPlaneLocal
omit [CharP F 2] in
/-- The odd torus responsible for the obstruction already belongs to L₂. -/
theorem torusLift_mem_planeLocal (a : Fˣ) :
    (torusLift F σ hσ a 1).val ∈ localFactor F J := by
  apply (mem_localFactor F J _).mpr
  refine ⟨(torusLift F σ hσ a 1).property.2, ?_⟩
  have h10 := ((mem_pointParabolicSU F J _).mp (torusLift F σ hσ a 1).property.1).1
  have hd := torusCharacter_snd_val F σ hσ (torusLift F σ hσ a 1)
  rw [torusCharacter_lift] at hd
  simpa [restrictionMatrix, Matrix.det_fin_two, h10] using hd.symm

omit [CharP F 2] in
private theorem restriction_matrixAut (a : planeParabolicSU F J) :
    restrictionMatrix F J
      ⟨matrixAut F σ hσ a.val, (matrixAut_mem_plane F σ hσ _).mpr a.property⟩ =
      (restrictionMatrix F J a).map σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP F 2] in
/-- Coefficient conjugation preserves the actual determinant-one plane factor. -/
theorem matrixAut_mem_planeLocal (a : G) :
    matrixAut F σ hσ a ∈ localFactor F J ↔ a ∈ localFactor F J := by
  have hpres : ∀ a : G, a ∈ localFactor F J →
      matrixAut F σ hσ a ∈ localFactor F J := by
    intro b hb
    obtain ⟨hp,hd⟩ := (mem_localFactor F J b).mp hb
    apply (mem_localFactor F J _).mpr
    refine ⟨(matrixAut_mem_plane F σ hσ b).mpr hp, ?_⟩
    rw [restriction_matrixAut F σ hσ ⟨b,hp⟩]
    calc
      _ = σ (restrictionMatrix F J ⟨b,hp⟩).det := (σ.map_det _).symm
      _ = 1 := by rw [hd, map_one]
  constructor
  · intro h
    simpa only [show matrixAut F σ hσ (matrixAut F σ hσ a) = a from
      matrixHom_involutive F σ hσ a] using hpres _ h
  · exact hpres a

def planeLocalAut : MulAut (localFactor F J) where
  toFun a := ⟨matrixAut F σ hσ a.val, (matrixAut_mem_planeLocal F σ hσ _).mpr a.property⟩
  invFun a := ⟨matrixAut F σ hσ a.val, (matrixAut_mem_planeLocal F σ hσ _).mpr a.property⟩
  left_inv a := Subtype.ext (matrixHom_involutive F σ hσ a.val)
  right_inv a := Subtype.ext (matrixHom_involutive F σ hσ a.val)
  map_mul' a b := Subtype.ext (map_mul (matrixAut F σ hσ) a.val b.val)

/-- The action on the actual two-core quotient, induced by the matrix involution. -/
def planeQuotientAut : MulAut (localFactor F J ⧸ pCore 2 (localFactor F J)) :=
  QuotientGroup.congr _ _ (planeLocalAut F σ hσ) (pCore_map_iso 2 _)

/-- Under the proved quotient identification, the induced action is entrywise σ. -/
theorem planeQuotientAut_field (x : localFactor F J ⧸ pCore 2 (localFactor F J)) :
    UnitaryFourPlaneRadical.quotientEquivSL2 F σ hσ (planeQuotientAut F σ hσ x) =
      SpecialLinearGroup.map σ.toRingHom
        (UnitaryFourPlaneRadical.quotientEquivSL2 F σ hσ x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    change factorRestriction F J (planeLocalAut F σ hσ g) =
      SpecialLinearGroup.map σ.toRingHom (factorRestriction F J g)
    apply Subtype.ext
    rw [UnitaryFourPlaneRadical.factorRestriction_val,
      SpecialLinearGroup.map_apply_coe, UnitaryFourPlaneRadical.factorRestriction_val]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl


omit [Finite F] in
/-- The candidate is literally the join of the embedded U with ⟨σ⟩. -/
theorem extendedUpper_eq_sup : extendedUpper F σ hσ =
    (upper F σ hσ).map SemidirectProduct.inl ⊔ Subgroup.zpowers (sigma F σ hσ) := by
  apply le_antisymm
  · intro x hx
    have hleft : SemidirectProduct.inl x.left ∈
        (upper F σ hσ).map (SemidirectProduct.inl (φ := action F σ hσ)) :=
      ⟨x.left, hx, rfl⟩
    have hright : SemidirectProduct.inr x.right ∈ Subgroup.zpowers (sigma F σ hσ) := by
      rcases c2_cases x.right with hr | hr
      · simp [hr]
      · rw [hr]
        exact Subgroup.mem_zpowers _
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hleft) (Subgroup.mem_sup_right hright)
  · apply sup_le
    · rintro _ ⟨x,hx,rfl⟩
      exact hx
    · exact Subgroup.zpowers_le.mpr (upper F σ hσ).one_mem

/-- This torus lies in B₂ = N_{L₂}(U ∩ L₂); shrinking from the full Borel to
B₁B₂⟨σ⟩ therefore does not remove the offending diagonal elements. -/
theorem torusLift_mem_planeLocal_normalizer (a : Fˣ) :
    (⟨(torusLift F σ hσ a 1).val, torusLift_mem_planeLocal F σ hσ a⟩ :
      localFactor F J) ∈
      Subgroup.normalizer ((upper F σ hσ).subgroupOf (localFactor F J) : Set _) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp
    (borel_le_normalizer_upper F σ hσ (torusLift F σ hσ a 1).property) x.val

omit [Finite F] in
/-- For S = U⟨σ⟩, the source S₁ = S ∩ L₁ is precisely the embedded U. -/
theorem extendedUpper_inf_pointLocal :
    extendedUpper F σ hσ ⊓
      (UnitaryFourPointLocal.localSU F J).map SemidirectProduct.inl =
      (upper F σ hσ).map SemidirectProduct.inl := by
  ext x
  constructor
  · rintro ⟨hx,y,hy,rfl⟩
    exact ⟨y,hx,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hy,⟨y,((mem_upper F σ hσ y).mp hy).1,rfl⟩⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
