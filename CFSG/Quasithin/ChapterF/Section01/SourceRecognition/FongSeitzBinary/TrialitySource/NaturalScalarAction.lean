module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.NaturalSectionApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.NaturalShears

/-!
# Recovering the actual natural scalar action in the triality source

The canonical radical quotient already has two additive cubic-field axes.
Its upper roots act by additive shears and its Weyl element exchanges the
axes. NaturalShears derives the diagonal action and multiplicative shear
operators from the whole rank-one group. The long diagonal normalizes the
first literal root, so its section action lifts to that root. Both coroots
belong to the same abelian full Cartan; hence the shears commute with every
short-coroot square scalar. Every scalar in the finite characteristic-two
field is a square, which proves linearity over that same cubic field.

Evaluation at one now constructs a field embedding of the actual fixed
field. The existing marking forces its image back into that fixed field.
This yields a single field automorphism of the entire long actor. The whole
matrix formula is proved by transvection generation, with an explicit
intertwining equation on the actual radical quotient. Relabeling the whole
pinning by the inverse automorphism gives the required leading mixed
commutator in U/(E D F). It also gives all six signed short-root characters
of the long coroot, retaining the third root's Frobenius shift.

The final scalar-comparison consumer no longer assumes a natural matrix
action or its scalar coefficient. The eight-dimensional tensor equations,
their lifts and covariance, the other mixed Cartan characters and full
recognition remain unproved source obligations. GeometricScalars supplies
both coroot placements and the pinning from the literal quotient geometry.
No perfectness or exclusion of q=2 or q=4 is used.

Source: Fong--Seitz I (6E)(b), II (9.24)--(9.31), printed pp.218--219.
All actions here are left conjugation; right commutators are x⁻¹y⁻¹xy.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.NaturalScalarAction
open NaturalSectionApplication
variable {X F : Type*} [Group X] [Field F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {σ : F ≃+* F} (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (hs : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (hl : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (hm : rotationOrder Q = 6)
  (hKs : simpleRemainder Q split (w.indices 0) ≤ localKernel Q (w.indices 0))
  (hKl : simpleRemainder Q split (w.indices 1) ≤ localKernel Q (w.indices 1))
  (row : StructuralRow Q split (w.indices 0) (w.indices 1))
  (hf : Function.Injective p.shortMap)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "d" => sourceSection Q split p w hs hm hKs hKl row
local notation "c" => fieldCoordinates Q split p w hs hm hKs hKl row hf
local notation "r" => action Q split p w hs hl hm hKs hKl row hf
local notation "f" => shear Q split p w hs hl hm hKs hKl row hf
local notation "hU" => action_uni Q split p w hs hl hm hKs hKl row hf
local notation "hW" => action_weyl Q split p w hs hl hm hKs hKl row hf
local notation "h1" => shear_one Q split p w hs hl hm hKs hKl row hf

/-- The actual source torus acts on both axes by the constructed shears. -/
theorem action_tor (t : Kˣ) (a b : F) :
    r (tor t) (.ofAdd a,.ofAdd b) =
      (.ofAdd (f (t⁻¹).val a),.ofAdd (f t.val b)) :=
  NaturalShears.action_tor r f hU hW h1 t a b

variable
  (hTs : ∀ t : Fˣ, p.shortMap (tor t) ∈ Q.tits.B ⊓ Q.tits.N)
  (hTl : ∀ t : (ScalarMarking.SourceFixed (σ := σ))ˣ, p.longMap (tor t) ∈ Q.tits.B ⊓ Q.tits.N)

include hTl in
/-- The first-axis torus formula lifts from the section to the literal simple root. -/
theorem tor_short (t : Kˣ) (a : F) :
    p.longMap (tor t)*p.s 0 a*(p.longMap (tor t))⁻¹ = p.s 0 (f (t⁻¹).val a) := by
  have hx : p.longMap (tor t)*p.s 0 a*(p.longMap (tor t))⁻¹ ∈
      simpleRoot Q split (w.indices 0) :=
    (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split (w.indices 0) (hTl t))
      (p.s 0 a)).mp (hs ▸ ⟨.ofAdd a,rfl⟩)
  obtain ⟨b,hb⟩ := hs.symm ▸ hx
  have he : (d).action (longActor Q split p w hl (tor t)) (c (.ofAdd a,1)) = c (b,1) := by
    change (QuotientGroup.mk' (d).denominator) _ = (QuotientGroup.mk' (d).denominator) _
    apply congrArg (QuotientGroup.mk' (d).denominator)
    apply Subtype.ext
    change p.longMap (tor t) * (p.s 0 a * p.shortOrbit 1 1) *
      (p.longMap (tor t))⁻¹ = p.shortOrbit 0 b * p.shortOrbit 1 1
    simpa only [map_one,mul_one] using hb.symm
  rw [← action_intertwines,show (1 : Multiplicative F) = .ofAdd 0 from rfl,
    action_tor,map_zero] at he
  have hb' : .ofAdd (f (t⁻¹).val a) = b := congrArg Prod.fst ((c).injective he)
  exact hb.symm.trans (congrArg (p.shortOrbit 0) hb'.symm)

include hTs hTl in
/-- Full-Cartan abelianness makes the source shear commute with every square scalar. -/
theorem shear_square (b : K) (a x : F) : f b (a^2*x) = a^2*f b x := by
  by_cases hb : b = 0
  · subst b
    rw [shear_zero,shear_zero,mul_zero]
  by_cases ha : a = 0
  · simp [ha]
  let t : Kˣ := Units.mk0 b hb
  let u : Fˣ := Units.mk0 a ha
  let T := p.longMap (tor t⁻¹)
  let S := p.shortMap (tor u)
  have ht (x : F) : T*p.s 0 x*T⁻¹ = p.s 0 (f b x) := by
    simpa only [T,t,inv_inv,Units.val_mk0] using
      tor_short Q split p w hs hl hm hKs hKl row hf hTl t⁻¹ x
  have hu (x : F) : S*p.s 0 x*S⁻¹ = p.s 0 (a^2*x) := by
    change p.shortMap (tor u)*p.shortMap (uni x)*(p.shortMap (tor u))⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,Borel_conj_uni]
    · rfl
    · exact (mem_Borel_iff _).mpr (by simp)
  have hc : Commute T S := by
    let := split.abelian
    exact congrArg Subtype.val (mul_comm
      (⟨T,hTl t⁻¹⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ⟨S,hTs u⟩)
  apply uni_injective
  apply hf
  change p.s 0 (f b (a^2*x)) = p.s 0 (a^2*f b x)
  calc
    _ = T*(S*p.s 0 x*S⁻¹)*T⁻¹ := by rw [hu,ht]
    _ = S*(T*p.s 0 x*T⁻¹)*S⁻¹ := by
      calc
        _ = (T*S)*p.s 0 x*(T*S)⁻¹ := by group
        _ = (S*T)*p.s 0 x*(S*T)⁻¹ := by rw [hc.eq]
        _ = _ := by group
    _ = _ := by rw [ht,hu]

variable [Finite F]
include hTs hTl in
/-- Every source shear is linear over the existing cubic field. No natural
representation or scalar-linearity premise is supplied. -/
theorem shear_scalar (b : K) (a x : F) : f b (a*x) = a*f b x := by
  obtain ⟨u,rfl⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := F))) a
  exact shear_square Q split p w hs hl hm hKs hKl row hf hTs hTl b u x

include hTs hTl in
theorem shear_coefficient (b : K) (a : F) : f b a = a*f b 1 := by
  simpa only [mul_one] using shear_scalar Q split p w hs hl hm hKs hKl row hf hTs hTl b a 1

/-- The coefficient embedding is constructed from the actual source section action. -/
def coefficientMap : K →+* F where
  toFun b := f b 1
  map_zero' := shear_zero Q split p w hs hl hm hKs hKl row hf 1
  map_one' := shear_one Q split p w hs hl hm hKs hKl row hf 1
  map_add' b₁ b₂ := NaturalShears.parameter_add r f hU b₁ b₂ 1
  map_mul' b₁ b₂ := by
    rw [NaturalShears.parameter_mul r f hU hW h1,
      shear_coefficient Q split p w hs hl hm hKs hKl row hf hTs hTl]
    exact mul_comm _ _


local notation "k" => coefficientMap Q split p w hs hl hm hKs hKl row hf hTs hTl

/-- The entire source rank-one action has the natural two-dimensional matrix
formula in the original cubic-field coordinates (with the two axes reversed). -/
theorem action_matrix (g : SL2 K) (a b : F) :
    r g (.ofAdd a,.ofAdd b) =
      (.ofAdd (k (g.val 1 1)*a+k (g.val 1 0)*b),
       .ofAdd (k (g.val 0 1)*a+k (g.val 0 0)*b)) := by
  revert a b
  apply Matrix.SL2.transvection_induction (fun g => ∀ a b : F,
    r g (.ofAdd a,.ofAdd b) =
      (.ofAdd (k (g.val 1 1)*a+k (g.val 1 0)*b),
       .ofAdd (k (g.val 0 1)*a+k (g.val 0 0)*b)))
  · intro i j hij t a b
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [hU]
      rw [shear_coefficient Q split p w hs hl hm hKs hKl row hf hTs hTl]
      change (Multiplicative.ofAdd a,Multiplicative.ofAdd (a*k t+b)) = _
      simp [Matrix.SpecialLinearGroup.transvection_coe,mul_comm]
    · rw [lower_transvection_eq_weyl_uni]
      simp only [map_mul,MulAut.mul_apply,hW,hU]
      rw [shear_coefficient Q split p w hs hl hm hKs hKl row hf hTs hTl]
      change (Multiplicative.ofAdd (b*k t+a),Multiplicative.ofAdd b) = _
      simp [Matrix.mul_apply,Fin.sum_univ_two,mul_comm,add_comm]
    · exact (hij rfl).elim
  · intro g₁ g₂ hg₁ hg₂ a b
    simp only [map_mul,MulAut.mul_apply,hg₁,hg₂]
    apply Prod.ext <;> apply Multiplicative.ofAdd.injective.eq_iff.mpr
    · simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,map_add,map_mul]
      ring
    · simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,map_add,map_mul]
      ring

/-- The two-dimensional matrix actor recovered from the actual quotient action. -/
def matrixAction : SL2 K →* SL2 F := Matrix.SpecialLinearGroup.map k

local notation "m" => matrixAction Q split p w hs hl hm hKs hKl row hf hTs hTl

@[simp] theorem matrixAction_uni (b : K) : m (uni b) = uni (k b) := by
  ext i j
  change k ((uni b).val i j) = (uni (k b)).val i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem matrixAction_weyl : m (weyl K) = weyl F := by
  ext i j
  change k ((weyl K).val i j) = (weyl F).val i j
  fin_cases i <;> fin_cases j <;> simp

/-- The recovered matrix representation intertwines literal conjugation on
the original radical quotient, using its two constructed field coordinates. -/
theorem matrix_intertwines (g : SL2 K) (a b : F) :
    c (.ofAdd ((m g).val 1 1*a+(m g).val 1 0*b),
       .ofAdd ((m g).val 0 1*a+(m g).val 0 0*b)) =
      (d).action (longActor Q split p w hl g) (c (.ofAdd a,.ofAdd b)) := by
  rw [← action_intertwines]
  exact congrArg c (action_matrix Q split p w hs hl hm hKs hKl row hf hTs hTl g a b).symm

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

include e in
/-- The source coefficient field lands in the same fixed subfield, with one
whole-actor automorphism rather than independently chosen field markings. -/
theorem exists_scalar_automorphism :
    ∃ η : K ≃+* K, ∀ b : K, k b = (η b).val := by
  obtain ⟨η,hη⟩ := NaturalCoordinates.exists_fixed_automorphism e m
    (fun b => ⟨k b,matrixAction_uni Q split p w hs hl hm hKs hKl row hf hTs hTl b⟩)
    (matrixAction_weyl Q split p w hs hl hm hKs hKl row hf hTs hTl)
  refine ⟨η,?_⟩
  intro b
  have hh := congrArg (fun g : SL2 F => g.val 0 1) (DFunLike.congr_fun hη (uni b))
  change k ((uni b).val 0 1) = (η ((uni b).val 0 1)).val at hh
  simpa using hh

/-- The actual scalar twist of the source long actor on the cubic root. -/
def scalarAutomorphism : K ≃+* K :=
  Classical.choose (exists_scalar_automorphism Q split p w hs hl hm hKs hKl row hf hTs hTl e)

local notation "η" => scalarAutomorphism Q split p w hs hl hm hKs hKl row hf hTs hTl e

theorem coefficientMap_eq (b : K) : k b = (η b).val :=
  Classical.choose_spec (exists_scalar_automorphism Q split p w hs hl hm hKs hKl row hf hTs hTl e) b

/-- The general leading mixed coefficient, including q=2 and q=4, now follows
from the section construction and Cartan, without a natural-module hypothesis. -/
theorem shear_eq (b : K) (a : F) : f b a = a*(η b).val := by
  rw [shear_coefficient Q split p w hs hl hm hKs hKl row hf hTs hTl]
  exact congrArg (a*·) (coefficientMap_eq Q split p w hs hl hm hKs hKl row hf hTs hTl e b)

/-- The actual mixed simple-root Cartan action before scalar relabeling. -/
theorem long_torus_short (t : Kˣ) (a : F) :
    p.longMap (tor t)*p.s 0 a*(p.longMap (tor t))⁻¹ = p.s 0 (a*(η t.val).val⁻¹) := by
  rw [tor_short Q split p w hs hl hm hKs hKl row hf hTl,
    shear_eq Q split p w hs hl hm hKs hKl row hf hTs hTl e]
  simp only [Units.val_inv_eq_inv_val,map_inv₀,Subfield.coe_inv]

omit [Finite F] in
private theorem B_long_torus (t : Kˣ) :
    p.dihedral.B (p.longMap (tor t)) = p.longMap (tor t⁻¹) := by
  change p.longMap (weyl K)*p.longMap (tor t)*(p.longMap (weyl K))⁻¹ = _
  rw [← map_inv,← map_mul,← map_mul,weyl_tor]

omit [Finite F] in
private theorem W_long_torus (t : Kˣ) :
    p.dihedral.W (p.longMap (tor t)) = p.longMap (tor t⁻¹) := by
  rw [p.W_longMap]
  exact B_long_torus Q p t

/-- All three short-root characters of the long torus follow from the natural
action and the already proved orthogonal centralization. -/
theorem long_torus_short_root (t : Kˣ) (i : Fin 3) (a : F) :
    p.longMap (tor t)*p.s i a*(p.longMap (tor t))⁻¹ =
      p.s i (![ (η t.val).val⁻¹, (η t.val).val, 1 ] i * a) := by
  fin_cases i
  · change p.longMap (tor t)*p.s 0 a*(p.longMap (tor t))⁻¹ = p.s 0 ((η t.val).val⁻¹*a)
    simpa only [mul_comm] using
      long_torus_short Q split p w hs hl hm hKs hKl row hf hTs hTl e t a
  · have hh := congrArg p.dihedral.B
      (long_torus_short Q split p w hs hl hm hKs hKl row hf hTs hTl e t⁻¹ a)
    simp only [map_mul,map_inv,B_long_torus,inv_inv,Units.val_inv_eq_inv_val,
      map_inv₀,Subfield.coe_inv] at hh
    change p.longMap (tor t)*p.dihedral.B (p.s 0 a)*(p.longMap (tor t))⁻¹ =
      p.dihedral.B (p.s 0 ((η t.val).val*a))
    simpa only [mul_comm] using hh
  · have hh := (p.longMap_commute_short2
      (StructuralApplication.positiveCommutations Q split p w hs hl hm row) (tor t) a).mul_inv_cancel
    change p.longMap (tor t)*p.s 2 a*(p.longMap (tor t))⁻¹ = p.s 2 (1*a)
    simpa only [one_mul] using hh

/-- The longest source word gives inverse characters on all negative short
roots. No additional negative-root action equation is assumed. -/
theorem long_torus_signed_short (t : Kˣ) (positive : Bool) (i : Fin 3) (a : F) :
    p.longMap (tor t)*p.signedValue positive (p.s i a)*(p.longMap (tor t))⁻¹ =
      p.signedValue positive (p.s i
        ((if positive then ![(η t.val).val⁻¹,(η t.val).val,1] i
          else (![(η t.val).val⁻¹,(η t.val).val,1] i)⁻¹)*a)) := by
  cases positive
  · have hh := congrArg p.dihedral.W
      (long_torus_short_root Q split p w hs hl hm hKs hKl row hf hTs hTl e t⁻¹ i a)
    simp only [map_mul,map_inv,W_long_torus,inv_inv,Units.val_inv_eq_inv_val,
      map_inv₀,Subfield.coe_inv] at hh
    change p.longMap (tor t)*p.dihedral.W (p.s i a)*(p.longMap (tor t))⁻¹ =
      p.dihedral.W (p.s i ((![(η t.val).val⁻¹,(η t.val).val,1] i)⁻¹*a))
    rw [hh]
    congr 3
    fin_cases i <;> simp
  · exact long_torus_short_root Q split p w hs hl hm hKs hKl row hf hTs hTl e t i a

/-- Relabeling the entire long pinning gives its required inverse mixed
character on the literal short simple root. -/
theorem relabeled_hB_short (t : Kˣ) (a : F) :
    ((p.relabelLong (η).symm).signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*p.s 0 a*
      (((p.relabelLong (η).symm).signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
        p.s 0 (a*t.val.val⁻¹) := by
  rw [p.relabelLong_hB, p.hB_parameter,
    long_torus_short Q split p w hs hl hm hKs hKl row hf hTs hTl e]
  change p.s 0 (a*((η) ((η).symm t.val)).val⁻¹) = _
  rw [(η).apply_symm_apply]

/-- All signed short-root characters for the relabeled source long coroot.
The third orbit retains its required Frobenius shift through signedRoots. -/
theorem relabeled_hB_signed_short (t : Kˣ) (positive : Bool) (i : Fin 3) (a : F) :
    ((p.relabelLong (η).symm).signedRoots e).hB (Units.map e.fixed.toMonoidHom t)*
      ((p.relabelLong (η).symm).signedRoots e).shortSigned positive i (e.extension a)*
      (((p.relabelLong (η).symm).signedRoots e).hB (Units.map e.fixed.toMonoidHom t))⁻¹ =
    ((p.relabelLong (η).symm).signedRoots e).shortSigned positive i
      (e.extension ((if positive then ![t.val.val⁻¹,t.val.val,1] i
        else (![t.val.val⁻¹,t.val.val,1] i)⁻¹)*a)) := by
  rw [p.relabelLong_hB,p.hB_parameter,
    p.relabelLong_signedShort,p.relabelLong_signedShort]
  rw [p.signedRoots_short,p.signedRoots_short]
  have hh (j : Fin 3) (x : F) := long_torus_signed_short Q split p w hs hl hm hKs hKl row hf hTs hTl e
    (Units.map (η).symm.toMonoidHom t) positive j x
  have hval : (η (Units.map (η).symm.toMonoidHom t).val).val = t.val.val := by
    change (η ((η).symm t.val)).val = t.val.val
    rw [(η).apply_symm_apply]
  simp only [hval] at hh
  by_cases hi : i = 2
  · subst i
    have hweight : (if positive then ![t.val.val⁻¹,t.val.val,1] (2 : Fin 3)
        else (![t.val.val⁻¹,t.val.val,1] (2 : Fin 3))⁻¹) = (1 : F) := by
      cases positive <;> simp
    simpa only [RankOnePair.markedShort_two,hweight,one_mul] using hh 2 (σ a)
  · have hmark (x : F) : p.markedShort i (.ofAdd x) = p.s i x := by
      rw [RankOnePair.markedShort,if_neg hi]
    rw [hmark,hmark]
    exact hh i a

variable [hN : ((middleRoots Q split (w.indices 0) (w.indices 1)).subgroupOf split.U).Normal]
local notation "M" => Subgroup.subgroupOf (middleRoots Q split (w.indices 0) (w.indices 1)) split.U
local notation "A₀" => ScalarAlignment.sectionA Q split p w hs M
local notation "B₀" => ScalarAlignment.sectionB Q split p w hl M
local notation "C₀" => ScalarAlignment.sectionC Q split p w hs hl hm M

/-- The first matrix comparison on p.219 on the literal original section. -/
theorem section_commutator (a : F) (b : K) :
    rightCommutator (A₀ (.ofAdd a)) (B₀ (.ofAdd b)) = C₀ (.ofAdd (a*(η b).val)) := by
  rw [NaturalSectionApplication.section_commutator Q split p w hs hl hm hKs hKl row hf,
    shear_eq Q split p w hs hl hm hKs hKl row hf hTs hTl e]

/-- The leading mixed equation after relabeling all of the long actor. -/
theorem normalized_commutator (a : F) (b : K) :
    rightCommutator (A₀ (.ofAdd a))
      (ScalarAlignment.sectionB Q split (p.relabelLong (η).symm) (w.relabelLong Q p (η).symm)
        ((p.relabelLong_long_range (η).symm 0).trans hl) M (.ofAdd b)) =
      C₀ (.ofAdd (a*b.val)) := by
  rw [ScalarAlignment.sectionB_relabel Q split p w hl M (η).symm b,
    section_commutator Q split p w hs hl hm hKs hKl row hf hTs hTl e,
    RingEquiv.apply_symm_apply]

/-- The remaining tensor comparison uses the constructed natural actor.
Neither its matrix homomorphism nor its scalar coefficient is an input. -/
theorem compare_tensor (τ₁ τ₂ ρ : K ≃+* K) (θ x y : F)
    (htensor : ∀ a₀ a₁ a₂ b : K,
      rightCommutator (B₀ (.ofAdd b)) (A₀ (.ofAdd (a₀.val+a₁.val*θ+a₂.val*θ^2))) =
        C₀ (.ofAdd (x*(τ₂ (τ₁.symm b)).val *
          ((τ₂ (ρ a₀)).val+(τ₂ (ρ a₁)).val*y+(τ₂ (ρ a₂)).val*y^2)))) :
    x = 1 ∧ y = θ ∧ η = τ₁.symm.trans τ₂ ∧ ρ.trans τ₂ = RingEquiv.refl K := by
  exact ScalarComparison.same_section_twists (ScalarMarking.SourceFixed (σ := σ)).subtype
    η τ₁ τ₂ ρ θ x y C₀
    (sectionC_injective Q split p w hs hl hm hKs hKl row hf)
    (fun a => A₀ (.ofAdd a)) (fun b => B₀ (.ofAdd b))
    (section_commutator Q split p w hs hl hm hKs hKl row hf hTs hTl e) htensor

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.NaturalScalarAction
