module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SmallNormalizer
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Fixed-space families in the full doubled natural normalizer

An elementary actor in A_j with j at least two has trivial coefficient
image: its field-linear kernel has index at most two, and its nonzero fixed
field line is therefore fixed by the whole actor. The faithful SL₃ × SL₂
tensor coordinates then give a multiplicity image of rank at most n.
For j>n the natural kernel has the same fixed space as the whole actor.
A common fixed natural vector in both copies forces every multiplicity
factor to be scalar, hence trivial in characteristic two.

Thus A_{2n} lies in the identical natural SL₃ component in every positive
binary degree. CriticalAction applies this to the literal E.3.10 image in
source 11.3.6; neither odd degree nor a small fixed codimension is assumed.

Source: Aschbacher--Smith, 11.3.6, printed p.772, the critical-pair action.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace FixedFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
local instance : Finite (Module.End (ZMod 2) (Space F)) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

omit [Finite F] [CharP F 2] in
private theorem coefficient_unique (b : Ambient F) {σ τ : F ≃+* F}
    (hs : ∀ c v, action F b (c • v) = σ c • action F b v)
    (ht : ∀ c v, action F b (c • v) = τ c • action F b v) : σ = τ := by
  ext c
  let w : Space F := fun _ _ => 1
  have he := (hs c (action F b⁻¹ w)).symm.trans (ht c (action F b⁻¹ w))
  have hc : action F b (action F b⁻¹ w) = w := by
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rw [hc] at he
  simpa only [w,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun (congrFun he 0) 0

private def coefficient (A : Subgroup (Ambient F)) (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F) :
    A →* (F ≃+* F) where
  toFun a := (normalizer_semilinear a.val (hAN a.property)).choose
  map_one' := coefficient_unique 1 (normalizer_semilinear 1 (hAN A.one_mem)).choose_spec
    (by intro c v; simp [action])
  map_mul' a b := coefficient_unique (a.val*b.val)
    (normalizer_semilinear _ (hAN (A.mul_mem a.property b.property))).choose_spec
    (by
      intro c v
      change (a.val : Module.End (ZMod 2) (Space F))
        ((b.val : Module.End (ZMod 2) (Space F)) (c • v)) = _
      rw [(normalizer_semilinear b.val (hAN b.property)).choose_spec,
        (normalizer_semilinear a.val (hAN a.property)).choose_spec]
      rfl)

omit [CharP F 2] in
private theorem coefficient_smul (A : Subgroup (Ambient F))
    (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F) (a : A) (c : F) (v : Space F) :
    action F a.val (c • v) = coefficient A hAN a c • action F a.val v :=
  (normalizer_semilinear a.val (hAN a.property)).choose_spec c v

private theorem kernel_corank {X : Type*} [Group X] [Finite X]
    (A : Subgroup X) {Y : Type*} [Group Y] (φ : A →* Y) :
    Nat.log 2 (((φ.ker.map A.subtype)).relIndex A) = rank φ.range := by
  change Nat.log 2 ((φ.ker.map A.subtype).comap A.subtype).index = _
  rw [comap_map_eq_self_of_injective A.subtype_injective,index_ker]
  rfl

/-- A fixed-space family of parameter at least two kills the coefficient action. -/
theorem family_linear {j : ℕ} (hj : 2 ≤ j) {A : Subgroup (Ambient F)}
    (hA : A ∈ fixedSpaceFamily (action F) j)
    (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F)
    (a : A) (c : F) (v : Space F) : action F a.val (c • v) = c • action F a.val v := by
  let := hA.2.1.2
  let φ := coefficient A hAN
  let B := φ.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hcor : Nat.log 2 (B.relIndex A) < j := by
    rw [kernel_corank A φ]
    have hb := Nat.log_mono_right (SL2NaturalOffenders.fieldAction_range_card_le_two A inferInstance φ) (b := 2)
    change Nat.log 2 (Nat.card φ.range) ≤ Nat.log 2 2 at hb
    have htwo : Nat.log 2 2 = 1 := by decide
    rw [htwo] at hb
    change Nat.log 2 (Nat.card φ.range) < j
    omega
  have hfix := hA.2.2 B hBA hcor
  have hlin (b : B) (r : F) (w : Space F) : action F b.val (r • w) = r • action F b.val w := by
    obtain ⟨x,hx,he⟩ := b.property
    have hs := coefficient_smul A hAN x r w
    rw [MonoidHom.mem_ker.mp hx] at hs
    change (x : Ambient F) = b.val at he
    rw [he] at hs
    exact hs
  let τ : Representation F B (Space F) :=
    { toFun b :=
        { toFun := action F b.val
          map_add' := (action F b.val).map_add
          map_smul' := hlin b }
      map_one' := by apply LinearMap.ext; intro w; rfl
      map_mul' b e := by apply LinearMap.ext; intro w; rfl }
  obtain ⟨w,hw,hfw⟩ := pGroup_fix_nonzero_vector
    (F := F) (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using
      (IsElementaryAbelian.isPGroup 2 A).to_le hBA) τ
  have hline (r : F) : r • w ∈ fixedSpace (action F) A := by
    rw [hfix]
    intro b
    change τ b (r • w) = r • w
    rw [map_smul]
    exact congrArg (r • ·) (hfw b)
  have he : φ a c • w = c • w := by
    have hs := coefficient_smul A hAN a c w
    rw [show action F a.val w = w from by simpa using hline 1 a] at hs
    exact hs.symm.trans (hline c a)
  have hc : φ a c = c := (smul_left_injective F hw) he
  change coefficient A hAN a c = c at hc
  rw [coefficient_smul A hAN,hc]

omit [Finite F] in
private theorem tensor_fixes_copies (g : SL F) (c : MultiplicitySL F)
    (v : Natural F) (hv : v ≠ 0)
    (hfix : ∀ i : Fin 2, tensorRepresentation F (g,c) (Pi.single i v) = Pi.single i v) : c=1 := by
  let w := g.val.mulVec v
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    exact ((specialLinearNatural (k := F) 3).apply_bijective g).1
      (hz.trans (map_zero _).symm)
  have hh (i j : Fin 2) : c.val i j • w = if i=j then v else 0 := by
    have he := congrFun (hfix j) i
    change g.val.mulVec (c.val i 0 • (Pi.single j v : Space F) 0 + c.val i 1 • (Pi.single j v : Space F) 1) = _ at he
    fin_cases i <;> fin_cases j <;> simpa [Matrix.mulVec_add,Matrix.mulVec_smul,w] using he
  have h01 : c.val 0 1 = 0 := (smul_eq_zero.mp (by simpa using hh 0 1)).resolve_right hw
  have h10 : c.val 1 0 = 0 := (smul_eq_zero.mp (by simpa using hh 1 0)).resolve_right hw
  have h00 : c.val 0 0 • w = v := by simpa using hh 0 0
  have h11 : c.val 1 1 • w = v := by simpa using hh 1 1
  have hd : c.val 0 0 = c.val 1 1 := (smul_left_injective F hw) (h00.trans h11.symm)
  have hs : c.val 0 0 ^ 2 = 1 := by
    have he := c.property
    rw [Matrix.det_fin_two,h01,h10,←hd] at he
    simpa [pow_two] using he
  have hone : c.val 0 0 = 1 := CharTwo.sq_injective (by simpa using hs)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01,h10,←hd,hone]

/-- A_{j} with j>n removes the multiplicity action as well as the field action. -/
theorem family_le_component {n j : ℕ} (hF : Nat.card F = 2^n)
    (hj : 2 ≤ j) (hnj : n < j) {A : Subgroup (Ambient F)}
    (hA : A ∈ fixedSpaceFamily (action F) j)
    (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F) : A ≤ component F := by
  let := hA.2.1.2
  have hAt : A ≤ tensorSubgroup F := by
    intro a ha
    obtain ⟨g,c,hgc⟩ := normalizer_linear_tensor_factors a (hAN ha)
      (family_linear hj hA hAN ⟨a,ha⟩)
    exact involution_mem_tensorSubgroup_of_gl_factors a g c hgc
      (elemPow_eq_one_of_isElementaryAbelian a ha)
  let e : (SL F × MultiplicitySL F) ≃* tensorSubgroup F :=
    MonoidHom.ofInjective SmallNormalizer.tensor_injective
  let f : A →* (SL F × MultiplicitySL F) := e.symm.toMonoidHom.comp (inclusion hAt)
  have hf (a : A) : (tensorRepresentation F).asGroupHom (f a) = a.val :=
    congrArg Subtype.val (e.apply_symm_apply (inclusion hAt a))
  let φ := (MonoidHom.snd (SL F) (MultiplicitySL F)).comp f
  let B := φ.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hcor : Nat.log 2 (B.relIndex A) < j := by
    rw [kernel_corank A φ]
    let : IsElementaryAbelian 2 φ.range :=
      IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hb := Nat.log_mono_right (multiplicity_elementary_card_le φ.range) (b := 2)
    rw [hF,Nat.log_pow (by decide)] at hb
    exact hb.trans_lt hnj
  have hfix := hA.2.2 B hBA hcor
  let τ : Representation F φ.ker (Natural F) :=
    (specialLinearNatural 3).comp ((MonoidHom.fst _ _).comp (f.comp φ.ker.subtype))
  have hp : IsPGroup 2 φ.ker := (IsElementaryAbelian.isPGroup 2 A).to_subgroup _
  obtain ⟨v,hv,hfv⟩ := pGroup_fix_nonzero_vector
    (F := F) (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hp) τ
  have hcopies (i : Fin 2) : Pi.single i v ∈ fixedSpace (action F) A := by
    rw [hfix]
    rintro ⟨b,x,hx,rfl⟩
    change action F x.val (Pi.single i v) = Pi.single i v
    rw [←hf x]
    have hx2 : (f x).2 = 1 := MonoidHom.mem_ker.mp hx
    change tensorRepresentation F (f x) (Pi.single i v) = Pi.single i v
    have he : f x = ((f x).1,1) := Prod.ext rfl hx2
    rw [he]
    change representation F (f x).1 (multiplicityRepresentation F 1 (Pi.single i v)) = _
    rw [map_one,Module.End.one_apply]
    ext k l
    by_cases hk : k=i
    · subst k
      have hvv : (f x).1.val.mulVec v = v := hfv ⟨x,hx⟩
      simpa using congrFun hvv l
    · simp [representation,hk]
  intro a ha
  let x : A := ⟨a,ha⟩
  have hc : (f x).2=1 := tensor_fixes_copies (f x).1 (f x).2 v hv
    (fun i => by change action F ((tensorRepresentation F).asGroupHom (f x)) _ = _
                 rw [hf]; exact hcopies i x)
  refine ⟨(f x).1,?_⟩
  change (representation F).asGroupHom (f x).1 = x.val
  rw [←hf x]
  apply Units.ext
  change representation F (f x).1 = representation F (f x).1 * multiplicityRepresentation F (f x).2
  rw [hc,map_one,mul_one]

end FixedFamily
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
