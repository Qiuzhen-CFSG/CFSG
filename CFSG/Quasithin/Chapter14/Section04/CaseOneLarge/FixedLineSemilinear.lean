module
public import Theory.Representation.SL2.NaturalMultiplicity
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.SpecificGroups.GL2.Semilinear
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.ElementaryAbelian.Quotient
public import CFSG.Quasithin.ChapterG.Section09.Setup

/-!
# The whole doubled SL₂(4) action in semilinear coordinates

Conjugation on the original normal component determines its canonical
inner-field action. Removing that action from the blocks of the two-copy
module constructs a coefficient representation. The same field automorphism
acts on both factors. The coefficient kernel is exactly the original component;
the conjugation kernel is its actual centralizer. The pair is faithful and
reconstructs every operator on the original module by its matrix coefficients.

The coefficient representation is realized in the actual matrix group ΓL₂(4).
Thus the original quotient by the component is its coefficient image. The
component centralizer embeds in GL₂(4), with its action on the original whole
space retained. The automorphism two-rank bound makes its intersection with
the original order-eight elementary actor nontrivial. The constructor uses the marked doubled action and adds no
ambient recognition premise. Identifying the coefficient image from the source
actor geometry remains necessary for the final large-case catalogue.

The private semilinear matrix construction adapts
`SL2FourNaturalOrbits.SemilinearNormalizer.Basic` to the already marked canonical
field, avoiding a change of scalar structures. The source application is
`source_large_semilinear_remainder_of_mixed_size` in `CatalogueExclusion`.
Source: Aschbacher--Smith G.11.8, printed pp.368--369, and 14.4.2,
printed pp.1006--1007; the multiplicity construction is D.3.21.
-/

public noncomputable section
open Subgroup Module Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
open Representation.SL2AutomorphismNatural

variable {K D W : Type*} [Field K] [Finite K] [CharP K 2] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) K := ZMod.algebra _ 2

private theorem coefficient_semilinear
    (τ : Representation (ZMod 2) D (Fin 2 → (Fin 2 → K)))
    (α : D →* MulAut (SL(2,K))) (μ : Representation (ZMod 2) D (Fin 2 → K))
    (hm : ∀ a c v, τ a (fun i => c i • v) = fun i => μ a c i • action (α a) v) :
    ∀ a c z, μ a (c • z) = fieldAction (α a) c • μ a z := by
  intro a c z
  let w : Fin 2 → K := ![1,0]
  have hw : w ≠ 0 := by intro he; have hh := congrFun he 0; simp [w] at hh
  have haw : action (α a) w ≠ 0 := fun he =>
    hw ((action.apply_bijective (α a)).injective (he.trans (map_zero _).symm))
  have hh := hm a (c • z) w
  have he : (fun i => (c • z) i • w) = (fun i => z i • (c • w)) := by
    ext i j
    simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,mul_left_comm]
  rw [he,hm,action_semilinear] at hh
  funext i
  apply smul_left_injective K haw
  have hi := congrFun hh i
  simpa only [Pi.smul_apply,smul_smul,smul_eq_mul,mul_comm] using hi.symm

private theorem action_on_blocks
    (τ : Representation (ZMod 2) D (Fin 2 → (Fin 2 → K)))
    (α : D →* MulAut (SL(2,K))) (μ : Representation (ZMod 2) D (Fin 2 → K))
    (hm : ∀ a c v, τ a (fun i => c i • v) = fun i => μ a c i • action (α a) v)
    (a : D) (z : Fin 2 → (Fin 2 → K)) (i : Fin 2) :
    τ a z i = ∑ j : Fin 2, μ a (Pi.single j 1) i • action (α a) (z j) := by
  have hz : z = ∑ j : Fin 2, (fun i : Fin 2 => (Pi.single j (1 : K) : Fin 2 → K) i • z j) := by
    ext i k
    fin_cases i <;> simp
  conv_lhs => rw [hz]
  rw [map_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => congrFun (hm a (Pi.single j 1) (z j)) i)

private theorem field_trivial_inner (a : MulAut (SL(2,K)))
    (ha : fieldAction a = 1) : ∃ g : SL(2,K), a = MulAut.conj g := by
  let b := parameterEquiv.symm a
  have hb : b.right = 1 := ha
  have he : b = SemidirectProduct.inl b.left := SemidirectProduct.ext rfl hb
  refine ⟨b.left,?_⟩
  have hh := parameterEquiv.apply_symm_apply a
  change parameterAut b = a at hh
  rw [he] at hh
  exact hh.symm.trans (SemidirectProduct.lift_inl _ _ _ _)

private theorem ambient_coordinates
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (H : Subgroup D) [H.Normal] (e : H ≃* SL(2,K))
    (f : W ≃ₗ[ZMod 2] (Fin 2 → (Fin 2 → K)))
    (hf : ∀ h : H, ∀ w, f (ρ h w) = fun i => (e h).val.mulVec (f w i)) :
    ∃ (α : D →* MulAut (SL(2,K))) (μ : Representation (ZMod 2) D (Fin 2 → K)),
      α.ker = centralizer (H : Set D) ∧
      (∀ h : H, α h = MulAut.conj (e h)) ∧
      μ.asGroupHom.ker = H ∧
      (∀ a c z, μ a (c • z) = fieldAction (α a) c • μ a z) ∧
      (∀ a w i, f (ρ a w) i =
        ∑ j : Fin 2, μ a (Pi.single j 1) i • action (α a) (f w j)) ∧
      Function.Injective (α.prod μ.asGroupHom) := by
  let α : D →* MulAut (SL(2,K)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : D →* MulAut H)
  let τ : Representation (ZMod 2) D (Fin 2 → (Fin 2 → K)) :=
    f.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (a : D) (z) : τ a z = f (ρ a (f.symm z)) := rfl
  have hmark (h : H) : α h = MulAut.conj (e h) := by
    apply MulEquiv.ext
    intro k
    change e (MulAut.conjNormal (h : D) (e.symm k)) = e h * k * (e h)⁻¹
    rw [MulAut.conjNormal_val]
    simp [MulAut.conj_apply]
  have hα (a : D) (h : H) : α a (e h) = e (MulAut.conjNormal a h) := by
    change e (MulAut.conjNormal a (e.symm (e h))) = _
    rw [e.symm_apply_apply]
  have hcov : ∀ a k z, τ a (fun i => k.val.mulVec (z i)) =
      fun i => (α a k).val.mulVec (τ a z i) := by
    intro a k z
    obtain ⟨h,rfl⟩ := e.surjective k
    obtain ⟨w,rfl⟩ := f.surjective z
    rw [hα,←hf,hτ,f.symm_apply_apply,hτ,f.symm_apply_apply,←hf]
    apply congrArg f
    change ρ a (ρ (h:D) w) = ρ (a * (h:D) * a⁻¹) (ρ a w)
    simp only [←Module.End.mul_apply,←map_mul]
    congr 1
    group
  obtain ⟨μ,hm,hdiag,_,_⟩ := exists_two_copy_coefficients τ α hcov
  have hsemi := coefficient_semilinear τ α μ hm
  have hblocks := action_on_blocks τ α μ hm
  have hker : μ.asGroupHom.ker = H := by
    apply le_antisymm
    · intro a ha
      have hfield : fieldAction (α a) = 1 :=
        ScalarMultiplicity.semilinear_ker_le_field_ker μ (fieldAction.comp α) hsemi ha
      obtain ⟨k,hk⟩ := field_trivial_inner (α a) hfield
      obtain ⟨h,rfl⟩ := e.surjective k
      have hμ : μ a = 1 := congrArg Units.val (MonoidHom.mem_ker.mp ha)
      have he : a = h := by
        apply hρ
        ext w
        apply f.injective
        funext i
        have hh := hblocks a (f w) i
        rw [hτ,f.symm_apply_apply] at hh
        rw [hh,hf,hμ,hk]
        simp only [Module.End.one_apply,action_conj]
        fin_cases i <;> simp
      exact he ▸ h.property
    · intro h hh
      apply MonoidHom.mem_ker.mpr
      exact hdiag h (e ⟨h,hh⟩) (fun z => by simpa only [hτ,f.apply_symm_apply] using hf ⟨h,hh⟩ (f.symm z))
  have hak : α.ker = centralizer (H : Set D) := by
    ext a
    constructor
    · intro ha
      apply mem_centralizer_iff.mpr
      intro h hh
      have he := hα a ⟨h,hh⟩
      rw [MonoidHom.mem_ker.mp ha] at he
      have he' := congrArg Subtype.val (e.injective he)
      change h = a * h * a⁻¹ at he'
      exact eq_mul_inv_iff_mul_eq.mp he'
    · intro ha
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro k
      obtain ⟨h,rfl⟩ := e.surjective k
      rw [hα]
      change e (MulAut.conjNormal a h) = e h
      apply congrArg e
      apply Subtype.ext
      change a * (h:D) * a⁻¹ = h
      rw [←mem_centralizer_iff.mp ha h h.property,mul_assoc,mul_inv_cancel,mul_one]
  refine ⟨α,μ,hak,hmark,hker,hsemi,?_,?_⟩
  · intro a w i
    simpa only [hτ,f.symm_apply_apply] using hblocks a (f w) i
  · intro a b hab
    have hαab : α a = α b := congrArg Prod.fst hab
    have hμab : μ a = μ b := congrArg Units.val (congrArg Prod.snd hab)
    apply hρ
    ext w
    apply f.injective
    funext i
    have h1 := hblocks a (f w) i
    have h2 := hblocks b (f w) i
    simp only [hτ,f.symm_apply_apply] at h1 h2
    rw [h1,h2,hαab,hμab]

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
open Representation.SL2AutomorphismNatural (fieldAction)
open Matrix.GeneralLinearGroup (GammaL2)

section Gamma
variable {K D : Type*} [Field K] [CharP K 2] [Group D]
local instance : Algebra (ZMod 2) K := ZMod.algebra _ 2

private def gammaLinear : Matrix.GeneralLinearGroup (Fin 2) K →*
    ((Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K)) where
  toFun g := ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))) g).restrictScalars (ZMod 2)
  map_one' := by ext z i; exact congrFun (LinearEquiv.congr_fun
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))).map_one z) i
  map_mul' g h := by ext z i; exact congrFun (LinearEquiv.congr_fun
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))).map_mul g h) z) i

private def gammaField : (K ≃+* K) →* ((Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K)) where
  toFun σ := {
    toFun z i := σ (z i)
    invFun z i := σ.symm (z i)
    left_inv z := by ext i; exact σ.symm_apply_apply _
    right_inv z := by ext i; exact σ.apply_symm_apply _
    map_add' z w := by ext i; exact map_add σ _ _
    map_smul' c z := by
      ext i
      fin_cases c
      · change σ ((0 : ZMod 2) • z i) = (0 : ZMod 2) • σ (z i); simp
      · change σ ((1 : ZMod 2) • z i) = (1 : ZMod 2) • σ (z i); simp }
  map_one' := by ext z i; rfl
  map_mul' _ _ := by ext z i; rfl

private def gammaAction : GammaL2 K →* ((Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K)) :=
  SemidirectProduct.lift gammaLinear gammaField (by
    intro σ
    ext g z i
    change ((g.val.map σ).mulVec z) i = σ (g.val.mulVec (fun j => σ.symm (z j)) i)
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,RingEquiv.apply_symm_apply,Matrix.map_apply])

private theorem gammaAction_apply (g : GammaL2 K) (z : Fin 2 → K) :
    gammaAction g z = g.left.val.mulVec (fun i => g.right (z i)) := rfl

private theorem gammaAction_semilinear (g : GammaL2 K) (c : K) (z : Fin 2 → K) :
    gammaAction g (c • z) = g.right c • gammaAction g z := by
  change g.left.val.mulVec (fun i => g.right (c * z i)) = _
  simp only [map_mul]
  exact Matrix.mulVec_smul g.left.val (g.right c) _

private theorem gammaAction_injective : Function.Injective (gammaAction (K := K)) := by
  intro g h he
  have hr : g.right = h.right := by
    apply RingEquiv.ext
    intro c
    obtain ⟨z,hz⟩ := (gammaAction g).surjective (fun _ => 1)
    have hh := LinearEquiv.congr_fun he (c • z)
    rw [gammaAction_semilinear,gammaAction_semilinear,←he,hz] at hh
    simpa using congrFun hh 0
  apply SemidirectProduct.ext ?_ hr
  have hh : gammaLinear g.left * gammaField g.right = gammaLinear h.left * gammaField h.right := he
  rw [hr] at hh
  have hl := mul_right_cancel hh
  apply (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))).injective
  apply LinearEquiv.ext
  intro z
  exact LinearEquiv.congr_fun hl z

private theorem gammaAction_exists (e : (Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K))
    (σ : K ≃+* K) (he : ∀ c z, e (c • z) = σ c • e z) :
    ∃ g : GammaL2 K, gammaAction g = e := by
  let l : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) := {
    ((gammaField σ).symm.trans e).toAddEquiv with
    map_smul' := by
      intro c z
      change e (fun i => σ.symm (c * z i)) = c • _
      simp only [map_mul]
      change e (σ.symm c • (fun i => σ.symm (z i))) = _
      rw [he,RingEquiv.apply_symm_apply]
      rfl }
  let q := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K))
  refine ⟨⟨q.symm l,σ⟩,?_⟩
  apply LinearEquiv.ext
  intro z
  change q (q.symm l) (gammaField σ z) = e z
  rw [q.apply_symm_apply]
  change e ((gammaField σ).symm (gammaField σ z)) = e z
  rw [LinearEquiv.symm_apply_apply]

private theorem coefficients_in_gamma [Finite K]
    (α : D →* MulAut (SL(2,K))) (μ : Representation (ZMod 2) D (Fin 2 → K))
    (hsemi : ∀ a c z, μ a (c • z) = fieldAction (α a) c • μ a z) :
    ∃ γ : D →* GammaL2 K,
      (∀ a z, gammaAction (γ a) z = μ a z) ∧
      (∀ a, (γ a).right = fieldAction (α a)) := by
  let b : D →* ((Fin 2 → K) ≃ₗ[ZMod 2] (Fin 2 → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 2 → K)).toMonoidHom.comp μ.asGroupHom
  have hb (a : D) : b a ∈ gammaAction.range :=
    gammaAction_exists (b a) (fieldAction (α a)) (hsemi a)
  let j := b.codRestrict gammaAction.range hb
  let γ := (MonoidHom.ofInjective gammaAction_injective).symm.toMonoidHom.comp j
  have he (a : D) : gammaAction (γ a) = b a :=
    congrArg Subtype.val ((MonoidHom.ofInjective gammaAction_injective).apply_symm_apply (j a))
  refine ⟨γ,fun a z => LinearEquiv.congr_fun (he a) z,?_⟩
  intro a
  apply RingEquiv.ext
  intro c
  obtain ⟨z,hz⟩ := (μ.apply_bijective a).surjective (fun _ => 1)
  have hh := gammaAction_semilinear (γ a) c z
  have hh' := hsemi a c z
  rw [he] at hh
  change μ a (c • z) = (γ a).right c • μ a z at hh
  rw [hh,hz] at hh'
  simpa using congrFun hh' 0
end Gamma

abbrev Field := OrthogonalFourMinus.FiniteModel.Field 1
abbrev Plane := Fin 2 → Field
abbrev Gamma := GammaL2 Field
abbrev LinearGroup := Matrix.GeneralLinearGroup (Fin 2) Field
local instance : Algebra (ZMod 2) Field := ZMod.algebra _ 2
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- The whole ambient action in compatible component and semilinear multiplicity
coordinates. Both kernels refer to the original subgroup, and the field
coefficient is shared by the two factors. -/
structure Coordinates (ρ : Representation (ZMod 2) D W) (H : Subgroup D) where
  component : H ≃* SL(2,Field)
  space : W ≃ₗ[ZMod 2] (Fin 2 → Plane)
  automorphism : D →* MulAut (SL(2,Field))
  coefficient : D →* Gamma
  automorphism_kernel : automorphism.ker = centralizer (H : Set D)
  component_marking : ∀ h : H, automorphism h = MulAut.conj (component h)
  coefficient_kernel : coefficient.ker = H
  same_field : ∀ a, (coefficient a).right = fieldAction (automorphism a)
  equivariant : ∀ a w i, space (ρ a w) i = ∑ j : Fin 2,
    (coefficient a).left.val i j • SL2AutomorphismNatural.action (automorphism a) (space w j)
  faithful : Function.Injective (automorphism.prod coefficient)

/-- Construct compatible coordinates for the entire ambient action from the
original doubled component action. No recognition premise for the ambient
image is used. -/
theorem coordinates_of_double
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (H : Subgroup D) [H.Normal]
    (hm : ChapterG.Section09.Quasiequivalent (ρ.comp H.subtype)
      ((SL2.BinarySmall.natural (K := Field)).prod (SL2.BinarySmall.natural (K := Field)))) :
    Nonempty (Coordinates ρ H) := by
  obtain ⟨e,f₀,hf₀⟩ := hm
  let f := f₀.trans (LinearEquiv.piFinTwo (ZMod 2) (fun _ : Fin 2 => Plane)).symm
  have hf (h : H) (w : W) : f (ρ h w) = fun i => (e h).val.mulVec (f w i) := by
    have hh := hf₀ h w
    change f₀ (ρ h w) = ((e h).val.mulVec (f₀ w).1,(e h).val.mulVec (f₀ w).2) at hh
    funext i
    fin_cases i
    · change (f₀ (ρ h w)).1 = (e h).val.mulVec (f₀ w).1
      exact congrArg Prod.fst hh
    · change (f₀ (ρ h w)).2 = (e h).val.mulVec (f₀ w).2
      exact congrArg Prod.snd hh
  obtain ⟨α,μ,hak,hmark,hker,hsemi,hact,hinj⟩ := ambient_coordinates ρ hρ H e f hf
  obtain ⟨γ,hγ,hfield⟩ := coefficients_in_gamma α μ hsemi
  have hγker : γ.ker = μ.asGroupHom.ker := by
    ext a
    simp only [MonoidHom.mem_ker]
    constructor
    · intro ha
      apply Units.ext
      apply LinearMap.ext
      intro z
      change μ a z = z
      rw [←hγ,ha,map_one]
      rfl
    · intro ha
      apply gammaAction_injective
      apply LinearEquiv.ext
      intro z
      rw [hγ,map_one]
      exact LinearMap.congr_fun (congrArg Units.val ha) z
  refine ⟨⟨e,f,α,γ,hak,hmark,hγker.trans hker,hfield,?_,?_⟩⟩
  · intro a w i
    rw [hact]
    apply Finset.sum_congr rfl
    intro j _
    rw [←hγ,gammaAction_apply]
    have he : (fun k : Fin 2 => (γ a).right ((Pi.single j (1 : Field) : Fin 2 → Field) k)) = Pi.single j 1 := by
      ext k
      by_cases h : j = k
      · subst k; simp
      · simp [Ne.symm h]
    rw [he]
    fin_cases j <;> simp [Matrix.mulVec,dotProduct]
  · intro a b hab
    apply hinj
    change (α a,μ.asGroupHom a) = (α b,μ.asGroupHom b)
    apply Prod.ext
    · exact congrArg (fun z : MulAut SL(2,Field) × Gamma => z.1) hab
    · apply Units.ext
      apply LinearMap.ext
      intro z
      change μ a z = μ b z
      rw [←hγ,←hγ,show γ a = γ b from congrArg Prod.snd hab]

namespace Coordinates
variable {ρ : Representation (ZMod 2) D W} {H : Subgroup D}
  (a : Coordinates ρ H)

/-- The coefficient image is the literal quotient by the original component. -/
def quotientEquiv [H.Normal] : D ⧸ H ≃* a.coefficient.range :=
  (QuotientGroup.quotientMulEquivOfEq a.coefficient_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange a.coefficient)

/-- Component centralizers have no field twist in the same coordinates. -/
theorem centralizer_field (c : centralizer (H : Set D)) :
    (a.coefficient c).right = 1 := by
  rw [a.same_field]
  have hc : a.automorphism c = 1 := MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ c.property)
  rw [hc,map_one]

/-- The original centralizer acts by actual F₄-linear two-by-two matrices. -/
def centralizerLinear : centralizer (H : Set D) →* LinearGroup where
  toFun c := (a.coefficient c).left
  map_one' := by change (a.coefficient 1).left = 1; rw [map_one]; rfl
  map_mul' c d := by
    change (a.coefficient ((c:D)*(d:D))).left = _
    rw [map_mul]
    change (a.coefficient c).left *
      Matrix.GeneralLinearGroup.coefficientAction Field (a.coefficient c).right (a.coefficient d).left = _
    rw [a.centralizer_field,map_one]
    rfl

/-- The linear centralizer marking uses the same coefficient matrices. -/
theorem centralizerLinear_apply (c : centralizer (H : Set D)) :
    a.centralizerLinear c = (a.coefficient c).left := by rfl

/-- No nonidentity element of the original centralizer disappears in its
linear coefficient action. -/
theorem centralizerLinear_injective : Function.Injective a.centralizerLinear := by
  intro c d hcd
  apply Subtype.ext
  apply a.faithful
  apply Prod.ext
  · have hc : a.automorphism c = 1 :=
      MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ c.property)
    have hd : a.automorphism d = 1 :=
      MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ d.property)
    exact hc.trans hd.symm
  · apply SemidirectProduct.ext hcd
    rw [a.centralizer_field,a.centralizer_field]

/-- The centralizer uses those exact matrices on the original whole module. -/
theorem centralizer_action (c : centralizer (H : Set D)) (w : W) (i : Fin 2) :
    a.space (ρ c w) i = ∑ j : Fin 2,
      (a.centralizerLinear c).val i j • a.space w j := by
  have hc : a.automorphism c = 1 :=
    MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ c.property)
  rw [a.equivariant,hc,map_one]
  rfl

end Coordinates

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear

open Subgroup Module Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D}

/-- An elementary actor of order greater than four has a nontrivial element
in the literal component centralizer. This uses Aut(SL₂(4))'s two-rank. -/
theorem actor_centralizer_ne_bot (a : Coordinates ρ H)
    (X : Subgroup D) [IsElementaryAbelian 2 X] (hX : 4 < Nat.card X) :
    (centralizer (H : Set D)).subgroupOf X ≠ ⊥ := by
  intro hz
  let β := a.automorphism.comp X.subtype
  have hbker : β.ker = (centralizer (H : Set D)).subgroupOf X := by
    ext x
    change a.automorphism x = 1 ↔ (x : D) ∈ centralizer (H : Set D)
    rw [←a.automorphism_kernel]
    rfl
  have hi : Function.Injective β := β.ker_eq_bot_iff.mp (hbker.trans hz)
  let : IsElementaryAbelian 2 β.range :=
    IsElementaryAbelian.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hr := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le
    (F := Field) (n := 2) (by decide) (GaloisField.card 2 2 (by decide))
  have hc := (primeRank_le_iff_elementary_card_le _).mp hr β.range inferInstance
  have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  change Nat.card β.range ≤ 4 at hc
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
