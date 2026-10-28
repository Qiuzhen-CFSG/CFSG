module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Basic
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Splitting the entire doubled SL₂(4) action

The semilinear coordinates determine an actual isomorphism from the ambient
acting group to SL₂(4) semidirect its coefficient image. Surjectivity is
constructive: lift a coefficient, then remove its inner component. The
isomorphism retains the original component, every coefficient and the action
on the original whole module. It is not an identification by group order.

The component centralizer is exactly the linear kernel in that coefficient
image. A one-dimensional binary fixed space forces the original actor to
induce the nonidentity field automorphism: otherwise scalar multiples of its
nonzero fixed point would give four fixed vectors. Consequently the component
and its centralizer have index two, and adjoining the actual actor generates
the whole group. The centralizer and its coefficient kernel inherit trivial
two-core from the ambient group.

`CatalogueExclusion.source_large_coefficient_remainder_of_mixed_size` applies
all these facts to the original flag. Classification of the coefficient
subgroup and the unmarked exchanged constituents remains necessary; the
semidirect description alone is not the G.11.2 catalogue.

Source: Aschbacher--Smith D.3.21, printed pp.206--207; G.11.8, printed
pp.368--369; and 14.4.2, printed pp.1006--1007 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Module Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
open Representation.SL2AutomorphismNatural
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)
local instance : Algebra (ZMod 2) Field := ZMod.algebra _ 2

/-- The field projection on the literal coefficient image. -/
def coefficientField : a.coefficient.range →* (Field ≃+* Field) :=
  SemidirectProduct.rightHom.comp a.coefficient.range.subtype

/-- The field projection evaluates on the original semilinear coefficient. -/
theorem coefficientField_apply (b : a.coefficient.range) :
    a.coefficientField b = (b : Gamma).right := by rfl

/-- The whole-action model, with the field action induced by its coefficients. -/
abbrev SplitGroup := SL(2,Field) ⋊[fieldHom.comp a.coefficientField] a.coefficient.range

private def innerParameters : D →* Parameters (F := Field) :=
  parameterEquiv.symm.toMonoidHom.comp a.automorphism

private theorem parameters_component (h : H) :
    a.innerParameters h = SemidirectProduct.inl (a.component h) := by
  apply parameterEquiv.injective
  change parameterEquiv (parameterEquiv.symm (a.automorphism h)) = _
  rw [parameterEquiv.apply_symm_apply,a.component_marking]
  change MulAut.conj (a.component h) = parameterAut (SemidirectProduct.inl (a.component h))
  exact (SemidirectProduct.lift_inl _ _ _ _).symm

private def splitHom : D →* a.SplitGroup where
  toFun g := ⟨(a.innerParameters g).left,a.coefficient.rangeRestrict g⟩
  map_one' := by apply SemidirectProduct.ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change (a.innerParameters (g*h)).left =
        (a.innerParameters g).left *
          fieldHom (a.coefficient g).right (a.innerParameters h).left
      rw [map_mul,a.same_field]
      rfl
    · exact a.coefficient.rangeRestrict.map_mul g h

private theorem splitHom_component (h : H) :
    a.splitHom h = SemidirectProduct.inl (a.component h) := by
  apply SemidirectProduct.ext
  · change (a.innerParameters h).left = a.component h
    exact congrArg SemidirectProduct.left (a.parameters_component h)
  · apply Subtype.ext
    exact MonoidHom.mem_ker.mp (a.coefficient_kernel.symm ▸ h.property)

private theorem splitHom_bijective : Function.Bijective a.splitHom := by
  constructor
  · intro g h he
    have hleft := congrArg SemidirectProduct.left he
    have hcoef : a.coefficient g = a.coefficient h :=
      congrArg (fun z : a.SplitGroup => (z.right : Gamma)) he
    apply a.faithful
    apply Prod.ext ?_ hcoef
    apply parameterEquiv.symm.injective
    change a.innerParameters g = a.innerParameters h
    change (a.innerParameters g).left = (a.innerParameters h).left at hleft
    apply SemidirectProduct.ext hleft
    change fieldAction (a.automorphism g) = fieldAction (a.automorphism h)
    rw [←a.same_field,←a.same_field,hcoef]
  · intro z
    obtain ⟨g,hg⟩ := a.coefficient.rangeRestrict_surjective z.right
    let h : H := a.component.symm (z.left * (a.innerParameters g).left⁻¹)
    refine ⟨(h:D)*g,?_⟩
    rw [map_mul,a.splitHom_component]
    apply SemidirectProduct.ext
    · change a.component h * (a.innerParameters g).left = z.left
      dsimp only [h]
      rw [a.component.apply_symm_apply,inv_mul_cancel_right]
    · change 1 * a.coefficient.rangeRestrict g = z.right
      simpa only [one_mul] using hg

/-- Explicit recognition of the entire ambient action over its coefficient image. -/
def splitEquiv : D ≃* a.SplitGroup := MulEquiv.ofBijective a.splitHom a.splitHom_bijective

/-- The original component is the first factor under the same marking. -/
theorem splitEquiv_component (h : H) :
    a.splitEquiv h = SemidirectProduct.inl (a.component h) := a.splitHom_component h

/-- The second coordinate is the original coefficient quotient map. -/
theorem splitEquiv_coefficient (g : D) :
    (a.splitEquiv g).right = a.coefficient.rangeRestrict g := by rfl

/-- Both factors describe every operator on the original whole module. -/
theorem splitEquiv_action (g : D) (w : W) (i : Fin 2) :
    a.space (ρ g w) i = ∑ j : Fin 2,
      ((a.splitEquiv g).right : Gamma).left.val i j •
        (a.splitEquiv g).left.val.mulVec
          (fun k => a.coefficientField (a.splitEquiv g).right (a.space w j k)) := by
  rw [a.equivariant]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change natural (a.innerParameters g) (a.space w j) = _
  change (a.innerParameters g).left.val.mulVec
    (fun k => (a.innerParameters g).right (a.space w j k)) = _
  rw [show (a.innerParameters g).right = (a.coefficient g).right from (a.same_field g).symm]
  rfl

/-- Removing the inner component gives an actual section of the coefficient map. -/
def coefficientLift : a.coefficient.range →* D :=
  a.splitEquiv.symm.toMonoidHom.comp SemidirectProduct.inr

/-- The section lifts the literal coefficient, not an abstract quotient element. -/
theorem coefficientLift_marking (b : a.coefficient.range) :
    a.coefficient.rangeRestrict (a.coefficientLift b) = b := by
  have hh := congrArg SemidirectProduct.right (a.splitEquiv.apply_symm_apply
    (SemidirectProduct.inr b))
  exact hh

private theorem coefficientLift_parameters (b : a.coefficient.range) :
    a.innerParameters (a.coefficientLift b) = SemidirectProduct.inr (a.coefficientField b) := by
  apply SemidirectProduct.ext
  · change (a.splitEquiv (a.coefficientLift b)).left = 1
    exact congrArg SemidirectProduct.left (a.splitEquiv.apply_symm_apply
      (SemidirectProduct.inr b))
  · change fieldAction (a.automorphism (a.coefficientLift b)) = _
    rw [←a.same_field]
    exact congrArg (fun c : a.coefficient.range => (c : Gamma).right)
      (a.coefficientLift_marking b)

/-- Linear coefficients lift into the original component centralizer. -/
theorem coefficientLift_centralizer (b : a.coefficient.range)
    (hb : a.coefficientField b = 1) : a.coefficientLift b ∈ centralizer (H : Set D) := by
  rw [←a.automorphism_kernel,MonoidHom.mem_ker]
  apply parameterEquiv.symm.injective
  change a.innerParameters (a.coefficientLift b) = parameterEquiv.symm 1
  rw [a.coefficientLift_parameters,hb,map_one,map_one]

private def centralizerCoefficients : centralizer (H : Set D) →* a.coefficientField.ker :=
  (a.coefficient.rangeRestrict.comp (centralizer (H : Set D)).subtype).codRestrict
    a.coefficientField.ker (fun c => a.centralizer_field c)

private theorem centralizerCoefficients_bijective : Function.Bijective a.centralizerCoefficients := by
  constructor
  · intro c d he
    apply Subtype.ext
    apply a.faithful
    apply Prod.ext
    · have hc : a.automorphism c = 1 :=
        MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ c.property)
      have hd : a.automorphism d = 1 :=
        MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ d.property)
      exact hc.trans hd.symm
    · exact congrArg (fun z : a.coefficientField.ker => ((z : a.coefficient.range) : Gamma)) he
  · intro b
    refine ⟨⟨a.coefficientLift b,a.coefficientLift_centralizer b b.property⟩,?_⟩
    apply Subtype.ext
    exact a.coefficientLift_marking b

/-- The component centralizer is exactly the field kernel in the coefficient image. -/
def centralizerCoefficientEquiv : centralizer (H : Set D) ≃* a.coefficientField.ker :=
  MulEquiv.ofBijective a.centralizerCoefficients a.centralizerCoefficients_bijective

/-- The original centralizer fills precisely the linear part of the coefficient image. -/
theorem centralizerLinear_range : a.centralizerLinear.range =
    a.coefficient.range.comap (SemidirectProduct.inl : LinearGroup →* Gamma) := by
  ext b
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c,?_⟩
    apply SemidirectProduct.ext (a.centralizerLinear_apply c).symm (a.centralizer_field c)
  · rintro ⟨g,hg⟩
    let c : a.coefficientField.ker := ⟨⟨SemidirectProduct.inl b,⟨g,hg⟩⟩,rfl⟩
    obtain ⟨d,hd⟩ := a.centralizerCoefficients_bijective.surjective c
    refine ⟨d,?_⟩
    rw [a.centralizerLinear_apply]
    exact congrArg (fun z : a.coefficientField.ker => ((z : a.coefficient.range) : Gamma).left) hd

/-- The common field action of both tensor factors on the whole original group. -/
def ambientField : D →* (Field ≃+* Field) :=
  a.coefficientField.comp a.coefficient.rangeRestrict

/-- The ambient field map is the field part of the same coefficient. -/
theorem ambientField_apply (g : D) :
    a.ambientField g = (a.coefficient g).right := by rfl

/-- Trivial field action means membership in the component-centralizer product. -/
theorem ambientField_kernel : a.ambientField.ker = H ⊔ centralizer (H : Set D) := by
  apply le_antisymm
  · intro g hg
    let h : H := a.component.symm (a.splitEquiv g).left
    let b := (a.splitEquiv g).right
    have hc : a.coefficientLift b ∈ centralizer (H : Set D) :=
      a.coefficientLift_centralizer b hg
    have he : (h:D) * a.coefficientLift b = g := by
      apply a.splitEquiv.injective
      rw [map_mul,a.splitEquiv_component]
      change SemidirectProduct.inl (a.component h) *
        a.splitEquiv (a.splitEquiv.symm (SemidirectProduct.inr b)) = a.splitEquiv g
      rw [a.splitEquiv.apply_symm_apply]
      dsimp only [h,b]
      rw [a.component.apply_symm_apply,SemidirectProduct.inl_left_mul_inr_right]
    exact he ▸ (H ⊔ centralizer (H : Set D)).mul_mem
      ((show H ≤ H ⊔ centralizer (H : Set D) from le_sup_left) h.property)
      ((show centralizer (H : Set D) ≤ H ⊔ centralizer (H : Set D) from le_sup_right) hc)
  · apply sup_le
    · intro h hh
      change (a.coefficient h).right = 1
      rw [MonoidHom.mem_ker.mp (a.coefficient_kernel.symm ▸ hh)]
      rfl
    · intro c hc
      exact a.centralizer_field ⟨c,hc⟩

/-- The original whole action has the same scalar twist as its coefficient image. -/
theorem scalar_action (g : D) (c : Field) (w : W) :
    a.space (ρ g (a.space.symm (c • a.space w))) =
      (a.coefficient g).right c • a.space (ρ g w) := by
  funext i
  rw [a.equivariant,a.space.apply_symm_apply]
  change _ = (a.coefficient g).right c • a.space (ρ g w) i
  rw [a.equivariant,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (a.coefficient g).left.val i j • action (a.automorphism g) (c • a.space w j) = _
  rw [action_semilinear,←a.same_field,smul_comm]

/-- A single binary fixed line forces a nontrivial field automorphism in the actor. -/
theorem actor_field_nontrivial [FiniteDimensional (ZMod 2) W]
    (X : Subgroup D) (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    ∃ x : X, a.ambientField x ≠ 1 := by
  by_contra! hh
  let : Finite W := Module.finite_of_finite (ZMod 2)
  have hvf : v ∈ BinaryOffender.fixedSpace ρ X := hf ▸ Submodule.mem_span_singleton_self v
  let f : Field → BinaryOffender.fixedSpace ρ X := fun c =>
    ⟨a.space.symm (c • a.space v),by
      intro x
      change ρ (x:D) _ = _
      apply a.space.injective
      rw [a.scalar_action]
      have hx' : (a.coefficient x).right = 1 := hh x
      have hvx : ρ (x:D) v = v := hvf x
      rw [hx',hvx,a.space.apply_symm_apply]
      rfl⟩
  have hne : a.space v ≠ 0 := by simpa using hv
  have hi : Function.Injective f := by
    intro c d he
    apply smul_left_injective Field hne
    exact a.space.symm.injective (congrArg Subtype.val he)
  have hb := Nat.card_le_card_of_injective f hi
  have hc : Nat.card (BinaryOffender.fixedSpace ρ X) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hf,
      finrank_span_singleton hv,Nat.card_zmod,pow_one]
  rw [hc,GaloisField.card 2 2 (by decide)] at hb
  norm_num at hb

private theorem field_automorphism_card : Nat.card (Field ≃+* Field) = 2 := by
  let e := SL2FourNatural.fieldEquiv
  let f : (Field ≃+* Field) ≃ (SL2FourNatural.F ≃+* SL2FourNatural.F) := {
    toFun σ := (e.trans σ).trans e.symm
    invFun σ := (e.symm.trans σ).trans e
    left_inv σ := by apply RingEquiv.ext; intro x; simp
    right_inv σ := by apply RingEquiv.ext; intro x; simp }
  exact (Nat.card_congr f).trans SL2FourNatural.SemilinearNormalizer.automorphism_card

/-- The original actor induces the full automorphism group of the field of four elements. -/
theorem actor_field_surjective [FiniteDimensional (ZMod 2) W]
    (X : Subgroup D) (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    Function.Surjective (a.ambientField.comp X.subtype) := by
  let β := a.ambientField.comp X.subtype
  let : Fact (Nat.card (Field ≃+* Field)).Prime := ⟨by rw [field_automorphism_card]; decide⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card β.range with hb | ht
  · obtain ⟨x,hx⟩ := a.actor_field_nontrivial X v hv hf
    exact (hx (Subgroup.mem_bot.mp (hb ▸ (show β x ∈ β.range from ⟨x,rfl⟩)))).elim
  · exact MonoidHom.range_eq_top.mp ht

include a in
/-- The original component, centralizer and actor generate the whole ambient group. -/
theorem generated_by_component_centralizer_actor [FiniteDimensional (ZMod 2) W]
    (X : Subgroup D) (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    H ⊔ centralizer (H : Set D) ⊔ X = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x,hx⟩ := actor_field_surjective a X v hv hf (a.ambientField g)
  have hk : g * (x:D)⁻¹ ∈ a.ambientField.ker := by
    change a.ambientField (g * (x:D)⁻¹) = 1
    rw [map_mul,map_inv,show a.ambientField x = a.ambientField g from hx,mul_inv_cancel]
  rw [a.ambientField_kernel] at hk
  have hh := (H ⊔ centralizer (H : Set D) ⊔ X).mul_mem
    ((show H ⊔ centralizer (H : Set D) ≤ H ⊔ centralizer (H : Set D) ⊔ X from le_sup_left) hk)
    ((show X ≤ H ⊔ centralizer (H : Set D) ⊔ X from le_sup_right) x.property)
  simpa only [inv_mul_cancel_right] using hh

include a in
/-- The component-centralizer product is the exact subgroup of index two. -/
theorem component_centralizer_index [FiniteDimensional (ZMod 2) W]
    (X : Subgroup D) (v : W) (hv : v ≠ 0)
    (hf : BinaryOffender.fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    (H ⊔ centralizer (H : Set D)).index = 2 := by
  have hs : Function.Surjective a.ambientField :=
    Function.Surjective.of_comp (a.actor_field_surjective X v hv hf)
  rw [←a.ambientField_kernel,Subgroup.index_ker,MonoidHom.range_eq_top.mpr hs,
    Nat.card_congr (Subgroup.topEquiv (G := Field ≃+* Field)).toEquiv,field_automorphism_card]

include a in
/-- Trivial ambient two-core descends to the actual normal centralizer. -/
theorem centralizer_twoCore (hc : pCore 2 D = ⊥) :
    pCore 2 (centralizer (H : Set D)) = ⊥ := by
  let : (centralizer (H : Set D)).Normal := a.automorphism_kernel ▸ inferInstance
  rw [Subgroup.pCore_eq_comap_of_normal,hc]
  exact (centralizer (H : Set D)).subtype.ker_eq_bot_iff.mpr Subtype.val_injective

/-- The linear coefficient kernel inherits the same trivial two-core. -/
theorem coefficient_kernel_twoCore (hc : pCore 2 D = ⊥) :
    pCore 2 a.coefficientField.ker = ⊥ := by
  rw [←pCore_map_iso 2 a.centralizerCoefficientEquiv,a.centralizer_twoCore hc,Subgroup.map_bot]

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
