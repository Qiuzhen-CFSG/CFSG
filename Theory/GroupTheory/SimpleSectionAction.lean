module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Automorphisms induced on actual simple sections

For a subnormal upper subgroup U and a normal subgroup V of U, only the
ambient elements normalizing both U and the image of V act on U/V. We retain
this stabilizer, its literal quotient action, and its representative equation.
The chosen simple-carrier isomorphism transports the action, including its
image and the join with inner automorphisms. For a nonabelian simple carrier
the inner copy is faithful. The separate split extension retains cyclic
factors, whose inner copy would be trivial.

This is the composition-section convention used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.11, printed pp.212--214.
-/

@[expose] public section

open Subgroup
namespace ChiefFactor.SimpleSection
universe u v w
variable {G : Type u} {S : Type v} [Group G] [Group S]

instance kernel_normal (s : SimpleSection G S) : s.kernel.Normal := s.normal

/-- The lower endpoint as a subgroup of the ambient group. -/
def kernelImage (s : SimpleSection G S) : Subgroup G := s.kernel.map s.subgroup.subtype

/-- The elements of T normalizing both endpoints of the section. -/
def stabilizer (s : SimpleSection G S) (T : Subgroup G) : Subgroup G :=
  T ⊓ (normalizer s.subgroup ⊓ normalizer s.kernelImage)

/-- Conjugation on the upper endpoint by the section stabilizer. -/
def upperAction (s : SimpleSection G S) (T : Subgroup G) :
    s.stabilizer T →* MulAut s.subgroup :=
  s.subgroup.normalizerMonoidHom.comp (inclusion (fun _ h => h.2.1))

theorem upperAction_kernel (s : SimpleSection G S) (T : Subgroup G)
    (g : s.stabilizer T) : s.kernel.map (s.upperAction T g).toMonoidHom = s.kernel := by
  have hmem (x : s.subgroup) : x ∈ s.kernel ↔ s.upperAction T g x ∈ s.kernel := by
    have hi (y : s.subgroup) : y ∈ s.kernel ↔ (y : G) ∈ s.kernelImage := by
      exact (mem_map_iff_mem s.subgroup.subtype_injective).symm
    rw [hi, hi]
    exact (mem_normalizer_iff.mp g.property.2.2) x
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hmem y).mp hy
  · intro hx
    exact ⟨(s.upperAction T g).symm x,
      (hmem _).mpr (by simpa using hx), (s.upperAction T g).apply_symm_apply x⟩

/-- The literal action on U/V. -/
def quotientAction (s : SimpleSection G S) (T : Subgroup G) :
    s.stabilizer T →* MulAut (s.subgroup ⧸ s.kernel) where
  toFun g := QuotientGroup.congr _ _ (s.upperAction T g) (s.upperAction_kernel T g)
  map_one' := by
    ext x
    induction x using Quotient.inductionOn with | h x =>
      change QuotientGroup.mk' s.kernel (s.upperAction T 1 x) = QuotientGroup.mk' s.kernel x
      rw [map_one]
      rfl
  map_mul' g h := by
    ext x
    induction x using Quotient.inductionOn with | h x =>
      change QuotientGroup.mk' s.kernel (s.upperAction T (g * h) x) =
        QuotientGroup.mk' s.kernel (s.upperAction T g (s.upperAction T h x))
      rw [map_mul]
      rfl

theorem quotientAction_mk (s : SimpleSection G S) (T : Subgroup G)
    (g : s.stabilizer T) (x : s.subgroup) :
    s.quotientAction T g (QuotientGroup.mk' s.kernel x) =
      QuotientGroup.mk' s.kernel
        ⟨(g : G) * x * (g : G)⁻¹, (mem_normalizer_iff.mp g.property.2.1 x).mp x.property⟩ := rfl

/-- The same induced action on the specified simple carrier. -/
def action (s : SimpleSection G S) (T : Subgroup G) : s.stabilizer T →* MulAut S :=
  (MulAut.congr s.equiv).toMonoidHom.comp (s.quotientAction T)

theorem action_equiv_mk (s : SimpleSection G S) (T : Subgroup G)
    (g : s.stabilizer T) (x : s.subgroup) :
    s.action T g (s.equiv (QuotientGroup.mk' s.kernel x)) =
      s.equiv (QuotientGroup.mk' s.kernel
        ⟨(g : G) * x * (g : G)⁻¹, (mem_normalizer_iff.mp g.property.2.1 x).mp x.property⟩) := by
  change s.equiv (s.quotientAction T g (s.equiv.symm (s.equiv _))) = _
  rw [s.equiv.symm_apply_apply, s.quotientAction_mk]

/-- Inn(S) together with the automorphisms actually induced by T. -/
def extension (s : SimpleSection G S) (T : Subgroup G) : Subgroup (MulAut S) :=
  MulAut.innerSubgroup S ⊔ (s.action T).range

/-- The split extension retains S even when S is cyclic and Inn(S) is trivial. -/
abbrev splitExtension (s : SimpleSection G S) (T : Subgroup G) :=
  S ⋊[(s.action T).range.subtype] (s.action T).range


instance splitExtension_finite [Finite S] (s : SimpleSection G S) (T : Subgroup G) :
    Finite (s.splitExtension T) :=
  Finite.of_equiv (S × (s.action T).range) SemidirectProduct.equivProd.symm

/-- The extension on the literal quotient carrier. -/
def quotientExtension (s : SimpleSection G S) (T : Subgroup G) :
    Subgroup (MulAut (s.subgroup ⧸ s.kernel)) :=
  MulAut.innerSubgroup (s.subgroup ⧸ s.kernel) ⊔ (s.quotientAction T).range

theorem map_quotientExtension (s : SimpleSection G S) (T : Subgroup G) :
    (s.quotientExtension T).map (MulAut.congr s.equiv).toMonoidHom = s.extension T := by
  rw [quotientExtension, Subgroup.map_sup, MulAut.map_innerSubgroup_congr,
    MonoidHom.map_range]
  rfl

/-- The quotient and chosen simple-carrier models give the same actual extension. -/
def quotientExtensionEquiv (s : SimpleSection G S) (T : Subgroup G) :
    s.quotientExtension T ≃* s.extension T :=
  ((MulAut.congr s.equiv).subgroupMap (s.quotientExtension T)).trans
    (MulEquiv.subgroupCongr (s.map_quotientExtension T))

theorem center_eq_bot (s : SimpleSection G S) (hn : ¬ IsMulCommutative S) :
    center S = ⊥ := by
  let := s.simple
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact False.elim (hn (center_eq_top_iff.mp h))

/-- A nonabelian simple factor is faithfully its inner subgroup. -/
noncomputable def innerEquiv (s : SimpleSection G S) (hn : ¬ IsMulCommutative S) :
    S ≃* MulAut.innerSubgroup S := by
  apply MonoidHom.ofInjective
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : S →* MulAut S).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hc : x ∈ center S := by
    apply mem_center_iff.mpr
    intro y
    have hy := MulEquiv.congr_fun hx y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [s.center_eq_bot hn, mem_bot] using hc

/-- The distinguished faithful copy of the nonabelian simple factor. -/
noncomputable def factorEmbedding (s : SimpleSection G S) (T : Subgroup G)
    (hn : ¬ IsMulCommutative S) : S →* s.extension T :=
  (inclusion le_sup_left).comp (s.innerEquiv hn).toMonoidHom

theorem factorEmbedding_injective (s : SimpleSection G S) (T : Subgroup G)
    (hn : ¬ IsMulCommutative S) : Function.Injective (s.factorEmbedding T hn) :=
  (inclusion_injective le_sup_left).comp (s.innerEquiv hn).injective

theorem factorEmbedding_apply (s : SimpleSection G S) (T : Subgroup G)
    (hn : ¬ IsMulCommutative S) (x : S) :
    (s.factorEmbedding T hn x : MulAut S) = MulAut.conj x := rfl

/-- The quotient map followed by the chosen identification with S. -/
def projection (s : SimpleSection G S) : s.subgroup →* S :=
  s.equiv.toMonoidHom.comp (QuotientGroup.mk' s.kernel)

theorem projection_surjective (s : SimpleSection G S) : Function.Surjective s.projection :=
  s.equiv.surjective.comp (QuotientGroup.mk'_surjective s.kernel)

theorem projection_eq_one (s : SimpleSection G S) (x : s.subgroup) :
    s.projection x = 1 ↔ x ∈ s.kernel := by
  change s.equiv (QuotientGroup.mk' s.kernel x) = 1 ↔ _
  rw [← s.equiv.map_one, s.equiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem action_projection (s : SimpleSection G S) (T : Subgroup G)
    (g : s.stabilizer T) (x : s.subgroup) :
    s.action T g (s.projection x) = s.projection (s.upperAction T g x) :=
  s.action_equiv_mk T g x

end ChiefFactor.SimpleSection
