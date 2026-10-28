module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.LocalClosure
public import Theory.GroupTheory.PCoreImage
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.Quotient

/-!
# The actual action on the chosen local closure

The flag hypotheses are the preceding geometry of V₁ ≤ V₃. G.2.2 makes
the image of the local closure elementary abelian. Relative normality of
K=L₁ puts O₂(K) in O₂(H₁), and the proved core commutator kills its action.
The resulting representation is on the literal image in G₁/V₁ and has
actor K/O₂(K). No decomposition or semisimplicity is assumed here.

Source: Aschbacher--Smith 11.5.5(3), printed p.780, and its application
with H₁=G₁ at the start of 11.5.7.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The preceding flag geometry used by G.2.2. These are hypotheses about
the original seed and its local actor, with no closure conclusion. -/
structure ClosureFlag : Prop where
  point_nonzero : E.point ≠ ⊥
  point_le_seed : E.V₁ ≤ E.V₃
  point_ne_seed : E.V₁ ≠ E.V₃
  sylow_normalizes_point : (T : Subgroup G) ≤ E.G₁
  local_normalizes_seed : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G)
  seed_irreducible : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
    E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃

/-- The original quotient map, restricted to an arbitrary subgroup of G₁. -/
def tildeProjection (A : Subgroup G) (hA : A ≤ E.G₁) : A →* E.tilde A where
  toFun a := ⟨QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨a, hA a.property⟩,
    ⟨⟨a, hA a.property⟩, a.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁))
    (⟨a, hA a.property⟩ : E.G₁) ⟨b, hA b.property⟩)

theorem tildeProjection_surjective (A : Subgroup G) (hA : A ≤ E.G₁) :
    Function.Surjective (E.tildeProjection A hA) := by
  rintro ⟨y, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem tildeProjection_kernel (A : Subgroup G) (hA : A ≤ E.G₁) :
    (E.tildeProjection A hA).ker = E.V₁.subgroupOf A := by
  ext a
  change E.tildeProjection A hA a = 1 ↔ (a : G) ∈ E.V₁
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (⟨a, hA a.property⟩ : E.G₁)

/-- Ambient conjugation on the image of A in G₁/V₁. -/
def tildeConjugation (A J : Subgroup G) (hJ : J ≤ E.G₁)
    (hn : J ≤ normalizer (A : Set G)) : J →* MulAut (E.tilde A) :=
  (E.tilde A).normalizerMonoidHom.comp
    (((QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)).comp (inclusion hJ)).codRestrict
      (normalizer (E.tilde A : Set E.Tilde)) (by
        intro j
        apply mem_normalizer_iff.mpr
        intro x
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨(⟨j, hJ j.property⟩ : E.G₁) * a * ⟨j, hJ j.property⟩⁻¹,
            (mem_normalizer_iff.mp (hn j.property) a).mp ha, ?_⟩
          simp only [map_mul, map_inv, MonoidHom.comp_apply]
          rfl
        · intro hx
          obtain ⟨a, ha, he⟩ := hx
          refine ⟨(⟨j, hJ j.property⟩ : E.G₁)⁻¹ * a * ⟨j, hJ j.property⟩,
            ?_, ?_⟩
          · change (j : G)⁻¹ * (a : G) * (j : G) ∈ A
            simpa only [inv_inv] using
              (mem_normalizer_iff.mp (hn (J.inv_mem j.property)) a).mp ha
          · change QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) a =
              QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨j, hJ j.property⟩ * x *
                (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨j, hJ j.property⟩)⁻¹ at he
            simp only [map_mul, map_inv]
            rw [he]
            group))

theorem tildeConjugation_apply (A J : Subgroup G) (hJ : J ≤ E.G₁)
    (hn : J ≤ normalizer (A : Set G)) (j : J) (a : E.tilde A) :
    (E.tildeConjugation A J hJ hn j a : E.Tilde) =
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨j, hJ j.property⟩ * a *
        (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨j, hJ j.property⟩)⁻¹ := rfl

namespace ClosureFlag
variable {E} (f : E.ClosureFlag) (H₁ : Subgroup G)
    (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁)

include hLH in
theorem closure_le : E.localClosure H₁ ≤ H₁ :=
  conjugateSpanBy_le_self ((D.centralQuotientPreimage_le E.threeSpace).trans
    (D.le_sylow.trans (le_sup_right.trans hLH)))

include f hH hLH in
theorem elementary : IsElementaryAbelian 2 (E.tilde (E.localClosure H₁)) :=
  (E.closureSetup_hypothesis f.point_nonzero f.point_le_seed f.point_ne_seed
    f.sylow_normalizes_point f.local_normalizes_seed f.seed_irreducible H₁ hH hLH).tilde_U_elementary

/-- The underlying group is exactly the image in G₁/V₁. The parameters
retain the elementary-abelian structure constructed from the preceding flag. -/
def Space (_f : E.ClosureFlag) (H₁ : Subgroup G) (_hH : H₁ ≤ E.G₁)
    (_hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁) := Additive (E.tilde (E.localClosure H₁))

instance spaceAddCommGroup : AddCommGroup (f.Space H₁ hH hLH) := by
  letI := f.elementary H₁ hH hLH
  exact inferInstanceAs (AddCommGroup (Additive (E.tilde (E.localClosure H₁))))

instance spaceModule : Module (ZMod 2) (f.Space H₁ hH hLH) := by
  letI := f.elementary H₁ hH hLH
  exact inferInstanceAs (Module (ZMod 2) (Additive (E.tilde (E.localClosure H₁))))

instance spaceFinite : Finite (f.Space H₁ hH hLH) :=
  inferInstanceAs (Finite (Additive (E.tilde (E.localClosure H₁))))

/-- The full H₁ action on the literal binary closure quotient. -/
def action : Representation (ZMod 2) H₁ (f.Space H₁ hH hLH) where
  toFun h := (E.tildeConjugation (E.localClosure H₁) H₁ hH
    (le_normalizer_conjugateSpanBy _ _) h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (E.tildeConjugation (E.localClosure H₁) H₁ hH
      (le_normalizer_conjugateSpanBy _ _) 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (E.tildeConjugation (E.localClosure H₁) H₁ hH
      (le_normalizer_conjugateSpanBy _ _) (a * b) v.toMul) = _
    rw [map_mul]
    rfl

theorem action_apply (h : H₁) (v : f.Space H₁ hH hLH) :
    ((f.action H₁ hH hLH h v).toMul : E.Tilde) =
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨h, hH h.property⟩ * v.toMul *
        (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨h, hH h.property⟩)⁻¹ := rfl

variable (hK : E.K = E.L₁)

include hLH hK in
theorem K_le : E.K ≤ H₁ := hK ▸ le_sup_left.trans hLH

include hH hLH hK in
theorem core_le : E.K.pCoreIn 2 ≤ H₁.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (K_le H₁ hLH hK) (hH.trans E.G₁_normalizes_K)

include f hH hLH hK in
/-- The core commutator on the original groups, using only relative normality. -/
theorem commutator_core : ⁅E.localClosure H₁, E.K.pCoreIn 2⁆ ≤ E.V₁ :=
  (commutator_mono le_rfl (core_le H₁ hH hLH hK)).trans
    (E.localClosure_core_and_frattini f.point_nonzero f.point_le_seed f.point_ne_seed
      f.sylow_normalizes_point f.local_normalizes_seed f.seed_irreducible H₁ hH hLH).2.2.2.2

/-- The action restricted to K, before passing to its two-core quotient. -/
def restrictedAction : Representation (ZMod 2) E.K
    (f.Space H₁ hH hLH) :=
  (f.action H₁ hH hLH).comp (inclusion (K_le H₁ hLH hK))

theorem core_le_kernel : pCore 2 E.K ≤ (f.restrictedAction H₁ hH hLH hK).ker := by
  intro k hk
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  obtain ⟨u, hu⟩ := E.tildeProjection_surjective (E.localClosure H₁)
    ((closure_le H₁ hLH).trans hH) v.toMul
  let ui : E.G₁ := ⟨u, hH (closure_le H₁ hLH u.property)⟩
  let ki : E.G₁ := ⟨k, E.K_le_G₁ k.property⟩
  let q := QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
  have hc : ⁅ui, ki⁆ ∈ E.V₁.subgroupOf E.G₁ :=
    f.commutator_core H₁ hH hLH hK
      (commutator_mem_commutator u.property (mem_map_of_mem E.K.subtype hk))
  have he : q ui * q ki = q ki * q ui := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  change q ki * (v.toMul : E.Tilde) * (q ki)⁻¹ = (v.toMul : E.Tilde)
  have hv : q ui = (v.toMul : E.Tilde) := congrArg Subtype.val hu
  rw [← hv, ← he, mul_inv_cancel_right]

/-- The actual K/O₂(K) action, with no kernel hypothesis left over. -/
def quotientAction : Representation (ZMod 2) (E.K ⧸ pCore 2 E.K)
    (f.Space H₁ hH hLH) :=
  Representation.quotientOfLEKer (f.restrictedAction H₁ hH hLH hK) (pCore 2 E.K)
    (f.core_le_kernel H₁ hH hLH hK)

/-- Representatives in K act through the original quotient of G₁ by V₁. -/
theorem quotientAction_apply (k : E.K)
    (v : f.Space H₁ hH hLH) :
    ((f.quotientAction H₁ hH hLH hK (QuotientGroup.mk' (pCore 2 E.K) k) v).toMul : E.Tilde) =
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨k, E.K_le_G₁ k.property⟩ * v.toMul *
        (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨k, E.K_le_G₁ k.property⟩)⁻¹ := rfl

end ClosureFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
