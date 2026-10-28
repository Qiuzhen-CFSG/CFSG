module

public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Two-cores of local field extensions

Let L map onto the actual PSL₂(F), with two-group kernel, and let A act on L
compatibly with a faithful group of coefficientwise field automorphisms.
The action of L ⋊ A on the quotient has exactly the embedded kernel as its
kernel: a field automorphism cannot be inner unless it is trivial. Since
an automorphism subgroup containing Inn(PSL₂(F)) has trivial two-core,
the embedded kernel is the entire two-core of the extension.

No assumption that A is a two-group is needed, so this applies in particular
to the two-group extensions on printed p.264 of Aschbacher--Smith F.1.12.
The local-map and kernel identifications are explicit inputs for either of
the two standard G₂ locals. This is a conditional local result, not an
assertion that all abstract G₂ automorphisms are inner times field.
-/

@[expose] public section

open scoped MatrixGroups
open Atlas.RankOneFieldAutomorphisms Theory.GroupTheory
namespace Atlas.G2.LieAutomorphismExtensions
variable {F L A : Type*} [Field F] [Group L] [Group A]
  (π : L →* PSL(2,F)) (β : A →* MulAut L) (σ : A →* (F ≃+* F))
  (heq : ∀ a x, π (β a x) = fieldEquivPSL 2 (σ a) (π x))

/-- The induced conjugation and field action on the actual rank-one quotient. -/
def localQuotientAction : L ⋊[β] A →* MulAut PSL(2,F) :=
  SemidirectProduct.lift (MulAut.conj.comp π) (pslFieldAction.comp σ) (by
    intro a
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    change π (β a x) * y * (π (β a x))⁻¹ =
      fieldEquivPSL 2 (σ a) (π x * (fieldEquivPSL 2 (σ a)).symm y * (π x)⁻¹)
    rw [heq]
    simp)

/-- The action kernel is exactly the original local kernel. -/
theorem localQuotientAction_kernel [CharP F 2] (hσ : Function.Injective σ) :
    (localQuotientAction π β σ heq).ker = π.ker.map (SemidirectProduct.inl : L →* L ⋊[β] A) := by
  have hc := conj_injective_of_center_eq_bot (psl_center_eq_bot (F := F))
  ext z
  constructor
  · intro hz
    have hz' : MulAut.conj (π z.left) * fieldEquivPSL 2 (σ z.right) = 1 := hz
    have hf : fieldEquivPSL 2 (σ z.right) = (MulAut.conj (π z.left))⁻¹ :=
      eq_inv_of_mul_eq_one_right hz'
    have hs : σ z.right = 1 := field_eq_one_of_PSL_inner _ ((π z.left)⁻¹) (by
      simpa only [map_inv] using hf)
    have hr : z.right = 1 := hσ (hs.trans σ.map_one.symm)
    have hl : π z.left = 1 := by
      apply hc
      simpa only [hr, map_one, show fieldEquivPSL 2 (1 : F ≃+* F) = 1 from
        pslFieldAction.map_one, mul_one] using hz'
    refine ⟨z.left, hl, ?_⟩
    ext <;> simp [hr]
  · rintro ⟨x, hx, rfl⟩
    change MulAut.conj (π x) * fieldEquivPSL 2 (σ 1) = 1
    have hx' : π x = 1 := hx
    simp only [hx', map_one, one_mul]
    exact pslFieldAction.map_one

include heq in
/-- Extending the local by faithful field automorphisms does not enlarge its two-core. -/
theorem localExtension_twoCore [Finite F] [CharP F 2] [Finite L] [Finite A]
    (hπ : Function.Surjective π) (hσ : Function.Injective σ)
    (hk : IsPGroup 2 π.ker) :
    pCore 2 (L ⋊[β] A) = π.ker.map (SemidirectProduct.inl : L →* L ⋊[β] A) := by
  let : Finite (L ⋊[β] A) := Finite.of_equiv (L × A)
    SemidirectProduct.equivProd.symm
  let a := localQuotientAction π β σ heq
  have hker := localQuotientAction_kernel π β σ heq hσ
  have hi : ∀ x : PSL(2,F), MulAut.conj x ∈ a.range := by
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    exact ⟨SemidirectProduct.inl y, SemidirectProduct.lift_inl _ _ _ _⟩
  have hak : IsPGroup 2 a.ker := by
    rw [show a.ker = _ from hker]
    exact hk.map _
  exact (core_eq_kernel_of_action 2
    (conj_injective_of_center_eq_bot psl_center_eq_bot) psl_twoCore_eq_bot a hi hak).trans hker
/-- Inner action on the quotient forces the field component to be trivial. -/
theorem localQuotientAction_inner_iff [CharP F 2] (hσ : Function.Injective σ)
    (z : L ⋊[β] A) :
    (∃ g : PSL(2,F), localQuotientAction π β σ heq z = MulAut.conj g) ↔
      z.right = 1 := by
  constructor
  · rintro ⟨g, hg⟩
    change MulAut.conj (π z.left) * fieldEquivPSL 2 (σ z.right) = MulAut.conj g at hg
    have hf : fieldEquivPSL 2 (σ z.right) = MulAut.conj ((π z.left)⁻¹ * g) := by
      rw [map_mul, map_inv]
      exact (eq_inv_mul_iff_mul_eq).mpr hg
    have hs : σ z.right = 1 := field_eq_one_of_PSL_inner _ _ hf
    exact hσ (hs.trans σ.map_one.symm)
  · intro hr
    refine ⟨π z.left, ?_⟩
    change MulAut.conj (π z.left) * pslFieldAction (σ z.right) = _
    simp only [hr, map_one, mul_one]

include heq in
/-- The extension two-core is the image of the original local two-core. -/
theorem localExtension_twoCore_eq_map [Finite F] [CharP F 2] [Finite L] [Finite A]
    (hπ : Function.Surjective π) (hσ : Function.Injective σ)
    (hk : IsPGroup 2 π.ker) :
    pCore 2 (L ⋊[β] A) =
      (pCore 2 L).map (SemidirectProduct.inl : L →* L ⋊[β] A) := by
  have hb : pCore 2 L = π.ker := by
    have h := π.comap_pCore_of_ker_isPGroup hπ hk
    rw [psl_twoCore_eq_bot] at h
    exact h.symm
  rw [localExtension_twoCore π β σ heq hπ hσ hk, hb]

end Atlas.G2.LieAutomorphismExtensions
