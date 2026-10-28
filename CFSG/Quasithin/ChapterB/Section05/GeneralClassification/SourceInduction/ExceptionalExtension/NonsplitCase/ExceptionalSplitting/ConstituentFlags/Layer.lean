module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Preparation
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.Order.OrderIsoNat

/-!
# Chief flags from a single natural layer

A surjective equivariant map from an invariant subspace to the natural
SL₃(2)-module, with central kernel and central upper quotient, gives a chief
flag with precisely one noncentral factor. Saturated chains refine the two
central intervals; the natural section itself is a cover by irreducibility.

Intersect the upper subspace with any submodule. Its image in the natural
module is either everything or zero. The first case gives another such layer
and proves faithfulness on that submodule from the natural action. In the
second case all displacements are central, so perfectness makes the whole
submodule central. Indecomposability is not needed for this construction.

The finite saturated-chain construction follows `InvariantFlags.lean` in
B.5.9's natural-component development. The present consumer uses the literal
`BinaryOffender.sectionRepresentation` convention throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed p.91, as applied in the B.5.6 endgame on printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
namespace ConstituentFlags
universe u v w
variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) D W}

/-- A central cover of the specified action, containing all ambient displacements. -/
structure Layer (σ : Representation (ZMod 2) D U) (τ : Representation (ZMod 2) D W) where
  upper : Subrepresentation σ
  projection : upper.toSubmodule →ₗ[ZMod 2] W
  surjective : Function.Surjective projection
  equivariant : ∀ g v, projection (upper.toRepresentation g v) = τ g (projection v)
  kernel_fixed : ∀ v, projection v = 0 → ∀ g, σ g v = v
  displacement : ∀ g v, σ g v - v ∈ upper.toSubmodule

private theorem saturated_chain {α : Type*} [PartialOrder α] [Finite α]
    {x y : α} (hxy : x ≤ y) :
    ∃ (n : ℕ) (c : ℕ → α), Monotone c ∧ c 0 = x ∧ c n = y ∧
      ∀ i < n, c i ⋖ c (i + 1) := by
  obtain ⟨a, ha, n, hn, hc⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hxy
  let c : ℕ → α := fun i => a (min i n)
  have hmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi]
        using (hc i hi).le
    · have hni : n ≤ i := by omega
      simp only [c, Nat.min_eq_right hni, Nat.min_eq_right (hni.trans (Nat.le_succ i))]
      exact le_rfl
  refine ⟨n, c, hmono, ?_, ?_, ?_⟩
  · simpa [c] using ha
  · simpa [c] using hn
  · intro i hi
    simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using hc i hi

private theorem flag_of_layer [FiniteDimensional (ZMod 2) U]
    (C N : Subrepresentation σ) (hcov : C ⋖ N)
    (hnat : IsLinearNatural (sectionRepresentation σ C N) BinaryField.two 3)
    (hfix : ∀ v ∈ C.toSubmodule, ∀ g, σ g v = v)
    (hdisp : ∀ g v, σ g v - v ∈ N.toSubmodule) :
    UniqueNoncentralNaturalFactor σ := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation σ) := Finite.of_injective
    (fun T : Subrepresentation σ => (T : Set U)) SetLike.coe_injective
  obtain ⟨n, a, hma, ha0, han, hca⟩ := saturated_chain (show ⊥ ≤ C from bot_le)
  obtain ⟨m, b, hmb, hb0, hbm, hcb⟩ := saturated_chain (show N ≤ ⊤ from le_top)
  let c : ℕ → Subrepresentation σ := fun i => if i ≤ n then a i else b (i - (n + 1))
  have hl (i) (hi : i ≤ n) : c i = a i := if_pos hi
  have hr (i) (hi : n < i) : c i = b (i - (n + 1)) := if_neg (by omega)
  have hcn : c n = C := (hl n le_rfl).trans han
  have hcn1 : c (n + 1) = N := by rw [hr _ (by omega), Nat.sub_self, hb0]
  have hm : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    rcases lt_trichotomy i n with hi | rfl | hi
    · rw [hl i (by omega), hl (i + 1) (by omega)]
      exact hma (Nat.le_succ i)
    · rw [hcn, hcn1]; exact hcov.le
    · rw [hr i hi, hr (i + 1) (by omega)]
      exact hmb (Nat.sub_le_sub_right (Nat.le_succ i) _)
  refine ⟨n + 1 + m, c, n, hm, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · rw [hl 0 (Nat.zero_le n), ha0]
  · rw [hr _ (by omega), Nat.add_sub_cancel_left, hbm]
  · intro i hi
    rcases lt_trichotomy i n with hi' | rfl | hi'
    · rw [hl i (by omega), hl (i + 1) (by omega)]
      exact hca i hi'
    · rwa [hcn, hcn1]
    · rw [hr i hi', hr (i + 1) (by omega),
        show i + 1 - (n + 1) = (i - (n + 1)) + 1 by omega]
      exact hcb _ (by omega)
  · rwa [hcn, hcn1]
  · intro i hi hne g
    apply (sectionRepresentation_trivial_iff σ (c i) (c (i + 1)) g).mpr
    intro v hv
    rcases lt_or_gt_of_ne hne with hi' | hi'
    · have hvC : v ∈ C.toSubmodule := by
        rw [← hcn]
        exact hm (by omega) hv
      rw [hfix v hvC g, sub_self]
      exact (c i).toSubmodule.zero_mem
    · exact (show N ≤ c i by rw [← hcn1]; exact hm (by omega)) (hdisp g v)

noncomputable def Layer.kernel (l : Layer σ τ) : Subrepresentation σ where
  toSubmodule := l.projection.ker.map l.upper.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨l.upper.toRepresentation g v, ?_, rfl⟩
    change l.projection (l.upper.toRepresentation g v) = 0
    rw [l.equivariant, show l.projection v = 0 from hv, map_zero]

theorem Layer.kernel_le (l : Layer σ τ) : l.kernel ≤ l.upper :=
  Submodule.map_subtype_le _ _

theorem Layer.mem_kernel_iff (l : Layer σ τ) (v : l.upper.toSubmodule) :
    (v : U) ∈ l.kernel ↔ l.projection v = 0 := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

noncomputable def Layer.sectionEquiv (l : Layer σ τ) :
    ActionEquiv (sectionRepresentation σ l.kernel l.upper) τ := by
  have hk : (sectionLower σ l.kernel l.upper).toSubmodule = l.projection.ker := by
    ext v
    exact l.mem_kernel_iff v
  let e := (Submodule.quotEquivOfEq _ _ hk).trans
    (l.projection.quotKerEquivOfSurjective l.surjective)
  refine ⟨MulEquiv.refl D, e, ?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact l.equivariant g v

theorem Layer.chief (l : Layer σ τ) [IsIrreducible τ] : l.kernel ⋖ l.upper := by
  let p := l.projection.intertwiningMap_of_isIntertwiningMap _ _ l.equivariant
  have hk : IsCoatom p.ker := SimpleHeadQuotient.isCoatom_ker_of_surjective p l.surjective
  have hlt : l.kernel < l.upper := lt_of_le_of_ne l.kernel_le (by
    intro he
    apply hk.1
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    exact (l.mem_kernel_iff v).mp (he.symm ▸ v.property))
  refine ⟨hlt, ?_⟩
  intro B hKB hBN
  let T := sectionLower σ B l.upper
  have hPT : p.ker < T := by
    refine lt_of_le_of_ne (fun v hv => hKB.le ((l.mem_kernel_iff v).mpr hv)) ?_
    intro he
    apply (not_le_of_gt hKB)
    intro v hv
    apply (l.mem_kernel_iff ⟨v, hBN.le hv⟩).mpr
    have : (⟨v, hBN.le hv⟩ : l.upper.toSubmodule) ∈ T := hv
    rwa [← he] at this
  have ht := hk.2 T hPT
  apply (not_le_of_gt hBN)
  intro v hv
  have : (⟨v, hv⟩ : l.upper.toSubmodule) ∈ T := by rw [ht]; trivial
  exact this

theorem Layer.uniqueFactor [FiniteDimensional (ZMod 2) U]
    (l : Layer σ τ) (e : ActionEquiv τ (linearNatural BinaryField.two 3)) :
    UniqueNoncentralNaturalFactor σ := by
  let := irreducible_of_equiv e (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  have hn : IsLinearNatural (sectionRepresentation σ l.kernel l.upper) BinaryField.two 3 :=
    ⟨{ groupEquiv := e.groupEquiv
       linearEquiv := l.sectionEquiv.linearEquiv.trans e.linearEquiv
       intertwines := fun g v => by
         change e.linearEquiv (l.sectionEquiv.linearEquiv
           (sectionRepresentation σ l.kernel l.upper g v)) = _
         rw [l.sectionEquiv.intertwines]
         exact e.intertwines g _ }⟩
  apply flag_of_layer l.kernel l.upper l.chief hn _ l.displacement
  rintro v ⟨w, hw, rfl⟩ g
  exact l.kernel_fixed w hw g

theorem Layer.faithful (l : Layer σ τ)
    (e : ActionEquiv τ (linearNatural BinaryField.two 3)) : Function.Injective σ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := e.linearEquiv.surjective v
  obtain ⟨x, rfl⟩ := l.surjective w
  have hx : l.upper.toRepresentation g x = l.upper.toRepresentation h x :=
    Subtype.ext (LinearMap.congr_fun he x)
  have hp : τ g (l.projection x) = τ h (l.projection x) := by
    rw [← l.equivariant, ← l.equivariant, hx]
  exact (e.intertwines g _).symm.trans
    ((congrArg e.linearEquiv hp).trans (e.intertwines h _))

/-- Intersecting the upper layer with a submodule either retains the whole
simple image or gives a central submodule. Perfectness is used in the latter case. -/
theorem Layer.restrictOrCentral [Group.IsPerfect D] [IsIrreducible τ]
    (l : Layer σ τ) (S : Subrepresentation σ) :
    (∀ g v, S.toRepresentation g v = v) ∨ Nonempty (Layer S.toRepresentation τ) := by
  let A := sectionLower σ l.upper S
  let j : A.toSubmodule →ₗ[ZMod 2] l.upper.toSubmodule :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p := l.projection.comp j
  have hp (g : D) (v : A.toSubmodule) : p (A.toRepresentation g v) = τ g (p v) :=
    l.equivariant g (j v)
  let f := p.intertwiningMap_of_isIntertwiningMap _ _ hp
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · right
    refine ⟨⟨A, p, hs, hp, ?_, ?_⟩⟩
    · intro v hv g
      exact Subtype.ext (l.kernel_fixed (j v) hv g)
    · intro g v
      exact l.displacement g v
  · left
    have hcentral : A.toSubmodule ≤ fixedSpace S.toRepresentation ⊤ := by
      intro v hv g
      have hpzero : p ⟨v, hv⟩ = 0 := by
        exact congrArg (fun t : A.toRepresentation.IntertwiningMap τ => t ⟨v, hv⟩) hz
      exact Subtype.ext (l.kernel_fixed (j ⟨v, hv⟩) hpzero g)
    have hcomm : moved S.toRepresentation ⊤ ≤ A.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, _, v, _, rfl⟩
      exact l.displacement g v
    have hfix := le_fixedSpace_of_commutator_le_fixedSpace S.toRepresentation
      (⊤ : Subgroup D) ⊤ (le_subspaceStabilizer _ ⊤ (by simp)) (hcomm.trans hcentral)
    intro g v
    exact hfix (Submodule.mem_top) ⟨g, Subgroup.mem_top g⟩

/-- A single natural layer gives the literal ambient flag and all constituent
flags. Faithfulness on a constituent is proved from its surviving natural image. -/
theorem Layer.applicability [FiniteDimensional (ZMod 2) U] [Group.IsPerfect D]
    (l : Layer σ τ) (e : ActionEquiv τ (linearNatural BinaryField.two 3)) :
    ConstituentApplicability σ := by
  let := irreducible_of_equiv e (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  intro S _
  rcases l.restrictOrCentral S with hc | hl
  · exact Or.inl hc
  · obtain ⟨lS⟩ := hl
    exact Or.inr ⟨lS.faithful e, lS.uniqueFactor e⟩

end ConstituentFlags
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit.ExceptionalSplitting
