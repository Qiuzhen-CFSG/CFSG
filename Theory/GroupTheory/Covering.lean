module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Generic finite quasisimple covering infrastructure. -/
/- BEGIN Theory.GroupTheory.Covering -/
universe u v w

namespace Theory.GroupTheory
/-- A group is quasisimple when it is perfect and its quotient by the center is simple. -/
public class IsQuasisimple (G : Type*) [Group G] : Prop extends Group.IsPerfect G where
  simple : IsSimpleGroup (G ⧸ Subgroup.center G)

public lemma isQuasisimple_def (G : Type u) [Group G] :
    IsQuasisimple G ↔ commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G) :=
  ⟨fun h ↦ ⟨h.commutator_eq_top, h.simple⟩,
    fun h ↦ { toIsPerfect := ⟨h.1⟩, simple := h.2 }⟩

/-- A covering is a surjective homomorphism between finite quasisimple groups. -/
public structure Covering (G : Type u) (H : Type v) [Group G] [Finite G]
    [IsQuasisimple G] [Group H] [Finite H] [IsQuasisimple H] extends G →* H where
  surjective : Function.Surjective toFun

namespace Covering

variable {G : Type u} {H : Type v} {I : Type w}
variable [Group G] [Finite G] [IsQuasisimple G]
variable [Group H] [Finite H] [IsQuasisimple H]
variable [Group I] [Finite I] [IsQuasisimple I]

public instance : FunLike (Covering G H) G H where
  coe f := f.toMonoidHom
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact MonoidHom.ext fun x ↦ congrFun h x

public instance : MonoidHomClass (Covering G H) G H where
  map_one f := f.toMonoidHom.map_one
  map_mul f := f.toMonoidHom.map_mul

/-- The kernel of a covering of quasisimple groups is central. -/
public theorem ker_le_center (f : Covering G H) :
    f.toMonoidHom.ker ≤ Subgroup.center G := by
  let : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    (inferInstance : IsQuasisimple G).simple
  let : IsSimpleGroup (H ⧸ Subgroup.center H) :=
    (inferInstance : IsQuasisimple H).simple
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  let N : Subgroup (G ⧸ Subgroup.center G) := f.toMonoidHom.ker.map q
  have : Nontrivial H :=
    (QuotientGroup.mk'_surjective (Subgroup.center H)).nontrivial
  have hker_ne_top : f.toMonoidHom.ker ≠ ⊤ := by
    intro hker
    have hf_one : f.toMonoidHom = 1 := MonoidHom.ker_eq_top_iff.mp hker
    obtain ⟨y, hy⟩ := exists_ne (1 : H)
    obtain ⟨x, rfl⟩ := f.surjective y
    exact hy (by simp [hf_one])
  have : N.Normal := by
    dsimp [N, q]
    infer_instance
  rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hN | hN
  · intro x hx
    have hxN : q x ∈ N := ⟨x, hx, rfl⟩
    rw [hN, Subgroup.mem_bot] at hxN
    exact (QuotientGroup.eq_one_iff x).mp hxN
  · exfalso
    have hcomap := congrArg (Subgroup.comap q) hN
    have hsup : f.toMonoidHom.ker ⊔ Subgroup.center G = ⊤ := by
      dsimp [N, q] at hcomap
      simpa [sup_comm] using hcomap
    have hcomm : _root_.commutator G ≤ f.toMonoidHom.ker :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        hsup (inferInstance : IsMulCommutative (Subgroup.center G))
    apply hker_ne_top
    apply top_unique
    simpa using hcomm

/-- For a covering onto a simple group, the kernel is the whole center of the
covering group. -/
public theorem ker_eq_center_of_isSimple (f : Covering G H) [IsSimpleGroup H] :
    f.toMonoidHom.ker = Subgroup.center G := by
  apply le_antisymm f.ker_le_center
  have hcenter : Subgroup.center H = ⊥ := by
    rcases (inferInstance : (Subgroup.center H).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      exact Group.IsPerfect.not_isMulCommutative H (Subgroup.center_eq_top_iff.mp h)
  intro z hz
  have hz' := Subgroup.mem_center_iff.mp hz
  have hfz : f.toMonoidHom z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, hx⟩ := f.surjective y
    rw [← hx]
    change f.toMonoidHom x * f.toMonoidHom z =
      f.toMonoidHom z * f.toMonoidHom x
    simpa only [map_mul] using congrArg f.toMonoidHom (hz' x)
  rw [hcenter, Subgroup.mem_bot] at hfz
  exact MonoidHom.mem_ker.mpr hfz

@[simp]
public theorem coe_toMonoidHom (f : Covering G H) : ⇑f.toMonoidHom = f := rfl

@[simp]
public theorem toMonoidHom_apply (f : Covering G H) (x : G) : f.toMonoidHom x = f x := rfl

@[ext]
public theorem ext {f g : Covering G H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[expose]
public def copy (f : Covering G H) (f' : G →* H) (h : f' = f.toMonoidHom) :
    Covering G H where
  toMonoidHom := f'
  surjective := by simpa [h] using f.surjective

@[simp]
public theorem copy_apply (f : Covering G H) (f' : G →* H)
    (h : f' = f.toMonoidHom) (x : G) : f.copy f' h x = f x := by
  subst f'
  rfl

@[expose]
public def id : Covering G G where
  toMonoidHom := MonoidHom.id G
  surjective := Function.surjective_id

@[simp]
public theorem id_apply (x : G) : (id : Covering G G) x = x := rfl

@[simp]
public theorem id_toMonoidHom : (id : Covering G G).toMonoidHom = MonoidHom.id G := rfl

@[expose]
public def comp (g : Covering H I) (f : Covering G H) : Covering G I where
  toMonoidHom := g.toMonoidHom.comp f.toMonoidHom
  surjective := g.surjective.comp f.surjective

@[simp]
public theorem comp_apply (g : Covering H I) (f : Covering G H) (x : G) :
    g.comp f x = g (f x) := rfl

@[simp]
public theorem comp_toMonoidHom (g : Covering H I) (f : Covering G H) :
    (g.comp f).toMonoidHom = g.toMonoidHom.comp f.toMonoidHom := rfl

@[simp]
public theorem id_comp (f : Covering G H) : id.comp f = f := by
  ext x
  rfl

@[simp]
public theorem comp_id (f : Covering G H) : f.comp id = f := by
  ext x
  rfl

public theorem comp_assoc {J : Type*} [Group J] [Finite J] [IsQuasisimple J]
    (h : Covering I J) (g : Covering H I) (f : Covering G H) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

@[expose]
public def ofMulEquiv (e : G ≃* H) : Covering G H where
  toMonoidHom := e.toMonoidHom
  surjective := e.surjective

@[simp]
public theorem ofMulEquiv_apply (e : G ≃* H) (x : G) : ofMulEquiv e x = e x := rfl

@[simp]
public theorem ofMulEquiv_toMonoidHom (e : G ≃* H) :
    (ofMulEquiv e).toMonoidHom = e.toMonoidHom := rfl

@[simp]
public theorem ofMulEquiv_refl : ofMulEquiv (MulEquiv.refl G) = id := by
  ext x
  rfl

@[simp]
public theorem ofMulEquiv_trans (e : G ≃* H) (d : H ≃* I) :
    ofMulEquiv (e.trans d) = (ofMulEquiv d).comp (ofMulEquiv e) := by
  ext x
  rfl

/-- The unique-lifting property defining a universal covering, relative to a source universe. -/
@[expose] public def IsUniversal {K : Type u} {L : Type v} [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L] (f : Covering L K) : Prop :=
  ∀ (M : Type w) [Group M] [Finite M] [IsQuasisimple M] (g : Covering M K),
    ∃! h : Covering L M, g.comp h = f

namespace IsUniversal

variable {K : Type u} {L : Type v} {M : Type w}
variable [Group K] [Finite K] [IsQuasisimple K]
variable [Group L] [Finite L] [IsQuasisimple L]
variable [Group M] [Finite M] [IsQuasisimple M]
variable {f : Covering L K}

public noncomputable def lift (hf : IsUniversal.{u, v, w} f) (g : Covering M K) :
    Covering L M :=
  Classical.choose (hf M g)

public theorem lift_fac (hf : IsUniversal.{u, v, w} f) (g : Covering M K) :
    g.comp (hf.lift g) = f :=
  (Classical.choose_spec (hf M g)).1

public theorem hom_ext (hf : IsUniversal.{u, v, w} f) (g : Covering M K)
    {h₁ h₂ : Covering L M} (hh₁ : g.comp h₁ = f) (hh₂ : g.comp h₂ = f) : h₁ = h₂ :=
  (hf M g).unique hh₁ hh₂

end IsUniversal

/-- The subgroup of automorphisms of the covering group that stabilize the
kernel of the covering. -/
@[expose]
public def kernelStabilizer {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) : Subgroup (MulAut L) where
  carrier := {α | ∀ x, x ∈ f.toMonoidHom.ker ↔ α x ∈ f.toMonoidHom.ker}
  one_mem' := by simp
  mul_mem' := by
    intro α β hα hβ x
    exact (hβ x).trans (hα (β x))
  inv_mem' := by
    intro α hα x
    simpa using (hα (α.symm x)).symm

/-- Schur's comparison theorem: a covering of base groups induces a unique
isomorphism between chosen universal covering groups. This is Theorem 5.1.2(b). -/
public theorem existsUnique_mulEquiv_of_isUniversal
    {K₁ K₂ L₁ L₂ : Type u}
    [Group K₁] [Finite K₁] [IsQuasisimple K₁]
    [Group K₂] [Finite K₂] [IsQuasisimple K₂]
    [Group L₁] [Finite L₁] [IsQuasisimple L₁]
    [Group L₂] [Finite L₂] [IsQuasisimple L₂]
    (c : Covering K₁ K₂) (f₁ : Covering L₁ K₁) (f₂ : Covering L₂ K₂)
    (hf₁ : IsUniversal.{u, u, u} f₁) (hf₂ : IsUniversal.{u, u, u} f₂) :
    ∃! e : L₁ ≃* L₂, f₂.comp (ofMulEquiv e) = c.comp f₁ := by
  let h : Covering L₂ L₁ := hf₂.lift (c.comp f₁)
  have hh : (c.comp f₁).comp h = f₂ := hf₂.lift_fac (c.comp f₁)
  let l : Covering L₁ L₂ := hf₁.lift (f₁.comp h)
  have hl : (f₁.comp h).comp l = f₁ := hf₁.lift_fac (f₁.comp h)
  have hhl : h.comp l = id := by
    apply hf₁.hom_ext f₁
    · rw [← comp_assoc, hl]
    · exact comp_id f₁
  have hlh : l.comp h = id := by
    apply hf₂.hom_ext f₂
    · ext x
      calc
        f₂ (l (h x)) = c (f₁ (h (l (h x)))) :=
          (congrArg (fun q : Covering L₂ K₂ ↦ q (l (h x))) hh).symm
        _ = c (f₁ (h x)) :=
          congrArg (fun y ↦ c y) (congrArg (fun q : Covering L₁ K₁ ↦ q (h x)) hl)
        _ = f₂ x := congrArg (fun q : Covering L₂ K₂ ↦ q x) hh
    · exact comp_id f₂
  have hleft : h.toMonoidHom.comp l.toMonoidHom = MonoidHom.id L₁ := by
    simpa only [comp_toMonoidHom, id_toMonoidHom] using
      congrArg (fun q : Covering L₁ L₁ ↦ q.toMonoidHom) hhl
  have hright : l.toMonoidHom.comp h.toMonoidHom = MonoidHom.id L₂ := by
    simpa only [comp_toMonoidHom, id_toMonoidHom] using
      congrArg (fun q : Covering L₂ L₂ ↦ q.toMonoidHom) hlh
  let e : L₁ ≃* L₂ := l.toMonoidHom.toMulEquiv h.toMonoidHom hleft hright
  refine ⟨e, ?_, ?_⟩
  · ext x
    calc
      f₂ (ofMulEquiv e x) = f₂ (l x) := rfl
      _ = c (f₁ (h (l x))) :=
        (congrArg (fun q : Covering L₂ K₂ ↦ q (l x)) hh).symm
      _ = c (f₁ x) :=
        congrArg (fun y ↦ c y) (congrArg (fun q : Covering L₁ K₁ ↦ q x) hl)
  · intro e' he'
    have heinv : (c.comp f₁).comp (ofMulEquiv e'.symm) = f₂ := by
      ext x
      calc
        c (f₁ (e'.symm x)) = f₂ (e' (e'.symm x)) :=
          (congrArg (fun q : Covering L₁ K₂ ↦ q (e'.symm x)) he').symm
        _ = f₂ x := by simp
    have hinv : ofMulEquiv e'.symm = h :=
      hf₂.hom_ext (c.comp f₁) heinv hh
    have hsymm : e'.symm = e.symm := by
      ext x
      simpa [e] using congrArg (fun q : Covering L₂ L₁ ↦ q x) hinv
    simpa using congrArg (fun q : L₂ ≃* L₁ ↦ q.symm) hsymm

/-- Universal covering groups of the same quasisimple group are uniquely isomorphic.
This is Corollary 5.1.3. -/
public theorem existsUnique_mulEquiv_of_isUniversal_sameBase
    {K L₁ L₂ : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L₁] [Finite L₁] [IsQuasisimple L₁]
    [Group L₂] [Finite L₂] [IsQuasisimple L₂]
    (f₁ : Covering L₁ K) (f₂ : Covering L₂ K)
    (hf₁ : IsUniversal.{u, u, u} f₁) (hf₂ : IsUniversal.{u, u, u} f₂) :
    ∃! e : L₁ ≃* L₂, f₂.comp (ofMulEquiv e) = f₁ := by
  simpa using existsUnique_mulEquiv_of_isUniversal (id : Covering K K) f₁ f₂ hf₁ hf₂

namespace IsUniversal

variable {K L : Type u}
variable [Group K] [Finite K] [IsQuasisimple K]
variable [Group L] [Finite L] [IsQuasisimple L]
variable {f : Covering L K}

/-- Every automorphism of the base lifts uniquely to the universal covering group.
This is Corollary 5.1.4(a). -/
public theorem existsUnique_liftMulAut (hf : IsUniversal.{u, u, u} f) (α : MulAut K) :
    ∃! β : MulAut L, f.comp (ofMulEquiv β) = (ofMulEquiv α).comp f := by
  simpa using existsUnique_mulEquiv_of_isUniversal (ofMulEquiv α) f f hf hf

@[expose]
public noncomputable def liftMulAut (hf : IsUniversal.{u, u, u} f) (α : MulAut K) : MulAut L :=
  Classical.choose (hf.existsUnique_liftMulAut α)

public theorem liftMulAut_fac (hf : IsUniversal.{u, u, u} f) (α : MulAut K) :
    f.comp (ofMulEquiv (hf.liftMulAut α)) = (ofMulEquiv α).comp f :=
  (Classical.choose_spec (hf.existsUnique_liftMulAut α)).1

public theorem liftMulAut_unique (hf : IsUniversal.{u, u, u} f) (α : MulAut K)
    {β : MulAut L} (hβ : f.comp (ofMulEquiv β) = (ofMulEquiv α).comp f) :
    β = hf.liftMulAut α :=
  (hf.existsUnique_liftMulAut α).unique hβ (hf.liftMulAut_fac α)

end IsUniversal


namespace IsUniversal

variable {K L : Type u}
variable [Group K] [Finite K] [IsQuasisimple K]
variable [Group L] [Finite L] [IsQuasisimple L]
variable {f : Covering L K}

public theorem liftMulAut_mem_kernelStabilizer
    (hf : IsUniversal.{u, u, u} f) (α : MulAut K) :
    hf.liftMulAut α ∈ kernelStabilizer f := by
  intro x
  change f x = 1 ↔ f (hf.liftMulAut α x) = 1
  have hpoint := congrArg (fun q : Covering L K ↦ q x) (hf.liftMulAut_fac α)
  constructor
  · intro hx
    simpa [hx] using hpoint
  · intro hx
    apply α.injective
    simpa [hx] using hpoint.symm

@[expose]
public noncomputable def liftMulAutToStabilizer
    (hf : IsUniversal.{u, u, u} f) : MulAut K →* kernelStabilizer f where
  toFun α := ⟨hf.liftMulAut α, hf.liftMulAut_mem_kernelStabilizer α⟩
  map_one' := by
    apply Subtype.ext
    exact (hf.liftMulAut_unique (1 : MulAut K) (by ext x; rfl)).symm
  map_mul' α β := by
    apply Subtype.ext
    symm
    apply hf.liftMulAut_unique (α * β)
    ext x
    have hα := congrArg (fun q : Covering L K ↦ q (hf.liftMulAut β x))
      (hf.liftMulAut_fac α)
    have hβ := congrArg (fun q : Covering L K ↦ q x) (hf.liftMulAut_fac β)
    exact hα.trans (congrArg (fun y ↦ α y) hβ)

end IsUniversal

/-- Every covering of the same base is a quotient of a universal covering group.
This is the quotient-isomorphism core of Corollary 5.1.5(a). -/
public theorem exists_quotient_mulEquiv_of_isUniversal
    {K L G : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering L K) (hf : IsUniversal.{u, u, u} f) (g : Covering G K) :
    ∃ (Z : Subgroup L) (_hZ : Z.Normal) (_hZcenter : Z ≤ Subgroup.center L),
      Nonempty (L ⧸ Z ≃* G) := by
  let h : Covering L G := hf.lift g
  let Z : Subgroup L := h.toMonoidHom.ker
  let : Z.Normal := by
    dsimp [Z]
    infer_instance
  exact ⟨Z, inferInstance, h.ker_le_center,
    ⟨QuotientGroup.quotientKerEquivOfSurjective h.toMonoidHom h.surjective⟩⟩

/-- Corollary 5.1.5(a): a quasisimple group with central factor `K` is a
central quotient of a universal covering group of `K`. -/
public theorem theorem_5_1_5_a
    {K L X : Type u}
    [Group K] [Finite K] [IsQuasisimple K] [IsSimpleGroup K]
    [Group L] [Finite L] [IsQuasisimple L]
    [Group X] [Finite X] [IsQuasisimple X]
    (f : Covering L K) (hf : IsUniversal.{u, u, u} f)
    (e : X ⧸ Subgroup.center X ≃* K) :
    ∃ (Z : Subgroup L) (_hZ : Z.Normal) (_hZcenter : Z ≤ Subgroup.center L),
      Nonempty (L ⧸ Z ≃* X) := by
  let g : Covering X K := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X)) }
  exact exists_quotient_mulEquiv_of_isUniversal f hf g

/-- An automorphism carrying one normal subgroup to another induces an
isomorphism of the corresponding quotient groups. -/
@[expose]
public def quotientMulEquivOfMapEq
    {L : Type u} [Group L] (e : L ≃* L) (Z₁ Z₂ : Subgroup L)
    [Z₁.Normal] [Z₂.Normal] (h : Subgroup.map e.toMonoidHom Z₁ = Z₂) :
    L ⧸ Z₁ ≃* L ⧸ Z₂ := by
  have he : Z₁ ≤ Subgroup.comap e.toMonoidHom Z₂ := by
    intro x hx
    change e x ∈ Z₂
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hsymm : Subgroup.map e.symm.toMonoidHom Z₂ = Z₁ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Subgroup.map e.toMonoidHom Z₁ := by
        rw [h]
        exact hy
      rcases hy' with ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      rw [← h]
      exact ⟨x, hx, rfl⟩
  have hesymm : Z₂ ≤ Subgroup.comap e.symm.toMonoidHom Z₁ := by
    intro x hx
    change e.symm x ∈ Z₁
    rw [← hsymm]
    exact ⟨x, hx, rfl⟩
  let q : L ⧸ Z₁ →* L ⧸ Z₂ :=
    QuotientGroup.map Z₁ Z₂ e.toMonoidHom he
  let qinv : L ⧸ Z₂ →* L ⧸ Z₁ :=
    QuotientGroup.map Z₂ Z₁ e.symm.toMonoidHom hesymm
  refine q.toMulEquiv qinv ?_ ?_
  · apply MonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [q, qinv]

  · apply MonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [q, qinv]

@[expose]
public noncomputable def descendMonoidHom
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (β : kernelStabilizer f) : K →* K :=
  (f.toMonoidHom.liftOfSurjective f.surjective)
    ⟨f.toMonoidHom.comp β.1.toMonoidHom, by
      intro x hx
      exact (β.property x).mp hx⟩

public theorem descendMonoidHom_fac
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (β : kernelStabilizer f) :
    (descendMonoidHom f β).comp f.toMonoidHom =
      f.toMonoidHom.comp β.1.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  simp [descendMonoidHom, MonoidHom.liftOfSurjective]

/-- An automorphism stabilizing the kernel descends to the base group. -/
@[expose]
public noncomputable def descendMulAut
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (β : kernelStabilizer f) : MulAut K := by
  let a : K →* K := descendMonoidHom f β
  let ainv : K →* K := descendMonoidHom f β⁻¹
  refine a.toMulEquiv ainv ?_ ?_
  · apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    have hβ := congrArg (fun q : L →* K ↦ q y) (descendMonoidHom_fac f β)
    have hβinv := congrArg (fun q : L →* K ↦ q (β.1 y))
      (descendMonoidHom_fac f β⁻¹)
    calc
      ainv (a (f y)) = ainv (f (β.1 y)) := congrArg ainv hβ
      _ = f ((β⁻¹ : kernelStabilizer f).1 (β.1 y)) := hβinv
      _ = f y := by simp
  · apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    have hβinv := congrArg (fun q : L →* K ↦ q y) (descendMonoidHom_fac f β⁻¹)
    have hβ := congrArg (fun q : L →* K ↦ q ((β⁻¹ : kernelStabilizer f).1 y))
      (descendMonoidHom_fac f β)
    calc
      a (ainv (f y)) = a (f ((β⁻¹ : kernelStabilizer f).1 y)) := congrArg a hβinv
      _ = f (β.1 ((β⁻¹ : kernelStabilizer f).1 y)) := hβ
      _ = f y := by simp

public theorem descendMulAut_fac
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (β : kernelStabilizer f) :
    (descendMulAut f β).toMonoidHom.comp f.toMonoidHom =
      f.toMonoidHom.comp β.1.toMonoidHom := by
  change (descendMonoidHom f β).comp f.toMonoidHom =
    f.toMonoidHom.comp β.1.toMonoidHom
  exact descendMonoidHom_fac f β

@[expose]
public noncomputable def descendMulAutHom
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) : kernelStabilizer f →* MulAut K where
  toFun := descendMulAut f
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    have h := congrArg (fun q : L →* K ↦ q y)
      (descendMulAut_fac f (1 : kernelStabilizer f))
    simpa using h
  map_mul' β γ := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    have hβγ := congrArg (fun q : L →* K ↦ q y) (descendMulAut_fac f (β * γ))
    have hγ := congrArg (fun q : L →* K ↦ q y) (descendMulAut_fac f γ)
    have hβ := congrArg (fun q : L →* K ↦ q (γ.1 y)) (descendMulAut_fac f β)
    calc
      descendMulAut f (β * γ) (f y) = f ((β * γ).1 y) := hβγ
      _ = f (β.1 (γ.1 y)) := rfl
      _ = descendMulAut f β (f (γ.1 y)) := hβ.symm
      _ = descendMulAut f β (descendMulAut f γ (f y)) :=
        congrArg (descendMulAut f β) hγ.symm
      _ = (descendMulAut f β * descendMulAut f γ) (f y) := rfl

/-- Corollary 5.1.4(b): automorphisms of the base are equivalent to
automorphisms of the universal covering group that stabilize the kernel. -/
@[expose]
public noncomputable def mulAutStabilizerEquiv
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hf : IsUniversal.{u, u, u} f) :
    MulAut K ≃* kernelStabilizer f := by
  refine (hf.liftMulAutToStabilizer).toMulEquiv (descendMulAutHom f) ?_ ?_
  · apply MonoidHom.ext
    intro α
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    have hdesc := congrArg (fun q : L →* K ↦ q y)
      (descendMulAut_fac f ⟨hf.liftMulAut α, hf.liftMulAut_mem_kernelStabilizer α⟩)
    have hlift := congrArg (fun q : Covering L K ↦ q y) (hf.liftMulAut_fac α)
    exact hdesc.trans hlift
  · apply MonoidHom.ext
    intro β
    apply Subtype.ext
    exact (hf.liftMulAut_unique (descendMulAut f β) (β := β.1) (by
      ext x
      exact (congrArg (fun q : L →* K ↦ q x) (descendMulAut_fac f β)).symm)).symm

/-- If the kernel is characteristic, its stabilizer is the full automorphism group. -/
@[expose]
public def kernelStabilizerEquivMulAutOfCharacteristic
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hchar : f.toMonoidHom.ker.Characteristic) :
    kernelStabilizer f ≃* MulAut L where
  toFun β := β.1
  invFun α := ⟨α, by
    intro x
    have hcomap := (Subgroup.characteristic_iff_comap_eq.mp hchar) α
    change x ∈ f.toMonoidHom.ker ↔ x ∈ Subgroup.comap α.toMonoidHom f.toMonoidHom.ker
    rw [hcomap]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Consequence 5.1.8: when the kernel of a universal covering is
characteristic, the automorphism groups of the base and covering group are
isomorphic. -/
@[expose]
public noncomputable def mulAutEquivOfCharacteristicKernel
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hf : IsUniversal.{u, u, u} f)
    (hchar : f.toMonoidHom.ker.Characteristic) :
    MulAut K ≃* MulAut L :=
  (mulAutStabilizerEquiv f hf).trans
    (kernelStabilizerEquivMulAutOfCharacteristic f hchar)

/-- Corollary 5.1.4(c): for a universal covering of a simple group, every
automorphism of the covering group descends uniquely to the base group. -/
@[expose]
public noncomputable def theorem_5_1_4_c
    {K L : Type u}
    [Group K] [Finite K] [IsQuasisimple K] [IsSimpleGroup K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hf : IsUniversal.{u, u, u} f) :
    MulAut L ≃* MulAut K :=
  (mulAutEquivOfCharacteristicKernel f hf (by
    rw [f.ker_eq_center_of_isSimple]
    infer_instance)).symm

/-- Consequence 5.1.8 for two groups with a common universal covering group:
if both covering kernels are characteristic, their automorphism groups are
isomorphic. -/
@[expose]
public noncomputable def mulAutEquiv_of_characteristicKernels
    {K L N : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    [Group N] [Finite N] [IsQuasisimple N]
    (fK : Covering L K) (fN : Covering L N)
    (hfK : IsUniversal.{u, u, u} fK) (hfN : IsUniversal.{u, u, u} fN)
    (hcharK : fK.toMonoidHom.ker.Characteristic)
    (hcharN : fN.toMonoidHom.ker.Characteristic) :
    MulAut N ≃* MulAut K :=
  (mulAutEquivOfCharacteristicKernel fN hfN hcharN).trans
    (mulAutEquivOfCharacteristicKernel fK hfK hcharK).symm

/-- A subgroup uniquely determined by its cardinality inside a characteristic
subgroup is itself characteristic. This is the group-theoretic input used in
the cyclic Schur-multiplier consequence of 5.1.8. -/
public theorem characteristic_of_unique_card_in_characteristic
    {L : Type u} [Group L] (M Z : Subgroup L) (hM : M.Characteristic)
    (hZM : Z ≤ M)
    (hunique : ∀ W : Subgroup L, W ≤ M → Nat.card W = Nat.card Z → W = Z) :
    Z.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro α
  apply hunique
  · rw [← (Subgroup.characteristic_iff_map_eq.mp hM) α]
    exact Subgroup.map_mono hZM
  · exact Subgroup.card_map_of_injective α.injective

/-- Consequence 5.1.8 in its kernel-cardinality form. If two groups have a
common universal covering, the first kernel is characteristic, and the second
kernel is the unique subgroup of its cardinality inside the first, then their
automorphism groups are isomorphic. For a cyclic Schur multiplier, uniqueness
of subgroups of each order supplies the uniqueness hypothesis. -/
@[expose]
public noncomputable def mulAutEquiv_of_uniqueKernelCard
    {K L N : Type u}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    [Group N] [Finite N] [IsQuasisimple N]
    (fK : Covering L K) (fN : Covering L N)
    (hfK : IsUniversal.{u, u, u} fK) (hfN : IsUniversal.{u, u, u} fN)
    (hcharK : fK.toMonoidHom.ker.Characteristic)
    (hle : fN.toMonoidHom.ker ≤ fK.toMonoidHom.ker)
    (hunique : ∀ Z : Subgroup L, Z ≤ fK.toMonoidHom.ker →
      Nat.card Z = Nat.card fN.toMonoidHom.ker → Z = fN.toMonoidHom.ker) :
    MulAut N ≃* MulAut K :=
  mulAutEquiv_of_characteristicKernels fK fN hfK hfN hcharK
    (characteristic_of_unique_card_in_characteristic
      fK.toMonoidHom.ker fN.toMonoidHom.ker hcharK hle hunique)

/-- Two subgroups are in the same automorphism orbit when an automorphism maps
one onto the other. -/
public def InSameMulAutOrbit {L : Type u} [Group L]
    (Z₁ Z₂ : Subgroup L) : Prop :=
  ∃ α : MulAut L, Subgroup.map α.toMonoidHom Z₁ = Z₂

/-- The forward implication in Corollary 5.1.5(b): automorphism-conjugate
central kernels give isomorphic quotient groups. -/
public theorem nonempty_quotientMulEquiv_of_inSameMulAutOrbit
    {L : Type u} [Group L] (Z₁ Z₂ : Subgroup L) [Z₁.Normal] [Z₂.Normal]
    (h : InSameMulAutOrbit Z₁ Z₂) : Nonempty (L ⧸ Z₁ ≃* L ⧸ Z₂) := by
  rcases h with ⟨α, hα⟩
  exact ⟨quotientMulEquivOfMapEq α Z₁ Z₂ hα⟩

/-- Consequence 5.1.8: if automorphisms act transitively on kernel subgroups
of a prescribed isomorphism type `T`, the resulting quotient covering groups
have a unique isomorphism type. -/
public theorem quotient_isomorphism_unique_of_kernelType_transitive
    {L : Type u} [Group L] (T : Type v) [Group T]
    (htrans : ∀ Z₁ Z₂ : Subgroup L,
      Nonempty (Z₁ ≃* T) → Nonempty (Z₂ ≃* T) → InSameMulAutOrbit Z₁ Z₂)
    (Z₁ Z₂ : Subgroup L) [Z₁.Normal] [Z₂.Normal]
    (hZ₁ : Nonempty (Z₁ ≃* T)) (hZ₂ : Nonempty (Z₂ ≃* T)) :
    Nonempty (L ⧸ Z₁ ≃* L ⧸ Z₂) :=
  nonempty_quotientMulEquiv_of_inSameMulAutOrbit Z₁ Z₂ (htrans Z₁ Z₂ hZ₁ hZ₂)

/-- The kernel-uniqueness form of the cyclic-multiplier consequence in 5.1.8.
For a cyclic Schur multiplier the hypothesis follows from uniqueness of its
subgroup of each isomorphism type. -/
public theorem quotient_isomorphism_unique_of_kernelType_unique
    {L : Type u} [Group L] (T : Type v) [Group T]
    (hunique : ∀ Z₁ Z₂ : Subgroup L,
      Nonempty (Z₁ ≃* T) → Nonempty (Z₂ ≃* T) → Z₁ = Z₂)
    (Z₁ Z₂ : Subgroup L) [Z₁.Normal] [Z₂.Normal]
    (hZ₁ : Nonempty (Z₁ ≃* T)) (hZ₂ : Nonempty (Z₂ ≃* T)) :
    Nonempty (L ⧸ Z₁ ≃* L ⧸ Z₂) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (hunique Z₁ Z₂ hZ₁ hZ₂)⟩

/-- The order-based uniqueness form of the cyclic-multiplier consequence in
5.1.8: unique subgroups of a given order give a unique quotient isomorphism
type. -/
public theorem quotient_isomorphism_unique_of_kernelCard_unique
    {L : Type u} [Group L]
    (hunique : ∀ Z₁ Z₂ : Subgroup L, Nat.card Z₁ = Nat.card Z₂ → Z₁ = Z₂)
    (Z₁ Z₂ : Subgroup L) [Z₁.Normal] [Z₂.Normal]
    (hcard : Nat.card Z₁ = Nat.card Z₂) :
    Nonempty (L ⧸ Z₁ ≃* L ⧸ Z₂) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (hunique Z₁ Z₂ hcard)⟩

/-- The Schur multiplier attached to a chosen universal covering is its kernel.
This is Definition 5.1.6. -/
@[expose]
public def schurMultiplier {K : Type u} {L : Type v}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (_hf : IsUniversal.{u, v, v} f) : Subgroup L :=
  f.toMonoidHom.ker
public instance schurMultiplierNormal {K : Type u} {L : Type v}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hf : IsUniversal.{u, v, v} f) :
    (schurMultiplier f hf).Normal := by
  change f.toMonoidHom.ker.Normal
  infer_instance

/-- The quotient of a universal covering group by its Schur multiplier is the base group. -/
@[expose]
public noncomputable def quotientSchurMultiplierEquiv {K : Type u} {L : Type v}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L K) (hf : IsUniversal.{u, v, v} f) :
    L ⧸ schurMultiplier f hf ≃* K :=
  QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective

end Covering

end Theory.GroupTheory
/- END Theory.GroupTheory.Covering -/
