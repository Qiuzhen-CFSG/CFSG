module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Indexed family amalgams

An indexed family amalgam records all proper-subset overlap maps of a finite family of
groups.  The universal completion is presented by the multiplication tables
of every local group and by the overlap identifications.  This is the direct
rank- n presentation from Aschbacher, *Sporadic Groups*, 36.1–36.5.

This file supplies only the universal-property layer.  It does not assert a
cycle-base hypothesis, a faithful-completion recognition theorem, or any
Held-specific conclusion.
-/

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false

namespace Theory.GroupTheory.IndexedFamilyAmalgam

universe u v w

/-- Only proper subsets index local groups. The full ambient group is excluded. -/
abbrev ProperIndex (I : Type u) [Fintype I] := {J : Finset I // J ≠ Finset.univ}

variable {I : Type u} [Fintype I]

/-- An amalgam indexed by the proper subsets of a finite type.

`map h` is the overlap homomorphism from the `J`-local group to the
`K`-local group, for an inclusion `h : J.val ⊆ K.val`. -/
structure Amalgam (P : ProperIndex I → Type v) [∀ J, Group (P J)] where
  map : ∀ (J K : ProperIndex I), J.val ⊆ K.val → P J →* P K
  map_refl : ∀ J, map J J (by intro x hx; exact hx) = MonoidHom.id (P J)
  map_comp : ∀ (J K L : ProperIndex I) (hJK : J.val ⊆ K.val) (hKL : K.val ⊆ L.val),
    (map K L hKL).comp (map J K hJK) = map J L (hJK.trans hKL)

namespace Amalgam

variable {P : ProperIndex I → Type v} [∀ J, Group (P J)] (A : Amalgam P)

/-- The disjoint union of all local groups, used as presentation generators. -/
abbrev Generator (P : ProperIndex I → Type v) := Σ J : ProperIndex I, P J

/-- Relations defining multiplication in a local group and every overlap. -/
inductive Relation : FreeGroup (Generator P) → Prop
  | mul (J : ProperIndex I) (a b : P J) :
      Relation
        (FreeGroup.of ⟨J, a * b⟩ *
          (FreeGroup.of ⟨J, a⟩ * FreeGroup.of ⟨J, b⟩)⁻¹)
  | overlap (J K : ProperIndex I) (h : J.val ⊆ K.val) (a : P J) :
      Relation
        (FreeGroup.of ⟨K, A.map J K h a⟩ * (FreeGroup.of ⟨J, a⟩)⁻¹)

/-- The universal completion of an indexed family amalgam. -/
abbrev Universal (A : Amalgam P) := PresentedGroup {r | Relation A r}

namespace Universal

/-- Inclusion of a local group into the universal completion. -/
def inclusion (J : ProperIndex I) : P J →* Universal A :=
  MonoidHom.mk' (fun a => PresentedGroup.of (⟨J, a⟩ : Generator P)) (by
    intro a b
    apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
    exact Relation.mul J a b)

@[simp] theorem inclusion_apply (J : ProperIndex I) (a : P J) :
    inclusion A J a = PresentedGroup.of (⟨J, a⟩ : Generator P) := rfl

/-- The defining overlap relation is respected by the local inclusions. -/
theorem inclusion_map (J K : ProperIndex I) (h : J.val ⊆ K.val) (a : P J) :
    inclusion A K (A.map J K h a) = inclusion A J a := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact Relation.overlap J K h a

/-- Homomorphisms out of the local groups which agree on every overlap. -/
structure CompatibleHom (G : Type w) [Group G] where
  hom : ∀ J : ProperIndex I, P J →* G
  compatible : ∀ (J K : ProperIndex I) (h : J.val ⊆ K.val) (a : P J),
    hom K (A.map J K h a) = hom J a

namespace CompatibleHom

variable {G : Type w} [Group G]

def generatorMap (f : Universal.CompatibleHom A G) : Generator P → G :=
  fun a => f.hom a.1 a.2

theorem relations (f : Universal.CompatibleHom A G) (r : FreeGroup (Generator P))
    (hr : Relation A r) : FreeGroup.lift (generatorMap A f) r = 1 := by
  cases hr with
  | mul J a b => simp [generatorMap]
  | overlap J K h a =>
      simp [generatorMap, f.compatible J K h a]

/-- The universal homomorphism induced by a compatible family of maps. -/
def lift (f : Universal.CompatibleHom A G) : Universal A →* G :=
  PresentedGroup.toGroup (fun r hr => relations A f r hr)

@[simp] theorem lift_inclusion (f : Universal.CompatibleHom A G) (J : ProperIndex I) (a : P J) :
    lift A f (inclusion A J a) = f.hom J a := by
  exact PresentedGroup.toGroup.of _

@[simp] theorem lift_inclusion_comp (f : Universal.CompatibleHom A G) (J : ProperIndex I)
    (a : P J) : lift A f (inclusion A J a) = f.hom J a :=
  lift_inclusion A f J a

end CompatibleHom

/-- The compatible family of literal inclusions into the universal completion. -/
def inclusions : Universal.CompatibleHom A (Universal A) where
  hom := inclusion A
  compatible := by
    intro J K h a
    exact inclusion_map A J K h a

/-- Homomorphisms out of the universal completion are determined by all local
generators. -/
theorem hom_ext {G : Type w} [Group G] (f g : Universal A →* G)
    (h : ∀ (J : ProperIndex I) (a : P J), f (inclusion A J a) = g (inclusion A J a)) :
    f = g := by
  apply PresentedGroup.ext
  intro a
  exact h a.1 a.2

end Universal

/-- A completion of an indexed family amalgam in an ambient group. -/
structure Completion (G : Type w) [Group G] where
  hom : ∀ J : ProperIndex I, P J →* G
  compatible : ∀ (J K : ProperIndex I) (h : J.val ⊆ K.val) (a : P J),
    hom K (A.map J K h a) = hom J a
  generated : Subgroup.closure
      (Set.range (fun a : Generator P => hom a.1 a.2)) = ⊤

namespace Completion

variable {G : Type w} [Group G]

/-- A completion is faithful when each local map is injective. -/
def Faithful (c : Completion A G) : Prop :=
  ∀ J : ProperIndex I, Function.Injective (c.hom J)

/-- The compatible map from the universal completion to an ambient completion. -/
def canonical (c : Completion A G) : Universal A →* G :=
  Universal.CompatibleHom.lift A
    { hom := c.hom
      compatible := c.compatible }

@[simp] theorem canonical_inclusion (c : Completion A G) (J : ProperIndex I) (a : P J) :
    canonical A c (Universal.inclusion A J a) = c.hom J a := by
  exact Universal.CompatibleHom.lift_inclusion A
    ({ hom := c.hom, compatible := c.compatible } : Universal.CompatibleHom A G) J a

/-- The canonical map is surjective whenever the local images generate. -/
theorem canonical_surjective (c : Completion A G) :
    Function.Surjective (canonical A c) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← c.generated]
  apply (Subgroup.closure_le ((canonical A c).range)).mpr
  rintro _ ⟨a, rfl⟩
  refine ⟨Universal.inclusion A a.1 a.2, ?_⟩
  change (canonical A c) (Universal.inclusion A a.1 a.2) = c.hom a.1 a.2
  exact canonical_inclusion A c a.1 a.2

theorem canonical_range_eq_top (c : Completion A G) : (canonical A c).range = ⊤ :=
  (MonoidHom.range_eq_top.mpr (canonical_surjective A c))

end Completion

/-- A compatible isomorphism of indexed family amalgams. -/
structure Iso {Q : ProperIndex I → Type v} [∀ J, Group (Q J)]
    (B : Amalgam Q) where
  localIso : ∀ J : ProperIndex I, P J ≃* Q J
  commutes : ∀ (J K : ProperIndex I) (h : J.val ⊆ K.val) (a : P J),
    localIso K (A.map J K h a) = B.map J K h (localIso J a)

namespace Iso

variable {Q : ProperIndex I → Type v} [∀ J, Group (Q J)]
variable {B : Amalgam Q} (e : Iso A B)

def toCompatibleHom : Universal.CompatibleHom A (Universal B) where
  hom J := (Universal.inclusion B J).comp (e.localIso J).toMonoidHom
  compatible := by
    intro J K h a
    change Universal.inclusion B K (e.localIso K (A.map J K h a)) =
      Universal.inclusion B J (e.localIso J a)
    rw [e.commutes J K h a, Universal.inclusion_map B J K h]

def toHom : Universal A →* Universal B :=
  Universal.CompatibleHom.lift A (toCompatibleHom A e)

def inverseCompatibleHom : Universal.CompatibleHom B (Universal A) where
  hom J := (Universal.inclusion A J).comp (e.localIso J).symm.toMonoidHom
  compatible := by
    intro J K h b
    obtain ⟨a, rfl⟩ := e.localIso J |>.surjective b
    simp only [MonoidHom.comp_apply]
    have hc := e.commutes J K h a
    rw [← hc]
    change Universal.inclusion A K
        ((e.localIso K).symm (e.localIso K (A.map J K h a))) =
      Universal.inclusion A J ((e.localIso J).symm (e.localIso J a))
    simp only [MulEquiv.symm_apply_apply]
    exact Universal.inclusion_map A J K h a

def inverseHom : Universal B →* Universal A :=
  Universal.CompatibleHom.lift B (inverseCompatibleHom A e)

/-- The universal completions of isomorphic indexed family amalgams are
isomorphic. -/
noncomputable def universalEquiv : Universal A ≃* Universal B :=
  let f : Universal A →* Universal B := toHom A e
  let g : Universal B →* Universal A := inverseHom A e
  have hf (J : ProperIndex I) (a : P J) :
      f (Universal.inclusion A J a) = Universal.inclusion B J (e.localIso J a) := by
    change toHom A e (Universal.inclusion A J a) = _
    exact Universal.CompatibleHom.lift_inclusion A (toCompatibleHom A e) J a
  have hg (J : ProperIndex I) (b : Q J) :
      g (Universal.inclusion B J b) =
        Universal.inclusion A J ((e.localIso J).symm b) := by
    change Universal.CompatibleHom.lift B (inverseCompatibleHom A e)
      (Universal.inclusion B J b) = _
    exact Universal.CompatibleHom.lift_inclusion B (inverseCompatibleHom A e) J b
  have hgf : g.comp f = MonoidHom.id (Universal A) := by
    apply Universal.hom_ext A
    intro J a
    change g (f (Universal.inclusion A J a)) = Universal.inclusion A J a
    rw [hf J a, hg J (e.localIso J a)]
    simp
  have hfg : f.comp g = MonoidHom.id (Universal B) := by
    apply Universal.hom_ext B
    intro J b
    change f (g (Universal.inclusion B J b)) = Universal.inclusion B J b
    rw [hg J b, hf J ((e.localIso J).symm b)]
    simp
  MonoidHom.toMulEquiv f g hgf hfg

@[simp] theorem universalEquiv_inclusion (J : ProperIndex I) (a : P J) :
    universalEquiv A e (Universal.inclusion A J a) =
      Universal.inclusion B J (e.localIso J a) := by
  simp only [universalEquiv, toHom]
  exact Universal.CompatibleHom.lift_inclusion A (toCompatibleHom A e) J a

end Iso

end Amalgam

end Theory.GroupTheory.IndexedFamilyAmalgam

