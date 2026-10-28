module
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.SubspaceQuotient
public import Mathlib.GroupTheory.IsPerfect


/-!
# Quotienting an elementary subgroup by the full fixed space

For a normal elementary subgroup A and a normal actor L, construct the literal
binary quotient A/C_A(L). Displacement in C_A(L) lets its action descend through
an actual group quotient. If L is perfect, this section has no L-fixed vectors:
a newly fixed lift would define a homomorphism from L into an abelian group.
The coordinate homomorphism, its exact kernel, and conjugation are retained.

Source application: MS93 (3.4), printed p.869, the action on Z-star-alpha D/D.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Representation.NormalElementaryQuotient
universe u v
variable {G : Type u} {J : Type v} [Group G] [Group J]
variable (A L : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A] [L.Normal]

/-- The full fixed space of the original normal actor. -/
def centralFixedSubrepresentation : Subrepresentation (originalAction A) where
  toSubmodule := fixedSpace (originalAction A) L
  apply_mem_toSubmodule g x hx :=
    (fixedSpace_stable_of_normalizes (originalAction A)
      (show (⊤ : Subgroup G) ≤ normalizer (L : Set G) from le_normalizer_of_normal)
      (mem_top g) x).2 hx

abbrev FixedQuotient := Additive A ⧸ fixedSpace (originalAction A) L

def fixedQuotientAction : Representation (ZMod 2) G (FixedQuotient A L) :=
  (centralFixedSubrepresentation A L).quotientRepresentation

def fixedQuotientProjection : A →* Multiplicative (FixedQuotient A L) where
  toFun a := Multiplicative.ofAdd ((fixedSpace (originalAction A) L).mkQ (Additive.ofMul a))
  map_one' := congrArg Multiplicative.ofAdd ((fixedSpace (originalAction A) L).mkQ.map_zero)
  map_mul' a b := congrArg Multiplicative.ofAdd
    ((fixedSpace (originalAction A) L).mkQ.map_add (Additive.ofMul a) (Additive.ofMul b))

omit [L.Normal] in
theorem fixedQuotientProjection_surjective : Function.Surjective (fixedQuotientProjection A L) := by
  intro w
  obtain ⟨a,ha⟩ := (fixedSpace (originalAction A) L).mkQ_surjective w.toAdd
  exact ⟨a.toMul,congrArg Multiplicative.ofAdd ha⟩

omit [L.Normal] in
theorem fixedQuotientProjection_kernel :
    (fixedQuotientProjection A L).ker = (centralizer (L : Set G)).subgroupOf A := by
  ext a
  change (fixedSpace (originalAction A) L).mkQ (Additive.ofMul a) = 0 ↔ _
  exact (Submodule.Quotient.mk_eq_zero _).trans (original_fixedSpace A L _)

theorem fixedQuotientProjection_equivariant (g : G) (a : A) :
    (fixedQuotientProjection A L (MulAut.conjNormal g a)).toAdd =
      fixedQuotientAction A L g (fixedQuotientProjection A L a).toAdd := by
  change (fixedSpace (originalAction A) L).mkQ (Additive.ofMul (MulAut.conjNormal g a)) =
    (fixedSpace (originalAction A) L).mkQ (originalAction A g (Additive.ofMul a))
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (originalAction_apply A g (Additive.ofMul a)).symm

/-- Core displacement in the full fixed subgroup makes the quotient action descend. -/
theorem exists_fixedQuotientAction_descent (q : G →* J) (hq : Function.Surjective q)
    (hc : ⁅A,q.ker⁆ ≤ centralizer (L : Set G)) :
    ∃ σ : Representation (ZMod 2) J (FixedQuotient A L),
      ∀ g : G, σ (q g) = fixedQuotientAction A L g := by
  have hk : q.ker ≤ (fixedQuotientAction A L).ker := by
    intro g hg
    change fixedQuotientAction A L g = 1
    apply LinearMap.ext
    intro w
    obtain ⟨a,rfl⟩ := (fixedSpace (originalAction A) L).mkQ_surjective w
    apply (Submodule.Quotient.eq _).mpr
    change originalAction A g a - a ∈ fixedSpace (originalAction A) L
    rw [original_fixedSpace]
    have he : ((originalAction A g a - a).toMul : G) = ⁅g,(a.toMul : G)⁆ := by
      rw [toMul_sub,div_eq_mul_inv]
      change ((originalAction A g a).toMul : G) * (a.toMul : G)⁻¹ = _
      rw [originalAction_apply]
      rfl
    rw [he]
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator hg a.toMul.property
  have hkU : q.ker ≤ (fixedQuotientAction A L).asGroupHom.ker := by
    intro g hg
    exact Units.ext (hk hg)
  let σ : Representation (ZMod 2) J (FixedQuotient A L) :=
    (Units.coeHom _).comp (q.liftOfSurjective hq ⟨(fixedQuotientAction A L).asGroupHom,hkU⟩)
  refine ⟨σ,?_⟩
  intro g
  change Units.coeHom (Module.End (ZMod 2) (FixedQuotient A L))
    ((q.liftOfSurjective hq ⟨(fixedQuotientAction A L).asGroupHom,hkU⟩) (q g)) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  exact Representation.asGroupHom_apply _ _

/-- A perfect actor has no new fixed vectors after quotienting by its full fixed space. -/
theorem fixedQuotientAction_fixed_eq_bot [Group.IsPerfect L] :
    fixedSpace (fixedQuotientAction A L) L = ⊥ := by
  apply bot_unique
  intro w hw
  obtain ⟨a,rfl⟩ := (fixedSpace (originalAction A) L).mkQ_surjective w
  have hfixed (l : L) : originalAction A l.val a - a ∈ fixedSpace (originalAction A) L :=
    (Submodule.Quotient.eq _).mp (hw l)
  let f : L →* Multiplicative (Additive A) := {
    toFun l := Multiplicative.ofAdd (originalAction A l.val a - a)
    map_one' := by simp
    map_mul' l k := by
      change originalAction A (l.val*k.val) a-a =
        (originalAction A l.val a-a)+(originalAction A k.val a-a)
      have hh := hfixed k l
      change originalAction A l.val (originalAction A k.val a-a) =
        originalAction A k.val a-a at hh
      rw [map_sub] at hh
      rw [map_mul,Module.End.mul_apply]
      calc
        _ = (originalAction A l.val (originalAction A k.val a) - originalAction A l.val a) +
          (originalAction A l.val a-a) := by abel
        _ = (originalAction A k.val a-a)+(originalAction A l.val a-a) := by rw [hh]
        _ = _ := add_comm _ _ }
  have hker : commutator L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp inferInstance] at hker
  have ha : a ∈ fixedSpace (originalAction A) L := by
    intro l
    have hl : f l = 1 := hker (mem_top l)
    exact sub_eq_zero.mp hl
  exact (Submodule.Quotient.mk_eq_zero _).mpr ha

end Representation.NormalElementaryQuotient
