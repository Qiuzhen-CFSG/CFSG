module


public import Theory.Representation.BinaryAlternatingNaturalCohomology.SixTransitive
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Fixed vectors detected by a transitive A₄ in the natural A₆ section

The actual natural A₆ moved-section action admits arbitrary central and
trivial-quotient attachments. A cocycle realization by six-point permutation
displacements shows that a cocycle vanishing on a transitive two-perfect
subgroup is zero: the remaining constant displacement is a binary character.
Thus a vector fixed by such a subgroup already lies in the whole component
fixed space, with no split-extension assumption.

Source: Aschbacher–Smith B.3, I.1.6(1), and 15.3.21, pp.83,408,1127.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {L : Subgroup D}

/-- A transitive two-perfect subgroup detects every fixed vector in the
original natural A₆ moved section, without splitting either attachment. -/
theorem MovedSection.alternatingSix_fixed_of_transitive
    (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 6))
    (A : Subgroup (alternatingGroup (Fin 6))) (hA : IsPPerfect 2 A)
    (ht : ∀ i j : Fin 6, ∃ g : A, g.val.val i = j)
    (w : W) (hw : ∀ a : A, ρ (e.groupEquiv.symm a) w = w) :
    w ∈ fixedSpace ρ L := by
  let d (l : L) : s.space.toSubmodule := ⟨ρ l w - w,by
    rw [s.space_eq]
    exact Submodule.subset_span ⟨l,l.property,w,Submodule.mem_top,rfl⟩⟩
  let f : cocycles (s.action.comp L.subtype) := ⟨fun l => s.central.toSubmodule.mkQ (d l),by
    intro l k
    change s.central.toSubmodule.mkQ (d (l*k)) =
      s.central.toSubmodule.mkQ (s.space.toRepresentation l (d k)) +
        s.central.toSubmodule.mkQ (d l)
    rw [←map_add]
    apply congrArg s.central.toSubmodule.mkQ
    apply Subtype.ext
    change ρ ((l:L)*(k:L)) w-w = ρ l (ρ k w-w)+(ρ l w-w)
    rw [map_mul,Module.End.mul_apply,map_sub]
    abel⟩
  let E := cocyclesCongr (s.action.comp L.subtype) (alternatingNatural 6)
    e.groupEquiv e.linearEquiv e.intertwines
  have he : E f = 0 := BinaryPermutation.alternatingSix_cocycle_eq_zero_of_transitive A hA ht
    (E f) (by
      intro a
      change e.linearEquiv (s.central.toSubmodule.mkQ (d (e.groupEquiv.symm a))) = 0
      have hd : d (e.groupEquiv.symm a) = 0 := Subtype.ext (sub_eq_zero.mpr (hw a))
      rw [hd,map_zero,map_zero])
  have hf : f = 0 := E.injective (he.trans E.map_zero.symm)
  have hc (l : L) : d l ∈ s.central.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun c : cocycles (s.action.comp L.subtype) => c.val l) hf
  have hfix (l k : L) : ρ k (ρ l w-w) = ρ l w-w := by
    have hh := hc l
    rw [s.central_eq] at hh
    exact congrArg Subtype.val (hh k)
  let φ : L →* Multiplicative W :=
    { toFun := fun l => Multiplicative.ofAdd (ρ l w-w)
      map_one' := by simp
      map_mul' := by
        intro l k
        apply Multiplicative.toAdd.injective
        change ρ ((l:L)*(k:L)) w-w = (ρ l w-w)+(ρ k w-w)
        rw [map_mul,Module.End.mul_apply]
        have hh := hfix k l
        rw [map_sub] at hh
        rw [sub_eq_iff_eq_add.mp hh]
        abel }
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro l
    exact Abelianization.commutator_subset_ker φ Group.IsPerfect.mem_commutator
  intro l
  exact sub_eq_zero.mp (congrArg Multiplicative.toAdd (DFunLike.congr_fun hφ l))

end CFSG.Quasithin.ChapterB.QuasisimpleSource
