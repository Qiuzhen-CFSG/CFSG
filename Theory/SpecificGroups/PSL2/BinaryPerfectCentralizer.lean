module
public import Theory.SpecificGroups.PGL2.PerfectCentralizer
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator

/-!
# Centralizers of perfect subgroups in binary PSL₂ automorphisms

A nontrivial perfect subgroup has trivial centralizer in PGL₂, hence also
in PSL₂. Its inner image's automorphism centralizer therefore embeds in
the cyclic field-automorphism quotient. A perfect subgroup of the inner
group also has trivial two-core, by the binary SL₂ Borel argument.

Consequently, if a two-group R mutually normalizes that inner image and
Y centralizes it, the identity [R,Y] = R forces R = 1. This retains the
actual embedding and requires no subfield marking or prime-order lift.
Source application: Aschbacher–Smith, original 4.3.16(1) and its elimination,
printed p.618; `NonblockEndgameSieveExclusionsBinaryMovement`.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
noncomputable section
variable {F : Type*} [Field F]

/-- A nontrivial perfect subgroup has trivial centralizer in the actual PSL₂ group. -/
theorem centralizer_eq_bot_of_perfect (H : Subgroup (Group F))
    [_root_.Group.IsPerfect H] (hne : H ≠ ⊥) :
    centralizer (H : Set (Group F)) = ⊥ := by
  let f : Group F →* PGL(2,F) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let : _root_.Group.IsPerfect (H.map f) := _root_.Group.IsPerfect.map f
  have hn : H.map f ≠ ⊥ := fun he => hne ((H.map_eq_bot_iff_of_injective hf).mp he)
  have hc := Theory.PGL2.centralizer_eq_bot_of_perfect (H.map f) hn
  apply bot_unique
  intro x hx
  have hx' : f x ∈ centralizer (H.map f : Set (PGL(2,F))) := by
    rintro _ ⟨y,hy,rfl⟩
    simpa only [← map_mul] using congrArg f (hx y hy)
  rw [hc, mem_bot] at hx'
  exact mem_bot.mpr (hf (hx'.trans (map_one f).symm))

variable [Finite F] [CharP F 2]

/-- The full automorphism centralizer embeds in the cyclic outer quotient. -/
theorem inner_image_centralizer_isCyclic (H : Subgroup (Group F))
    [_root_.Group.IsPerfect H] (hne : H ≠ ⊥) :
    IsCyclic (centralizer (H.map (MulAut.conj : Group F →* MulAut (Group F)) : Set (MulAut (Group F)))) := by
  rw [Theory.GroupTheory.PerfectSubgroupAutomorphismFixer.inner_centralizer_eq_fixer]
  let C := fixingSubgroup (MulAut (Group F)) (H : Set (Group F))
  let q := QuotientGroup.mk' (inner F)
  let : IsCyclic (MulAut (Group F) ⧸ inner F) := outer_isCyclic F
  apply isCyclic_of_injective (q.comp C.subtype)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hi : (a : MulAut (Group F)) ∈ inner F := (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨x,hx⟩ := hi
  have hfix := (mem_fixingSubgroup_iff _).mp a.property
  have hc : x ∈ centralizer (H : Set (Group F)) := by
    intro y hy
    have hh := hfix y hy
    rw [← hx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [centralizer_eq_bot_of_perfect H hne, mem_bot] at hc
  apply mem_bot.mpr
  apply Subtype.ext
  change (a : MulAut (Group F)) = 1
  simpa only [hc, map_one] using hx.symm

/-- A perfect subgroup consisting of inner binary PSL₂ automorphisms has trivial two-core. -/
theorem perfect_inner_subgroup_twoCore_eq_bot
    (D : Subgroup (MulAut (Group F))) [_root_.Group.IsPerfect D]
    (hi : D ≤ inner F) : pCore 2 D = ⊥ := by
  have hconj : Function.Injective (MulAut.conj : Group F →* MulAut (Group F)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro g hg
    exact psl2_conj_eq_one_implies g hg
  let e := MonoidHom.ofInjective hconj
  let f : D →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (sl2QuotientEquiv F).symm.toMonoidHom.comp
      (e.symm.toMonoidHom.comp (D.subtype.codRestrict (inner F) (fun d => hi d.property)))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : inner F => (z : MulAut (Group F)))
      (e.symm.injective ((sl2QuotientEquiv F).symm.injective hxy))
  have hk := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker f
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hf] at hk
  exact bot_unique hk

/-- A mutually normalizing two-group cannot be moved by this centralizer. -/
theorem twoGroup_eq_bot_of_moved_by_centralizer (H : Subgroup (Group F))
    [_root_.Group.IsPerfect H] (hne : H ≠ ⊥)
    (R Y : Subgroup (MulAut (Group F))) (hR : IsPGroup 2 R)
    (hHR : H.map MulAut.conj ≤ normalizer (R : Set (MulAut (Group F))))
    (hRH : R ≤ normalizer (H.map MulAut.conj : Set (MulAut (Group F))))
    (hY : Y ≤ centralizer (H.map MulAut.conj : Set (MulAut (Group F))))
    (hmoved : ⁅R,Y⁆ = R) : R = ⊥ := by
  let X := H.map (MulAut.conj : Group F →* MulAut (Group F))
  let : _root_.Group.IsPerfect X := _root_.Group.IsPerfect.map _
  have hcore : pCore 2 X = ⊥ := perfect_inner_subgroup_twoCore_eq_bot X (map_le_range _ _)
  have hc : R ≤ centralizer (X : Set (MulAut (Group F))) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [commutator_comm]
    apply bot_unique
    have hh := commutator_le_pCore_of_mutual_normalization X R hR hHR hRH
    simpa only [hcore, Subgroup.map_bot] using hh
  let C := centralizer (X : Set (MulAut (Group F)))
  let : IsCyclic C := inner_image_centralizer_isCyclic H hne
  have hzero : ⁅C,C⁆ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  rw [← hmoved]
  exact bot_unique ((commutator_mono hc hY).trans hzero.le)
end
end Theory.PSL2
