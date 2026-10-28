module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import Theory.Representation.RepEquiv
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Faithfulness on the actual moved quotient in B.5.1

An element of L in the quotient kernel acts trivially on the three successive
sections of 0 ≤ C_[V,L](L) ≤ [V,L] ≤ V. Its displacement has cube zero, so in
characteristic two its fourth power is the identity. Thus the kernel is a
two-group and the already proved triviality of O₂(L) makes it trivial.
Faithfulness on F*(LA)=L then gives faithfulness on every LA with A a two-group.
The quotient equivalence also transports the given Irr⁺ condition to the
literal action in MovedSection, without any classification premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99 (the coprime-action and LT-faithfulness step).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Kernel elements have all displacements in the literal central submodule. -/
theorem kernel_displacement (s : MovedSection ρ L) (g : G) (hg : g ∈ s.action.ker) (v : s.space.toSubmodule) :
    s.space.toRepresentation g v - v ∈ fixedSpace s.space.toRepresentation L := by
  have he := LinearMap.congr_fun hg (s.central.toSubmodule.mkQ v)
  change s.central.toSubmodule.mkQ (s.space.toRepresentation g v) =
    s.central.toSubmodule.mkQ v at he
  have hv := (Submodule.Quotient.eq s.central.toSubmodule).mp he
  rwa [s.central_eq] at hv

/-- The component kernel on the moved central quotient has exponent dividing four. -/
theorem component_kernel_isTwoGroup (s : MovedSection ρ L) (hf : Function.Injective ρ) :
    IsPGroup 2 (s.action.comp L.subtype).ker := by
  classical
  intro x
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply hf
  rcases subsingleton_or_nontrivial V with hV | hV
  · let := hV
    exact Subsingleton.elim _ _
  let := hV
  let : CharP (Module.End (ZMod 2) V) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  change ρ ((x.val : G) ^ (2 ^ 2)) = ρ (1 : G)
  rw [map_pow, map_one]
  let d : Module.End (ZMod 2) V := ρ (x.val : G) - 1
  have hd (v : V) : d v ∈ s.space.toSubmodule := by
    rw [s.space_eq]
    exact Submodule.subset_span ⟨x.val, x.val.property, v, Submodule.mem_top, rfl⟩
  have hc (v : V) : d (d v) ∈ fixedSpace ρ L := by
    have hh := kernel_displacement s (x.val : G) x.property ⟨d v, hd v⟩
    intro l
    exact congrArg Subtype.val (hh l)
  have hn : d ^ 3 = 0 := by
    ext v
    change d (d (d v)) = 0
    exact sub_eq_zero.mpr (hc v x.val)
  have hn4 : d ^ (2 ^ 2) = 0 := by
    rw [show 2 ^ 2 = 3 + 1 from rfl, pow_succ, hn, zero_mul]
  have hp := sub_pow_char_pow_of_commute (R := Module.End (ZMod 2) V)
    2 2 (Commute.one_right (ρ (x.val : G)))
  rw [one_pow] at hp
  exact sub_eq_zero.mp (hp.symm.trans hn4)

/-- The original source hypothesis makes L faithful on its actual moved quotient. -/
theorem component_faithful [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) :
    Function.Injective (s.action.comp L.subtype) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hk : (s.action.comp L.subtype).ker ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, component_kernel_isTwoGroup s h.faithful⟩
  rw [local_twoCore_eq_bot L L h.fitting h.twoCore le_rfl] at hk
  exact (MonoidHom.ker_eq_bot_iff _).mp (le_bot_iff.mp hk)

/-- Faithfulness on F*(G) implies faithfulness on a finite ambient group. -/
theorem faithful_of_fitting_restriction [Finite G]
    (hf : Function.Injective (ρ.comp (generalizedFitting G).subtype)) :
    Function.Injective ρ := by
  have hi : ρ.ker ⊓ generalizedFitting G ≤ ⊥ := by
    intro x hx
    have he : (⟨x, hx.2⟩ : generalizedFitting G) = 1 := hf (by
      change ρ x = ρ 1
      simpa only [map_one] using (show ρ x = 1 from hx.1))
    exact congrArg Subtype.val he
  have hc : ρ.ker ≤ centralizer (generalizedFitting G : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_le_inf _ _).trans hi))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_bot_iff.mp (fun x hx => hi ⟨hx, QuasisimpleSections.centralizer_generalizedFitting_le (hc hx)⟩)

/-- Each literal LA acts faithfully on the moved quotient when A is a two-subgroup. -/
theorem local_faithful [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    Function.Injective (s.action.comp (L ⊔ A).subtype) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  apply faithful_of_fitting_restriction
  rw [local_generalizedFitting L A h.fitting h.twoCore hA]
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : L => (z : G)) (component_faithful h s
    (show s.action.comp L.subtype ⟨x.val, x.property⟩ =
      s.action.comp L.subtype ⟨y.val, y.property⟩ from hxy))

/-- Identify the two literal central-quotient conventions, with their L-actions. -/
noncomputable def centralQuotientEquiv (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) :
    RepEquiv (s.action.comp L.subtype)
      (centralQuotientRepresentation ρ L s.space.toSubmodule hI.choose) := by
  have hc : s.central.toSubmodule =
      (fixedSpace ρ L).comap s.space.toSubmodule.subtype := by
    rw [s.central_eq]
    ext v
    constructor
    · intro hv g
      exact congrArg Subtype.val (hv g)
    · intro hv g
      exact Subtype.ext (hv g)
  refine ⟨Submodule.Quotient.equiv _ _ (LinearEquiv.refl (ZMod 2) _)
    (by simpa using hc), ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

/-- Irr⁺ supplies irreducibility for the actual quotient action stored in s. -/
theorem moved_action_irreducible (s : MovedSection ρ L)
    (hI : IsIrrPlus ρ L s.space.toSubmodule) :
    IsIrreducible (s.action.comp L.subtype) :=
  (centralQuotientEquiv s hI).irreducible_of_euqiv hI.choose_spec.2

end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
