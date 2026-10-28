module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent.Projections
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.SeedSpace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.CyclicInvariantExtension
public import Theory.Representation.BinaryOffender.FaithfulRankOne


/-!
# Recognition of the second natural component in B.5.9

A proper natural seed forces the minimal offender to have order greater than
two: otherwise restriction to its noncentral seed has equal rank and fixed
codimension, and B.1.5(2) supplies a supplement forcing U=W.

For a second moved component M not containing A, the preliminary alternatives
therefore leave only a natural seed or a natural action on the whole moved
space. In the latter case the action of MA on W is irreducible, so O₂(MA)
fixes W. The natural M-action gives [W,M]=W, proving
[C_V(O₂(MA)),M]=W. Restricting the actual ambient W-action to MA then supplies
the requested seed with the same field, intertwiner and inner action.

The only unproved earlier input is the universal preliminary conclusion
already in Setup, whose producer is `qt-b05-component-preliminary-actions`.
No adequate-counterexample hypothesis or further classification input is used.
The parent `qt-b05-natural-second-component` supplies M using its existing
selection theorem and retains assembly of the two-component configuration.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the symmetry argument in the final paragraph.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem seed_not_fixed {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (seed : NaturalSeed ρ A L) :
    ¬ seed.space.toSubmodule ≤ fixedSpace ρ A := by
  intro hfix
  have hstab : L ≤ subspaceStabilizer ρ seed.space.toSubmodule := by
    apply le_subspaceStabilizer
    intro l hl w hw
    exact seed.space.apply_mem_toSubmodule ⟨l, mem_sup_left hl⟩ hw
  have hfixL := le_fixedSpace_commutator_of_invariant ρ hstab hfix
  rw [hLA] at hfixL
  have hzero := ExtensionConsequences.invariants_of_equiv seed.natural
    (ExtensionConsequences.linearNatural_invariants seed.field (by decide : 2 ≤ 3))
  let : Nontrivial seed.space.toSubmodule := seed.natural.linearEquiv.symm.injective.nontrivial
  obtain ⟨w, hw⟩ := exists_ne (0 : seed.space.toSubmodule)
  apply hw
  apply (Submodule.mem_bot (ZMod 2)).mp
  rw [← hzero]
  intro l
  exact Subtype.ext (hfixL w.property l)

variable [Finite G]

/-- The source inequality |A|>2 follows from properness of the original seed. -/
theorem proper_seed_card_gt_two {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hLA : ⁅L,A⁆ = L)
    (seed : NaturalSeed ρ A L) (hproper : seed.space.toSubmodule < moved ρ L) :
    2 < Nat.card A := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  let : IsElementaryAbelian 2 A := setup.minimal.1.1.2
  have hn := seed_not_fixed ρ hLA seed
  have hstab : A ≤ subspaceStabilizer ρ seed.space.toSubmodule := by
    apply le_subspaceStabilizer
    intro a ha w hw
    exact seed.space.apply_mem_toSubmodule ⟨a, mem_sup_right ha⟩ hw
  have hb := setup.minimal.1.restricted ρ seed.space.toSubmodule hstab hn
  have hr := rank_subspaceKernel_add_image ρ seed.space.toSubmodule A hstab
    (IsElementaryAbelian.isPGroup 2 A)
  have hp := fixedCodim_pos_of_faithful
    (subspaceImageRepresentation ρ seed.space.toSubmodule)
    (subspaceImageRepresentation_injective ρ seed.space.toSubmodule) hb.1.1
  have hoff := (hb.isOffender _).2
  by_contra! hcard
  have hrank : rank A ≤ 1 := by
    calc
      rank A = Nat.log 2 (Nat.card A) := rfl
      _ ≤ Nat.log 2 2 := Nat.log_monotone hcard
      _ = 1 := by decide
  have he : rank (restrictedSubgroup ρ seed.space.toSubmodule A) =
      fixedCodim (subspaceImageRepresentation ρ seed.space.toSubmodule)
        (restrictedSubgroup ρ seed.space.toSubmodule A) := by omega
  have hs := (setup.minimal.faithful_span_of_image_rank_eq ρ
    seed.space.toSubmodule hstab hn he).2
  have hw := PreliminaryActions.moved_le_of_supplement ρ hLA seed.space hs
  exact hproper.not_ge hw

omit [Finite G] in
private theorem natural_space_commutator {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype) (linearNatural F 3)) :
    subspaceCommutator ρ s.space.toSubmodule L = s.space.toSubmodule := by
  let σ : Representation (ZMod 2) L s.space.toSubmodule :=
    s.space.toRepresentation.comp L.subtype
  let : IsIrreducible σ := ExtensionConsequences.irreducible_of_equiv e
    (ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 3))
  let : Nontrivial s.space.toSubmodule := e.linearEquiv.symm.injective.nontrivial
  have hzero : σ.invariants = ⊥ := ExtensionConsequences.invariants_of_equiv e
    (ExtensionConsequences.linearNatural_invariants F (by decide : 2 ≤ 3))
  let D := subspaceCommutator ρ s.space.toSubmodule L
  have hD := subspaceCommutator_invariant ρ s.space.toSubmodule L
  let T : Subrepresentation σ :=
    ⟨D.comap s.space.toSubmodule.subtype, fun l w hw => (hD l.property w).2 hw⟩
  have hT : T ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := exists_ne (0 : s.space.toSubmodule)
    apply hw
    apply (Submodule.mem_bot (ZMod 2)).mp
    rw [← hzero]
    intro l
    have hd : σ l w - w ∈ T := by
      exact Submodule.subset_span ⟨l, l.property, w, w.property, rfl⟩
    rw [hbot] at hd
    exact sub_eq_zero.mp hd
  have ht : T = ⊤ := (eq_bot_or_eq_top T).resolve_left hT
  apply le_antisymm
  · apply subspaceCommutator_le_of_invariant
    apply le_subspaceStabilizer
    intro l hl w hw
    exact s.space.apply_mem_toSubmodule l hw
  · intro w hw
    have hh : (⟨w,hw⟩ : s.space.toSubmodule) ∈ T := by rw [ht]; trivial
    exact hh

/-- The whole natural moved space is the literal two-core seed. -/
theorem naturalSeedSpace_eq_of_natural_moved {A M : Subgroup G}
    (s : MovedSection ρ M) (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp M.subtype) (linearNatural F 3)) :
    naturalSeedSpace ρ M A = s.space.toSubmodule := by
  let σ : Representation (ZMod 2) ↥(M ⊔ A) s.space.toSubmodule :=
    s.space.toRepresentation.comp (M ⊔ A).subtype
  let : Module.Finite (ZMod 2) s.space.toSubmodule :=
    Module.Finite.equiv e.linearEquiv.symm
  let : IsIrreducible (σ.comp (Subgroup.inclusion
      (show M ≤ M ⊔ A from le_sup_left))) :=
    ExtensionConsequences.irreducible_of_equiv e
      (ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 3))
  let : IsIrreducible σ := isIrreducible_of_comp σ
    (Subgroup.inclusion (show M ≤ M ⊔ A from le_sup_left))
  have hker := normal_p_subgroup_le_ker σ (pCore 2 ↥(M ⊔ A))
    (pCore_isPGroup (p := 2) (G := ↥(M ⊔ A)))
  have hfixed : s.space.toSubmodule ≤ fixedSpace ρ (localTwoCore M A) := by
    intro w hw q
    obtain ⟨q₀,hq₀,hq⟩ := q.property
    have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (hker hq₀))
      (⟨w,hw⟩ : s.space.toSubmodule)
    change ρ (q : G) w = w
    rw [← hq]
    exact congrArg Subtype.val he
  apply le_antisymm
  · rw [s.space_eq]
    exact PreliminaryActions.seedSpace_le_moved ρ A M
  · rw [← natural_space_commutator ρ s F e]
    exact subspaceCommutator_mono_left ρ hfixed M

/-- Transfer the whole-space natural case to a genuine MA seed. -/
theorem naturalSeed_of_natural_moved {A M : Subgroup G}
    (s : MovedSection ρ M) (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (s.space.toRepresentation.comp M.subtype) (linearNatural F 3))
    (hi : InducesInner A M) : Nonempty (NaturalSeed ρ A M) := by
  let W : Subrepresentation (ρ.comp (M ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hw => s.space.apply_mem_toSubmodule g hw⟩
  refine ⟨⟨F, ho, W, (naturalSeedSpace_eq_of_natural_moved ρ s F e).symm, ?_, hi⟩⟩
  exact e

/-- Recognition of the explicit second component chosen by the parent theorem. -/
theorem second_component_naturalSeed {K : GroupClass} {A L M : Subgroup G}
    (setup : Setup ρ K A) (hLA : ⁅L,A⁆ = L)
    (seed : NaturalSeed ρ A L) (hproper : seed.space.toSubmodule < moved ρ L)
    (hM : IsComponent G M) (hMA : ⁅M,A⁆ = M) (hAM : ¬ A ≤ M) :
    Nonempty (NaturalSeed ρ A M) := by
  let : M.Normal := setup.component_normal M hM
  let s := MovedSection.ofNormal ρ M
  rcases setup.preliminary M hM hMA s with ⟨H,hcase⟩ | seedM
  · cases hcase with
    | linearTwo F hn hsyl hs =>
      obtain ⟨T,hT⟩ := hsyl
      apply False.elim (hAM ?_)
      rw [hT]
      rintro _ ⟨t,ht,rfl⟩
      exact t.property
    | symmetricFive ha hc hs =>
      have hgt := proper_seed_card_gt_two ρ setup hLA seed hproper
      omega
    | doubleThree F ho hn hc hs => exact (hAM hc).elim
    | naturalThree F ho hn hi =>
      obtain ⟨e⟩ := hn
      exact naturalSeed_of_natural_moved ρ s F ho e hi
    | fourCover hc hk hcont hs => exact (hAM hcont).elim
  · exact ⟨seedM⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
