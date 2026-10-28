module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MinimalNormal
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.SolvableResidual

/-!
# Characteristic-two reduction without perfect local factors

For the same finite marked split quotient, assume characteristic two in
both marked parabolics and normal generation by U. Its unique minimal
normal subgroup R = O²(Y) is nonabelian and perfect. Indeed, if R were
abelian, its trivial two-core would force R intersect Pᵢ to have trivial
two-core. Local self-centralization kills that intersection. The proved
factorization Y = RU would then give Pᵢ = U = B, contradicting the
nontrivial simple Bruhat cell. Characteristic simplicity now gives R' = R.
Consequently R is the solvable residual, even when Y is not perfect.

The Borel contains a full Sylow subgroup of either characteristic-two
parabolic. Characteristic-two inheritance therefore also proves
F(B) = O₂(B) = U with the actual inclusion retained.

Source: the reductions used in Fong–Seitz I, Theorem A and §§1–3
(Invent. Math. 21 (1973), pp.1–16), and DGS, Groups and Graphs, pp.80–81
and224. These are elementary consequences of the stated source data;
no permitted Weyl order, root-field compatibility or Lie recognition is
assumed or proved. In particular the whole quotient is not asserted perfect.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (split : SplitData d.tits)
  (hc : ∀ i, centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
    Set (d.tits.standardParabolic {d.simple i})) ≤
    pCore 2 (d.tits.standardParabolic {d.simple i}))
  (hgen : split.unipotentClosure = ⊤)

include split hc hgen

/-- The minimal normal two-residual cannot be abelian. -/
theorem twoResidual_not_commutative : ¬ IsMulCommutative (pResidual 2 (X ⧸ d.D)) := by
  intro ha
  let R := pResidual 2 (X ⧸ d.D)
  let := ha
  have hRcore : pCore 2 R = ⊥ := by
    rw [pCore_eq_comap_of_normal, split.twoCore_eq_bot, MonoidHom.comap_bot]
    exact R.subtype.ker_eq_bot R.subtype_injective
  have hdis (i : Fin 2) : R.subgroupOf (d.tits.standardParabolic {d.simple i}) = ⊥ := by
    let A := d.tits.standardParabolic {d.simple i}
    let K := R.subgroupOf A
    let f : K →* R :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    have hf : Function.Injective f := by
      intro a b hab
      have hh : a.val.val = b.val.val :=
        congrArg (fun z : R => (z : X ⧸ d.D)) hab
      exact Subtype.ext (Subtype.ext hh)
    have hK : pCore 2 K = ⊥ := by
      have hh : (pCore 2 K).map f ≤ pCore 2 R :=
        le_sSup ⟨inferInstance, pCore_isPGroup.map f⟩
      rw [hRcore] at hh
      exact ((pCore 2 K).map_eq_bot_iff_of_injective hf).mp (le_bot_iff.mp hh)
    exact AmalgamLocalCores.normal_eq_bot_of_core_eq_bot K (hc i) hK
  have hUP (i : Fin 2) : d.tits.standardParabolic {d.simple i} ≤ split.U := by
    intro a ha
    obtain ⟨r, hr, u, hu, he⟩ := mem_sup_of_normal_left.mp
      ((d.normal_subgroup_sup_unipotent split hc hgen R (d.twoResidual_ne_bot split)) ▸
        mem_top a)
    have huP := split.U_le.trans (d.tits.B_le_standardParabolic {d.simple i}) hu
    have hrP : r ∈ d.tits.standardParabolic {d.simple i} := by
      have hh := (d.tits.standardParabolic {d.simple i}).mul_mem ha
        ((d.tits.standardParabolic {d.simple i}).inv_mem huP)
      rwa [← he, mul_inv_cancel_right] at hh
    have hrK : (⟨r,hrP⟩ : d.tits.standardParabolic {d.simple i}) ∈
        R.subgroupOf (d.tits.standardParabolic {d.simple i}) := hr
    rw [hdis i] at hrK
    have hr1 : r = 1 := congrArg
      (fun z : d.tits.standardParabolic {d.simple i} => (z : X ⧸ d.D)) (mem_bot.mp hrK)
    simpa only [← he, hr1, one_mul] using hu
  have he : d.tits.standardParabolic {d.simple 0} = d.tits.standardParabolic ∅ := by
    rw [d.tits.standardParabolic_empty]
    exact le_antisymm ((hUP 0).trans split.U_le) (d.tits.B_le_standardParabolic _)
  have hh := (d.tits.standardParabolic_eq_iff
    (Set.singleton_subset_iff.mpr (d.simple_mem 0)) (Set.empty_subset _)).mp he
  exact Set.not_nonempty_empty (hh ▸ Set.singleton_nonempty _)

/-- Characteristic simplicity and noncommutativity force perfectness. -/
theorem twoResidual_isPerfect : Group.IsPerfect (pResidual 2 (X ⧸ d.D)) := by
  apply Group.isPerfect_def.mpr
  obtain hb | ht := d.twoResidual_characteristic_simple split hc hgen
    (_root_.commutator (pResidual 2 (X ⧸ d.D)))
  · exact (d.twoResidual_not_commutative split hc hgen
      ((commutator_eq_bot_iff _).mp hb)).elim
  · exact ht

/-- The two-residual is the intrinsic solvable residual of the same quotient. -/
theorem twoResidual_eq_solvableResidual : pResidual 2 (X ⧸ d.D) = solvableResidual (X ⧸ d.D) := by
  let := d.twoResidual_isPerfect split hc hgen
  let : Group.IsNilpotent ((X ⧸ d.D) ⧸ pResidual 2 (X ⧸ d.D)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  exact le_antisymm (le_solvableResidual_of_isPerfect _)
    (solvableResidual_le_of_solvable_quotient _)

omit hgen in
/-- The Borel has precisely the specified unipotent subgroup as its Fitting subgroup. -/
theorem borel_fitting_eq_unipotent : fittingSubgroup d.tits.B = split.U.subgroupOf d.tits.B := by
  have hg := generalizedFitting_eq_pCore_of_sylow_overgroup split.sylow d.tits.B
    (d.tits.standardParabolic {d.simple 0}) split.U_le
    (d.tits.B_le_standardParabolic _) (hc 0)
  rw [← split.borel_twoCore]
  exact le_antisymm ((fitting_le_generalizedFitting _).trans hg.le)
    (pCore_le_fitting _ 2)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
