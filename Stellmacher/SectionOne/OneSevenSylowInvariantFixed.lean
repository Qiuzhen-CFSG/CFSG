module
public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity
public import Stellmacher.SectionOne.OneSevenFixedCommutator

/-!
# Sylow-invariant subgroups and the canonical fixed subgroup

With transitive canonical factors and trivial E-fixed space, every subgroup
preserved by the supplied Sylow is comparable with the J-fixed subgroup.
If a coordinate moves a vector, its nonzero displacement generates its
order-two commutator line. Sylow conjugation transports this displacement
to every coordinate line. Their join contains the J-fixed subgroup.
Otherwise every coordinate fixes the entire invariant subgroup.

Consequently an invariant subgroup whose order is at least that of the
J-fixed subgroup contains it. The argument uses the original action and
actual canonical factors; it requires neither a chosen swap complement nor
a factor-count assumption. This is the invariant-subgroup step used for
the two-factor action in Stellmacher (8.4), printed p.40/PDF p.30 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne
open RankOneThreeGroupAssembly
universe u

private theorem order_two_subgroup_le_of_common_nonidentity
    {V : Type u} [Group V] [Finite V]
    (line target : Subgroup V) (hcard : Nat.card line = 2)
    (point : V) (hline : point ∈ line) (htarget : point ∈ target)
    (hne : point ≠ 1) : line ≤ target := by
  obtain ⟨chosen, hchosen, hunique⟩ := (Nat.card_eq_two_iff' (1 : line)).mp hcard
  have hpoint : (⟨point, hline⟩ : line) = chosen :=
    hunique _ (fun heq => hne (congrArg Subtype.val heq))
  intro vector hvector
  by_cases heq : vector = 1
  · exact heq ▸ target.one_mem
  · have hv : (⟨vector, hvector⟩ : line) = chosen :=
      hunique _ (fun hequality => heq (congrArg Subtype.val hequality))
    have : vector = point := congrArg Subtype.val (hv.trans hpoint.symm)
    exact this ▸ htarget

public theorem oneSeven_sylow_invariant_fixed_dichotomy
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (sylow : Sylow 2 G)
    (hgen : oneE (V := V) (sylow : Subgroup G) ⊔ (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) ⊤)
    (hfixed : FixedPoints.subgroup
      (oneE (V := V) (sylow : Subgroup G)) V = ⊥)
    (invariant : Subgroup V)
    (hstable : ∀ actor : sylow, ∀ vector ∈ invariant, actor • vector ∈ invariant) :
    invariant ≤ FixedPoints.subgroup (oneJ (V := V) (sylow : Subgroup G)) V ∨
      FixedPoints.subgroup (oneJ (V := V) (sylow : Subgroup G)) V ≤ invariant := by
  classical
  let factors := oneSevenFactors (G := G) (V := V)
  let indices := {factor : Subgroup G // factor ∈ factors}
  let generated := oneSevenGenerated (G := G) (V := V)
  let coordinate (index : indices) := (sylow : Subgroup G) ⊓ index.val
  let offenders := oneJ (V := V) (sylow : Subgroup G)
  obtain ⟨hnormal, hproduct, _⟩ := oneSeven_global_product hyp sylow
  obtain ⟨hidentify, _⟩ := oneSeven_global_identification hyp sylow
  obtain ⟨_, hcoordinates, _, hcoordinateCard⟩ :=
    sl2_product_sylow_coordinates sylow generated hnormal factors hproduct
      (fun factor hfactor => ((mem_oneSevenFactors_iff factor).mp hfactor).1)
  have hjoin : offenders = ⨆ index : indices, coordinate index :=
    hidentify.trans hcoordinates
  by_cases htrivial : ∀ index : indices,
      coordinate index ≤ fixingSubgroup G (invariant : Set V)
  · left
    have hle : offenders ≤ fixingSubgroup G (invariant : Set V) := by
      rw [hjoin]
      exact iSup_le htrivial
    intro vector hvector actor
    exact (mem_fixingSubgroup_iff (M := G)).mp (hle actor.property) vector hvector
  · right
    push Not at htrivial
    obtain ⟨index, hactive⟩ := htrivial
    obtain ⟨actor, hactor, hnotfixed⟩ := SetLike.not_le_iff_exists.mp hactive
    rw [mem_fixingSubgroup_iff] at hnotfixed
    push Not at hnotfixed
    obtain ⟨vector, hvector, hmoved⟩ := hnotfixed
    let displacement := vector⁻¹ * (actor • vector)
    have hdisplacement : displacement ∈ invariant :=
      invariant.mul_mem (invariant.inv_mem hvector)
        (hstable ⟨actor, hactor.1⟩ vector hvector)
    have hnonidentity : displacement ≠ 1 := by
      intro heq
      exact hmoved (inv_mul_eq_one.mp heq).symm
    have hlines (other : indices) : commutatorAction (coordinate other) V ≤ invariant := by
      obtain ⟨transporter, htransport⟩ := oneSeven_factor_orbit_transitive hyp sylow
        hgen hunique index.val index.property other.val other.property
      let conjugate := (transporter : G) * actor * (transporter : G)⁻¹
      have hconjugate : conjugate ∈ coordinate other := by
        refine ⟨sylow.mul_mem (sylow.mul_mem transporter.property hactor.1)
          (sylow.inv_mem transporter.property), ?_⟩
        rw [← htransport]
        exact ⟨actor, hactor.2, rfl⟩
      have hidentity : (transporter : G) • displacement =
          ((transporter : G) • vector)⁻¹ *
            (conjugate • ((transporter : G) • vector)) := by
        simp only [displacement, smul_mul', smul_inv', conjugate, mul_smul,
          inv_smul_smul]
      have hline : (transporter : G) • displacement ∈
          commutatorAction (coordinate other) V := by
        rw [hidentity, commutatorAction_eq_closure]
        exact Subgroup.subset_closure
          ⟨⟨conjugate, hconjugate⟩, (transporter : G) • vector, rfl⟩
      have hlineCard : Nat.card (commutatorAction (coordinate other) V) = 2 :=
        oneSevenFactor_involution_commutator_card_two hyp.action_faithful other.val
          (coordinate other) ((mem_oneSevenFactors_iff other.val).mp other.property)
          inf_le_right (hcoordinateCard other.val other.property)
      apply order_two_subgroup_le_of_common_nonidentity _ invariant hlineCard
        ((transporter : G) • displacement) hline (hstable transporter _ hdisplacement)
      intro heq
      exact hnonidentity (MulAction.injective (transporter : G)
        (heq.trans (smul_one (transporter : G)).symm))
    have hcommutator : commutatorAction offenders V ≤ invariant := by
      rw [commutatorAction_eq_iSup_of_eq_iSup coordinate hjoin]
      exact iSup_le hlines
    have hcover := oneSeven_fixed_le_fixed_sup_commutator hyp sylow
    rw [hfixed, bot_sup_eq] at hcover
    exact hcover.trans hcommutator

public theorem oneSeven_sylow_invariant_contains_fixed_of_card_ge
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (sylow : Sylow 2 G)
    (hgen : oneE (V := V) (sylow : Subgroup G) ⊔ (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) ⊤)
    (hfixed : FixedPoints.subgroup
      (oneE (V := V) (sylow : Subgroup G)) V = ⊥)
    (invariant : Subgroup V)
    (hstable : ∀ actor : sylow, ∀ vector ∈ invariant, actor • vector ∈ invariant)
    (hcard : Nat.card (FixedPoints.subgroup
      (oneJ (V := V) (sylow : Subgroup G)) V) ≤ Nat.card invariant) :
    FixedPoints.subgroup (oneJ (V := V) (sylow : Subgroup G)) V ≤ invariant := by
  rcases oneSeven_sylow_invariant_fixed_dichotomy hyp sylow hgen hunique hfixed
      invariant hstable with hle | hle
  · exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge
  · exact hle

end Stellmacher.SectionOne
