module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarResidualContract

/-!
# The marked residual in the C.2.7 star stabilizer

The C.2.7 central-kernel bound makes the kernel of the restricted map from K
solvable. Since K is perfect with K/O₂(K) ≃ A₅, its solvable radical is O₂(K).
Thus prime-core transport preserves the original A₅ marking. Normality in H
and H ∩ Gᵤ = K Tᵤ give the normal star image and its two-group supplement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.68(2),
printed pp. 1071–1072, and C.2.7(1), printed pp. 145–147.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

include d in
private theorem K_perfect : Group.IsPerfect (K F) := by
  let := d.component.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (K_le_H F)).toMonoidHom)
    (subgroupOfEquivOfLe (K_le_H F)).surjective

include d in
private theorem K_radical_eq_core : solvableRadical (K F) = pCore 2 (K F) := by
  let := d.K_perfect
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let := d.KCoreAlternatingFive.isSimpleGroup
  exact PerfectCoreTwoExtension.radical_eq_core

private theorem K_le_starLocal (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : K F ≤ (F.H ⊓ d.fixedCentralizer u) ⊓ Lu :=
  le_inf (le_inf (K_le_H F) (d.K_le_fixedCentralizer u h.member)) h.larger.le

/-- The literal K-image lies inside precisely the C.2.7 stabilizer. -/
theorem fixedComponent_starImage_K_le_starM (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    starImage Lu (d.fixedCore u) (K F) ≤
      starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) :=
  map_mono (subgroupOf_mono _ (d.K_le_starLocal u h))

/-- The original K-image, restricted to the actual local star stabilizer. -/
def fixedStarResidual (u : F.U) (Lu : Subgroup G) :
    Subgroup (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :=
  (starImage Lu (d.fixedCore u) (K F)).subgroupOf
    (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))

/-- The witness is exactly the marked K-image, including its ambient embedding. -/
theorem fixedStarResidual_map_subtype (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    (d.fixedStarResidual u Lu).map
        (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subtype =
      starImage Lu (d.fixedCore u) (K F) :=
  map_subgroupOf_eq_of_le (d.fixedComponent_starImage_K_le_starM u h)

/-- The literal star quotient map on K, with codomain the marked witness. -/
def KToFixedStarResidual (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : K F →* d.fixedStarResidual u Lu where
  toFun k := ⟨⟨QuotientGroup.mk' (starKernel Lu (d.fixedCore u))
      ⟨k, (h.larger.le.trans le_sup_left) k.property⟩,
    d.fixedComponent_starImage_K_le_starM u h
      (mem_map_of_mem _ (show (⟨k, (h.larger.le.trans le_sup_left) k.property⟩ :
        (Lu ⊔ d.fixedCore u : Subgroup G)) ∈ (K F).subgroupOf _ from k.property))⟩,
    mem_map_of_mem _ k.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- This map uses the original representatives in LᵤRᵤ/C(V). -/
theorem KToFixedStarResidual_apply (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) (k : K F) :
    ((d.KToFixedStarResidual u h k).val.val : StarQuotient Lu (d.fixedCore u)) =
      QuotientGroup.mk' (starKernel Lu (d.fixedCore u))
        ⟨k, (h.larger.le.trans le_sup_left) k.property⟩ := rfl

theorem KToFixedStarResidual_surjective (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : Function.Surjective (d.KToFixedStarResidual u h) := by
  intro b
  obtain ⟨x, hx, hxb⟩ := b.property
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxb)⟩

/-- Perfectness is inherited from the genuine component K in H. -/
theorem fixedStarResidual_perfect (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : Group.IsPerfect (d.fixedStarResidual u Lu) := by
  let := d.K_perfect
  exact Group.IsPerfect.ofSurjective (f := d.KToFixedStarResidual u h)
    (d.KToFixedStarResidual_surjective u h)

/-- Restrict the central-kernel bound to K before passing to its radical. -/
theorem KToFixedStarResidual_ker_isTwoGroup (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    IsPGroup 2 (d.KToFixedStarResidual u h).ker := by
  let f := d.KToFixedStarResidual u h
  let q := (QuotientGroup.mk' (pCore 2 Lu)).comp (inclusion h.larger.le)
  have hq : IsPGroup 2 q.ker := by
    rw [show q.ker = (pCore 2 Lu).comap (inclusion h.larger.le) by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective h.larger.le)
  let : Group.IsNilpotent q.ker := hq.isNilpotent
  let C := (center (Lu ⧸ pCore 2 Lu)).comap q
  let : Group.IsSolvable (center (Lu ⧸ pCore 2 Lu)) :=
    Group.isSolvable_of_comm fun x y =>
      Subtype.ext (mem_center_iff.mp x.property y).symm
  let : Group.IsSolvable C := isSolvable_comap_of_solvable_ker q _
  have hkC : f.ker ≤ C := by
    intro k hk
    apply d.fixedComponent_coreToStar_ker_le_center u h c27
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact congrArg (fun b : d.fixedStarResidual u Lu => b.val.val)
      (show f k = 1 from hk)
  have hs : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hkC) (inclusion_injective hkC)
  have hk : f.ker ≤ pCore 2 (K F) := by
    rw [← d.K_radical_eq_core]
    exact le_solvableRadical _ inferInstance hs
  exact pCore_isPGroup.to_le hk

/-- The A₅ isomorphism descends the original qH marking through the actual map. -/
def fixedStarResidualCoreAlternatingFive (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    (d.fixedStarResidual u Lu ⧸ pCore 2 (d.fixedStarResidual u Lu)) ≃*
      alternatingGroup (Fin 5) :=
  ((d.KToFixedStarResidual u h).pCoreQuotientEquiv
    (d.KToFixedStarResidual_surjective u h)
    (d.KToFixedStarResidual_ker_isTwoGroup u h c27)).symm.trans d.KCoreAlternatingFive

/-- The marking agrees with qH on every original K representative. -/
theorem fixedStarResidualCoreAlternatingFive_mk (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) (k : K F) :
    d.fixedStarResidualCoreAlternatingFive u h c27
      (QuotientGroup.mk' (pCore 2 (d.fixedStarResidual u Lu))
        (d.KToFixedStarResidual u h k)) = d.KToAlternatingFive k := by
  let e := (d.KToFixedStarResidual u h).pCoreQuotientEquiv
    (d.KToFixedStarResidual_surjective u h)
    (d.KToFixedStarResidual_ker_isTwoGroup u h c27)
  change d.KCoreAlternatingFive (e.symm _) = _
  have he : e (QuotientGroup.mk' (pCore 2 (K F)) k) =
      QuotientGroup.mk' (pCore 2 (d.fixedStarResidual u Lu))
        (d.KToFixedStarResidual u h k) := rfl
  rw [← he, e.symm_apply_apply, d.KCoreAlternatingFive_mk]

/-- K is normal only in the local stabilizer, via its original normality in H. -/
theorem fixedStarResidual_normal (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : (d.fixedStarResidual u Lu).Normal := by
  let J := Lu ⊔ d.fixedCore u
  let A := (K F).subgroupOf J
  let q := QuotientGroup.mk' (starKernel Lu (d.fixedCore u))
  have hn : (((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf J) ≤ normalizer (A : Set J) := by
    rw [← subgroupOf_normalizer_eq (h.larger.le.trans le_sup_left)]
    exact subgroupOf_mono _ ((inf_le_left.trans inf_le_left).trans (H_normalizes_K F))
  exact normal_subgroupOf_of_le_normalizer
    ((map_mono (f := q) hn).trans (A.le_normalizer_map q))

private theorem starLocal_sup (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    (F.H ⊓ d.fixedCentralizer u) ⊓ Lu = K F ⊔ (d.fixedSylow u ⊓ Lu) := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (K F : Set G) * (d.fixedSylow u : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left (K F) (d.fixedSylow u)
        (show d.fixedSylow u ≤ normalizer (K F : Set G) from
          inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))),
        ← d.fixedCentralizer_inter_H u h.member]
      exact hx.1
    obtain ⟨k, hk, t, ht, rfl⟩ := hxprod
    apply Subgroup.mul_mem_sup hk
    refine ⟨ht, ?_⟩
    change t ∈ Lu
    have hh := Lu.mul_mem (Lu.inv_mem (h.larger.le hk)) hx.2
    simpa only [inv_mul_cancel_left] using hh
  · exact sup_le (d.K_le_starLocal u h)
      (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans (F.invariant 1)))
        (inf_le_left.trans inf_le_right)) inf_le_right)

/-- The image of Tᵤ ∩ Lᵤ is an actual two-group supplement in M*. -/
theorem fixedStarResidual_quotient_isTwoGroup (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    let := d.fixedStarResidual_normal u h
    IsPGroup 2 ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) ⧸
      d.fixedStarResidual u Lu) := by
  let := d.fixedStarResidual_normal u h
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  let P := starImage Lu (d.fixedCore u) (d.fixedSylow u ⊓ Lu)
  have hp : IsPGroup 2 P :=
    ((T.isPGroup'.to_le (inf_le_left.trans inf_le_left)).comap_subtype).map _
  have hs : starImage Lu (d.fixedCore u) (K F) ⊔ P = M := by
    dsimp only [M, starM]
    rw [d.starLocal_sup u h]
    unfold starImage
    rw [subgroupOf_sup (h.larger.le.trans le_sup_left)
      (inf_le_right.trans le_sup_left), Subgroup.map_sup]
    rfl
  have hPM : P ≤ M := hs ▸ le_sup_right
  apply isPGroup_quotient_of_sup_eq_top (d.fixedStarResidual u Lu) (P.subgroupOf M)
    hp.comap_subtype
  rw [fixedStarResidual, ← subgroupOf_sup (d.fixedComponent_starImage_K_le_starM u h) hPM,
    hs, subgroupOf_self]

/-- Both residuals are the marked K-image in the literal star stabilizer. -/
theorem fixedStarM_residuals (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    pResidual 2 (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) =
        d.fixedStarResidual u Lu ∧
      solvableResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) =
        d.fixedStarResidual u Lu := by
  let := d.fixedStarResidual_normal u h
  let := d.fixedStarResidual_perfect u h
  exact PerfectCoreTwoExtension.residuals _ (d.fixedStarResidual_quotient_isTwoGroup u h)

/-- The concrete local extension premise for both C.2.7 model comparisons. -/
theorem fixedStarM_hasA5TwoResidual (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    Nonquasisimple.HasA5TwoResidual
      (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) := by
  exact ⟨d.fixedStarResidual u Lu, d.fixedStarResidual_normal u h,
    d.fixedStarResidual_perfect u h, ⟨d.fixedStarResidualCoreAlternatingFive u h c27⟩,
    d.fixedStarResidual_quotient_isTwoGroup u h⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
