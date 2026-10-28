module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarResidualContract

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarLocalResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.BlockComparisons
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.RankOne
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
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open ChapterB.QuasisimpleSource
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem KToFixedStarResidual_ker_isTwoGroup_of_source (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    IsPGroup 2 (d.KToFixedStarResidual u h).ker := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  have hkstar := (ChapterC.C27Source.kernel_offender_of_normal_input
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)).1
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
    apply FullSieve.coreToStar_ker_le_center_of_bound
      (d.fixedCore_normalizes_component u h) hkstar.upper
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact congrArg (fun b : d.fixedStarResidual u Lu => b.val.val)
      (show f k = 1 from hk)
  have hs : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hkC) (inclusion_injective hkC)
  have hk : f.ker ≤ pCore 2 (K F) := by
    have hp : Group.IsPerfect (K F) := by
      let := d.component.perfect
      exact Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (K_le_H F)).toMonoidHom)
        (subgroupOfEquivOfLe (K_le_H F)).surjective
    let := hp
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let := d.KCoreAlternatingFive.isSimpleGroup
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact le_solvableRadical _ inferInstance hs
  exact pCore_isPGroup.to_le hk


theorem fixedStarM_hasA5TwoResidual_of_source (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    Nonquasisimple.HasA5TwoResidual
      (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) := by
  let e := ((d.KToFixedStarResidual u h).pCoreQuotientEquiv
    (d.KToFixedStarResidual_surjective u h)
    (d.KToFixedStarResidual_ker_isTwoGroup_of_source u h)).symm.trans d.KCoreAlternatingFive
  exact ⟨d.fixedStarResidual u Lu, d.fixedStarResidual_normal u h,
    d.fixedStarResidual_perfect u h, ⟨e⟩, d.fixedStarResidual_quotient_isTwoGroup u h⟩
theorem fixedComponent_C27_rankOne_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hCJ : starImage Lu (d.fixedCore u) Lu ≤ offenderSubgroup (starRepresentation Lu (d.fixedCore u)))
    (s : MovedSection
      ((starRepresentation Lu (d.fixedCore u)).comp (offenderSubgroup (starRepresentation Lu (d.fixedCore u))).subtype)
      ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))))
    (k : BinaryField)
    (natural : ActionEquiv (s.action.comp
      ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))).subtype)
      (linearNatural k 2))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage Lu (d.fixedCore u) Lu).subgroupOf
        (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))),
        B = (S : Subgroup _).map ((starImage Lu (d.fixedCore u) Lu).subgroupOf
          (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))).subtype) :
False := by
  have hb := (d.fixedComponent_C27_rankOne_geometry u h hCJ s k natural hratio hoff).2.1
  let e : starImage Lu (d.fixedCore u) Lu ≃* SL(2,k.Carrier) :=
    (subgroupOfEquivOfLe hCJ).symm.trans natural.groupEquiv
  obtain ⟨S,hS⟩ := hb
  have hs : ChapterF.Source.RankOneSylowFacts S :=
    ChapterF.Source.rankOneSylowFacts_of_equiv S e
      (ChapterF.Source.Linear.all_sylows _
        (ChapterF.Source.Linear.standard_facts k.Carrier k.degree k.degree_pos k.card_eq) _)
  let : Group.IsSolvable (normalizer (S : Set (starImage Lu (d.fixedCore u) Lu))) := hs.solvable
  have hsolv : Group.IsSolvable (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) := by
    rw [hS]
    exact Group.isSolvable_of_surjective
      ((starImage Lu (d.fixedCore u) Lu).subtype.subgroupMap_surjective _)
  let := hsolv
  exact (d.fixedStarM_hasA5TwoResidual_of_source u h).not_isSolvable

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
