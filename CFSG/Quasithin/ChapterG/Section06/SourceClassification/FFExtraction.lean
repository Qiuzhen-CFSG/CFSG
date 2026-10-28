module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.Assembly
public import Theory.Representation.BinaryOffender.RankOneNormalClosure
public import Theory.GroupTheory.PCoreRestriction

/-!
# The actual FF actor in the transvection source argument

A rank-one involution generates its literal normal closure by best offenders.
The normal closure inherits faithfulness and trivial two-core. Pulling it
back along the original SQTK cover supplies the required quotient presentation;
no SQTK hypothesis on an ambient simple group is introduced.

Thus the normal closure satisfies every hypothesis of B.5.3. In the solvable
branch the proved B.1.8 construction already gives genuine internal S3 factors
and their natural moved spaces. In general the application of corrected
B.5.6 retains precisely its universal earlier input, with no classified
normal-closure or transvection-model premise.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346, first paragraph of proof;
B.5.3 and B.5.6, pp.104–105; C.5.12, p.163.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_ffHypothesis
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    letI := h.finite_group
    FFHypothesis κ (ρ.comp (normalClosure ({a} : Set G)).subtype) := by
  let := h.finite_group
  let := h.finite_cover
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  have hc : pCore 2 K = ⊥ := by
    have hle : (pCore 2 K).map K.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map K.subtype⟩
    rw [h.twoCore] at hle
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    exact Subtype.ext (hle (Subgroup.mem_map_of_mem K.subtype hx))
  let cover : SQTKQuotient κ G :=
    { Cover := Cover
      kernel := q.ker
      sqtk := h.cover_sqtk
      equiv := QuotientGroup.quotientKerEquivOfSurjective q h.quotient_surjective }
  exact ⟨h.finite_module, h.faithful.comp Subtype.val_injective, hc,
    normalClosure_offenderSubgroup_of_rank_one ρ a h.involution h.nonidentity ht.le,
    ⟨cover.subgroup K⟩⟩

theorem Hypotheses.normalClosure_solvable_factors
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hsolv : Group.IsSolvable (normalClosure ({a} : Set G))) :
    Nonempty (ChapterB.SolvableFFFactors
      (ρ.comp (normalClosure ({a} : Set G)).subtype)) := by
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let σ := ρ.comp K.subtype
  have hf := h.normalClosure_ffHypothesis ht
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have hbest : IsBestOffender σ (zpowers t) :=
    bestOffender_of_involution_displacement_le_one σ t
      (Subtype.ext h.involution)
      (fun he => h.nonidentity (congrArg Subtype.val he)) ht.le
  exact ChapterB.Glauberman.factors_nonempty σ hsolv hf.twoCore hf.faithful
    ⟨_, hbest.isOffender σ⟩

theorem Hypotheses.normalClosure_adequate_of_B_5_6
    (hB : AdequateClassificationInput.{u, v} κ)
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    NontrivialAdequateAlternative (ρ.comp (normalClosure ({a} : Set G)).subtype) := by
  let := h.finite_group
  have hf := h.normalClosure_ffHypothesis ht
  rcases hB _ _ _ hf with hs | hc
  · have haK : a ∈ normalClosure ({a} : Set G) := subset_normalClosure (Set.mem_singleton a)
    exact (h.nonidentity (congrArg Subtype.val (hs.elim ⟨a, haK⟩ 1))).elim
  · exact hc
end CFSG.Quasithin.ChapterG.Section06
