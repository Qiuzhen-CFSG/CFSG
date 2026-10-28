module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.TwoCore
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Context
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Inner projections and the second moved component

The natural marking makes L centerless. Its inner A-action therefore gives
actual homomorphisms A → L and A → C_G(L), with their product equal to the
original inclusion. The second image A_C has the same centralizer as A inside
C_G(L). If U is properly contained in W, then A_C is nontrivial: otherwise
A ≤ L, O₂(LA)=1, and the defining formula for U gives U=W.

If every other component centralized A, the two-group A_C would centralize
F*(G), contradicting O₂(G)=1 and generalized-Fitting self-centralization.
Thus another actual component M is moved by A. Component normality gives
[M,A]=M, and [L,A]=L shows A is not contained in M.

This constructs the second moved component, without yet identifying its
natural seed or the prime-to-three residual. No additional earlier-source
parameter is used beyond the published Setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, first three sentences of the final paragraph.
-/

public section
open scoped Pointwise
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The literal L and C_G(L) coordinates of each element of A. -/
structure InnerProjections (A L : Subgroup G) where
  left : A →* L
  right : A →* centralizer (L : Set G)
  factor : ∀ a : A, (a : G) = (left a : G) * (right a : G)

private theorem disjoint_centralizer_of_center_eq_bot (L : Subgroup G)
    (hz : center L = ⊥) : Disjoint L (centralizer (L : Set G)) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hc
  have hxc : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc l l.property)
  have hxe : (⟨x, hx⟩ : L) = 1 := by simpa only [hz, mem_bot] using hxc
  exact congrArg Subtype.val hxe

private theorem inner_le_sup {A L : Subgroup G} (hi : InducesInner A L) :
    A ≤ L ⊔ centralizer (L : Set G) := by
  intro a ha
  obtain ⟨l, hl, he⟩ := hi a ha
  have hc : l⁻¹ * a ∈ centralizer (L : Set G) := by
    intro x hx
    have hh := congrArg (fun t => l⁻¹ * t * a) (he x hx)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm
  have hmem := (L ⊔ centralizer (L : Set G)).mul_mem (mem_sup_left hl) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hmem

/-- The actual two projection homomorphisms, obtained from the direct product
L C_G(L) when L is centerless. -/
noncomputable def InnerProjections.ofInner {A L : Subgroup G}
    (hz : center L = ⊥) (hi : InducesInner A L) : InnerProjections A L := by
  classical
  let C := centralizer (L : Set G)
  have hex := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L C
    (disjoint_centralizer_of_center_eq_bot L hz)
    (le_centralizer_iff.mp le_rfl)
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  let f : A →* L × C := e.symm.toMonoidHom.comp (inclusion (inner_le_sup hi))
  refine ⟨(MonoidHom.fst L C).comp f, (MonoidHom.snd L C).comp f, ?_⟩
  intro a
  have hh := he (f a).1 (f a).2
  change (a : G) = ((f a).1 : G) * ((f a).2 : G)
  rw [← hh]
  exact congrArg Subtype.val (e.apply_symm_apply (inclusion (inner_le_sup hi) a)).symm

/-- The natural seed supplies centerlessness and the inner action used above. -/
noncomputable def innerProjections {A L : Subgroup G} (seed : NaturalSeed ρ A L) :
    InnerProjections A L :=
  InnerProjections.ofInner (seed_center_eq_bot ρ seed) seed.inner

namespace InnerProjections
variable {A L : Subgroup G} (d : InnerProjections A L)
/-- The subgroup A_C inside the original ambient group. -/
def centralProjection : Subgroup G := ((centralizer (L : Set G)).subtype.comp d.right).range

theorem centralProjection_le : d.centralProjection ≤ centralizer (L : Set G) := by
  rintro _ ⟨a, rfl⟩
  exact (d.right a).property

theorem disjoint (hz : center L = ⊥) : Disjoint L d.centralProjection :=
  (disjoint_centralizer_of_center_eq_bot L hz).mono_right d.centralProjection_le

theorem centralProjection_isPGroup (hA : IsPGroup 2 A) : IsPGroup 2 d.centralProjection :=
  hA.of_surjective _ ((centralizer (L : Set G)).subtype.comp d.right).rangeRestrict_surjective

theorem right_eq (a : A) : (d.right a : G) = (d.left a : G)⁻¹ * (a : G) := by
  rw [d.factor a, inv_mul_cancel_left]

theorem offender_le : A ≤ L ⊔ d.centralProjection := by
  intro a ha
  change (⟨a, ha⟩ : A).val ∈ _
  rw [d.factor ⟨a, ha⟩]
  exact mul_mem (mem_sup_left (d.left ⟨a, ha⟩).property) (mem_sup_right ⟨⟨a, ha⟩, rfl⟩)

theorem centralProjection_le_join : d.centralProjection ≤ L ⊔ A := by
  rintro _ ⟨a, rfl⟩
  change (d.right a : G) ∈ L ⊔ A
  rw [d.right_eq a]
  exact mul_mem (mem_sup_left (L.inv_mem (d.left a).property)) (mem_sup_right a.property)

theorem join_eq : L ⊔ A = L ⊔ d.centralProjection :=
  le_antisymm (sup_le le_sup_left d.offender_le)
    (sup_le le_sup_left d.centralProjection_le_join)

/-- The source equality C_G(A) ∩ C_G(L) = C_G(A_C) ∩ C_G(L). -/
theorem centralizer_eq :
    centralizer (A : Set G) ⊓ centralizer (L : Set G) =
      centralizer (d.centralProjection : Set G) ⊓ centralizer (L : Set G) := by
  have swap {H : Subgroup G} {x : G} (hx : x ∈ centralizer (H : Set G)) :
      H ≤ centralizer ({x} : Set G) := by
    intro h hh y hy
    have hyx : y = x := hy
    subst y
    exact (hx h hh).symm
  ext x
  constructor
  · rintro ⟨hA, hL⟩
    refine ⟨?_, hL⟩
    have h := d.centralProjection_le_join.trans (sup_le (swap hL) (swap hA))
    intro c hc
    exact (h hc x rfl).symm
  · rintro ⟨hC, hL⟩
    refine ⟨?_, hL⟩
    have h := d.offender_le.trans (sup_le (swap hL) (swap hC))
    intro a ha
    exact (h ha x rfl).symm

/-- Once A lies in two commuting factors, its centralizer projection lies
in the second factor. The containment premise is discharged by residual placement. -/
theorem centralProjection_le_second {M : Subgroup G}
    (hz : center L = ⊥) (hM : M ≤ centralizer (L : Set G)) (hA : A ≤ L ⊔ M) :
    d.centralProjection ≤ M := by
  intro c hc
  have hcLM : c ∈ L ⊔ M :=
    d.centralProjection_le_join.trans (sup_le le_sup_left hA) hc
  have hp : c ∈ (L : Set G) * (M : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L M
      (hM.trans (Subgroup.centralizer_le_normalizer _))]
    exact hcLM
  obtain ⟨l, hl, m, hm, he⟩ := hp
  have hlC : l ∈ centralizer (L : Set G) := by
    have h := (centralizer (L : Set G)).mul_mem (d.centralProjection_le hc)
      ((centralizer (L : Set G)).inv_mem (hM hm))
    change l * m = c at he
    rwa [← he, mul_inv_cancel_right] at h
  have hl1 : l = 1 := disjoint_iff_inf_le.mp
    (disjoint_centralizer_of_center_eq_bot L hz) ⟨hl, hlC⟩
  change l * m = c at he
  rw [hl1, one_mul] at he
  exact he ▸ hm

end InnerProjections

variable [Finite G]

private theorem seed_eq_moved_of_offender_le {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L) (hAL : A ≤ L) :
    seed.space.toSubmodule = moved ρ L := by
  let : IsQuasisimple L := hL.2
  have hcore : pCore 2 L = ⊥ := le_bot_iff.mp
    ((IsQuasisimple.pCore_le_center 2).trans (seed_center_eq_bot ρ seed).le)
  have hlocal : localTwoCore L A = ⊥ := by
    unfold localTwoCore
    rw [sup_eq_left.mpr hAL, hcore, Subgroup.map_bot]
  rw [seed.space_eq]
  unfold naturalSeedSpace
  rw [hlocal, fixedSpace_bot]


theorem centralProjection_ne_bot {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hproper : seed.space.toSubmodule < moved ρ L) (d : InnerProjections A L) :
    d.centralProjection ≠ ⊥ := by
  intro hz
  have hAL := d.offender_le
  rw [hz, sup_bot_eq] at hAL
  exact hproper.ne (seed_eq_moved_of_offender_le ρ seed hL hAL)

private theorem component_centralizes_fitting {L : Subgroup G} (hL : IsComponent G L) :
    L ≤ centralizer (fittingSubgroup G : Set G) := by
  rcases hL.normal_dichotomy (fittingSubgroup G) with h | h
  · let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    have hs : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable L hs).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp h

private theorem exists_distinct_moved_of_projection {A L : Subgroup G}
    (hcore : pCore 2 G = ⊥) (hA : IsPGroup 2 A)
    (hfit : A ≤ centralizer (fittingSubgroup G : Set G)) (hL : IsComponent G L)
    (d : InnerProjections A L) (hne : d.centralProjection ≠ ⊥) :
    ∃ M, IsComponent G M ∧ L ≠ M ∧ ⁅M, A⁆ ≠ ⊥ := by
  by_contra! hn
  have hf : d.centralProjection ≤ centralizer (fittingSubgroup G : Set G) :=
    d.centralProjection_le_join.trans (sup_le (component_centralizes_fitting hL) hfit)
  have he : componentLayer G ≤ centralizer (d.centralProjection : Set G) := by
    apply sSup_le
    intro M hM
    by_cases hLM : L = M
    · subst M
      exact le_centralizer_iff.mp d.centralProjection_le
    · have hLC : L ≤ centralizer (M : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hLM)
      have hAC : A ≤ centralizer (M : Set G) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hn M hM hLM))
      exact le_centralizer_iff.mp (d.centralProjection_le_join.trans (sup_le hLC hAC))
  have hF : d.centralProjection ≤ centralizer (generalizedFitting G : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hf) he)
  exact hne ((ChapterB.QuasisimpleSections.disjoint_centralizer_fitting hcore
    d.centralProjection (d.centralProjection_isPGroup hA)).eq_bot_of_le hF)

/-- A proper natural seed forces another actual component moved by A. -/
theorem exists_distinct_moved_component {K : GroupClass} {A L : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L)
    (seed : NaturalSeed ρ A L) (hproper : seed.space.toSubmodule < moved ρ L) :
    ∃ M, IsComponent G M ∧ L ≠ M ∧ ⁅M, A⁆ = M ∧ ¬ A ≤ M := by
  let d := innerProjections ρ seed
  let : IsElementaryAbelian 2 A := setup.minimal.1.1.2
  obtain ⟨M, hM, hLM, hMA⟩ := exists_distinct_moved_of_projection setup.hypothesis.twoCore
    (IsElementaryAbelian.isPGroup 2 A) setup.centralizes_fitting hL d
    (centralProjection_ne_bot ρ seed hL hproper d)
  let : M.Normal := setup.component_normal M hM
  have hMeq : ⁅M, A⁆ = M := by
    rcases hM.commutator_dichotomy A with hz | he
    · exact (hMA hz).elim
    · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq,
        iSup_const] using he
  refine ⟨M, hM, hLM, hMeq, ?_⟩
  intro hAM
  have hc : ⁅L, A⁆ ≤ ⊥ := (commutator_mono le_rfl hAM).trans
    (hL.commutator_eq_bot_of_ne hM hLM).le
  have hLbot : L = ⊥ := le_bot_iff.mp (hLA ▸ hc)
  have hu : moved ρ L = ⊥ := by
    rw [hLbot]
    apply (subspaceCommutator_eq_bot_iff ρ ⊤ ⊥).mpr
    rw [fixedSpace_bot]
  rw [hu] at hproper
  exact (not_lt_bot hproper)




end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
