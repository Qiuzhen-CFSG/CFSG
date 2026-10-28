module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.VertexResidues
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalThompson

/-!
# Constructing the original normalizer supplement and generating pair

The full normalizer acts on the marked five-dimensional core by six-letter
permutations. Since alternating and symmetric permutations have the same
orbits on binary words, every normalizer element agrees on z with an element
of L. Lifting that element proves M=L C_M(z), without assuming this supplement.

The original local product then gives M=LT. Its centralizer of z and the
original plane normalizer are distinct proper overgroups of T: equality
would put z in C_V(L₂)=C_V(L), contrary to escape. The six-letter subgroup
lattice proves they generate M. Thus both geometric premises previously
retained by the marked-chamber assembly are constructed on the original
subgroups and inclusion maps.

OriginalGeneratedAmalgam applies these results to ambient recognition and
the four marked involution classes. The earlier source hypotheses, including
the genuine universal Structural1222, remain explicit.
Source: Aschbacher–Smith 13.4.9, printed p.906; Notation 13.2.1, p.877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3 Quasithin.I5
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The six-letter action of the full normalizer has the same orbits on V
as L. Lifting the matching even permutation gives the centralizer supplement. -/
theorem normalizer_component_centralizer_supplement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : V) :
    normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) := by
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,_,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  apply le_antisymm ?_ (sup_le L.le_normalizer inf_le_right)
  intro x hx
  let a : normalizer (L : Set G) := ⟨x,hx⟩
  let w := (m.coordinate z).toAdd
  obtain ⟨b,hb⟩ := BinaryPermutation.exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 6)) w.val
    (BinaryPermutation.representation (Fin 6) (q a) w.val)
    (BinaryPermutation.wordWeight_permute (q a) w.val).symm
  obtain ⟨v,hv⟩ := m.quotient.surjective b
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) v
  have he : l.val * z.val * l.val⁻¹ = x * z.val * x⁻¹ := by
    have he := m.equivariant l z
    rw [hv] at he
    have hqz := hq a z
    have hb' : BinaryPermutation.coreRepresentation (Fin 6) b.val w =
        BinaryPermutation.coreRepresentation (Fin 6) (q a) w := Subtype.ext hb
    have hh := he.trans (hb'.trans hqz.symm)
    exact congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective hh))
  have hc : l.val⁻¹ * x ∈ centralizer ({z.val} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun y : G => l.val⁻¹ * y * x) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh.symm
  have hm : l.val⁻¹ * x ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).inv_mem (L.le_normalizer l.property)) hx
  have hh := (L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G))).mul_mem
    (mem_sup_left l.property) (mem_sup_right ⟨hc,hm⟩)
  simpa only [mul_inv_cancel_left] using hh


/-- The two original inside parabolics generate LT. Distinctness follows
from the plane residual's fixed line and the chosen escaping vector. -/
theorem original_inside_parabolics_generate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) =
          L ⊔ (T : Subgroup G) := by
  have hM := normalizer_eq_component_sylow_of_centralizer_intersection
    (normalizer_component_centralizer_supplement h structural D m z) hinter
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  obtain ⟨⟨eB⟩,_,_,_⟩ := original_second_flag_chief_factors D m eL W hW hT
  have hB : IsCoatom (B.subgroupOf (normalizer (L : Set G))) := by
    rw [hM]
    exact original_second_flag_coatom D m W hW hT
  let M := normalizer (L : Set G)
  let A := centralizer ({z.val} : Set G) ⊓ M
  let Ai := (centralizer ({z.val} : Set G)).subgroupOf M
  let Bi := B.subgroupOf M
  let S := T.subtype D.sylow_normalizes_component
  have hTA : (T : Subgroup G) ≤ A :=
    le_inf (original_sylow_le_centralizer hz) D.sylow_normalizes_component
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eA⟩ := normalizer_centralizer_quotient D m hcore z hzL hinter
  let a : Ai ≃* A :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_right _ _).symm).trans
      (subgroupOfEquivOfLe (show A ≤ M from inf_le_right))
  have ha : ¬ IsPGroup 2 Ai := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eA (hp.of_equiv a)
  let b := subgroupOfEquivOfLe hBM
  have hb : ¬ IsPGroup 2 Bi := fun hp =>
    not_twoGroup_of_symmetricThree_quotient eB (hp.of_equiv b)
  have hSA : (S : Subgroup M) ≤ Ai := fun _ hx => (hTA hx).1
  have hSB : (S : Subgroup M) ≤ Bi := fun _ hx => hTB hx
  have hAp : Ai ≠ ⊤ := by
    intro he
    apply hzL
    intro l hl
    exact mem_centralizer_singleton_iff.mp
      (show (⟨l,L.le_normalizer hl⟩ : M) ∈ Ai from he ▸ mem_top _)
  have hne : Ai ≠ Bi := by
    intro he
    have hBC : B ≤ centralizer ({z.val} : Set G) := by
      intro b hb
      exact (show (⟨b,hBM hb⟩ : M) ∈ Ai from he ▸ hb)
    have hzK : z.val ∈ V ⊓ centralizer (((pResidual 2 B).map B.subtype : Subgroup G) : Set G) := by
      refine ⟨z.property,?_⟩
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hBC ((map_subtype_le _) hk))
    rw [original_second_flag_fixed D m W hW hT] at hzK
    exact hzL hzK.2
  have hp := Quasithin.I5.RankTwoParabolics.of_six_letter_two_quotient (pCore 2 M) pCore_isPGroup
    (normalizer_quotient_of_ordinary h structural D m eL hM) S Ai Bi
    (lt_iff_le_not_ge.mpr ⟨hSA,fun hh => ha (S.isPGroup'.to_le hh)⟩)
    (lt_iff_le_not_ge.mpr ⟨hSB,fun hh => hb (S.isPGroup'.to_le hh)⟩)
    hAp hB.ne_top hne
  have hg := congrArg (map M.subtype) hp.generate
  rw [Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM,
    ←MonoidHom.range_eq_map,range_subtype] at hg
  rw [hinter] at hg
  exact ⟨hM,hg.trans hM⟩

/-- Apply the generation argument to the literal R₁ product, supplying its
ordinary quotient and intersection from the already proved solvable branch. -/
theorem original_R1_inside_generation
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) =
          L ⊔ (T : Subgroup G) := by
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  obtain ⟨⟨eL⟩,_,_,_,_,hinter,_,_,_⟩ := centralizer_pair_quotient_of_original_R1
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  exact original_inside_parabolics_generate h structural D m eL z hz hzL hinter W hW hT

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
