module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterA.Section04.Defs
public import CFSG.Quasithin.ClassificationModels.RankTwo
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The source hypotheses for Section 12.2

Hypotheses 12.2.1 and 12.2.3 use maximality in the canonical local family,
faithful membership, and the literal quotient by the two-core. The exclusions
in 12.2.3 use the complete rank-two catalogue, including Ree, at exponent
greater than one. They do not exclude all groups over larger binary fields.

The chosen member of Irr⁺ is specified separately, using conjugation on the
actual R₂(LT), its fixed-space quotient, and the homogeneous selection of
A.1.40. Elementarity, containment and L-normalization of its ambient image
are proved below. T-invariance and reducedness of the chosen member are
outputs of 12.2.2, not fields of the hypothesis.

The universal structural implication of 12.2.2 and the full alternatives of
12.2.13 are propositions to be proved by their source owners. In particular
they contain no Section 12.8 flag, full action or escape assumption.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypotheses 12.2.1, 12.2.3 and Theorems 12.2.2, 12.2.13, pp.794–799.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous

namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine L_f^*: maximal in L(G,T), and a member of X_f. -/
def FaithfulMaximalLocal (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  L ∈ Chapter1.LStar G (T : Subgroup G) ∧ ChapterA.Section04.IsFaithfulSignalizerType L

/-- Hypothesis 12.2.1. The final source application takes the full known-simple
class as K; no restricted carrier catalogue is built into this definition. -/
structure Hypothesis1221 (K : GroupClass.{u}) (T : Sylow 2 G) (L : Subgroup G) : Prop where
  simpleQTKE : IsSimpleQTKE K G
  maximal_faithful : FaithfulMaximalLocal T L
  quasisimple : IsQuasisimple (L ⧸ pCore 2 L)

/-- Exactly Hypothesis 12.2.3, before choosing V. -/
structure Hypothesis1223 (K : GroupClass.{u}) (T : Sylow 2 G) (L : Subgroup G) : Prop
    extends Hypothesis1221 K T L where
  no_rankTwo : ∀ f : ℕ, 1 < f → ¬ ClassificationModels.IsRankTwoModel G f
  no_M22 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M22)
  no_M23 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M23)
  no_J4 : ¬ Nonempty (G ≃* Janko4.Model)

/-- R₂(H), as the actual normal subgroup of H. -/
abbrev ReducedModule (H : Subgroup G) := reducedTwoSubgroup H

instance reducedModule_elementary (H : Subgroup G) :
    IsElementaryAbelian 2 (ReducedModule H) := isPReduced_reducedPSubgroup.elementary

/-- The literal conjugation action of H on R₂(H). -/
def reducedConjugation (H : Subgroup G) : H →* MulAut (ReducedModule H) :=
  (ReducedModule H).normalizerMonoidHom.comp
    ((MonoidHom.id H).codRestrict _ fun h => by
      rw [Subgroup.normalizer_eq_top]
      exact mem_top h)

noncomputable def reducedRepresentation (H : Subgroup G) :
    Representation (ZMod 2) H (Additive (ReducedModule H)) :=
  Representation.elementaryRepresentation (reducedConjugation H)

/-- A subspace of R₂(H), included into the original ambient group. -/
def subspaceImage (H : Subgroup G)
    (I : Submodule (ZMod 2) (Additive (ReducedModule H))) : Subgroup G :=
  (I.toAddSubgroup.toSubgroup'.map (ReducedModule H).subtype).map H.subtype

/-- The original choice V ∈ Irr⁺(L,R₂(LT),T), before applying 12.2.2. -/
structure ChosenModule (T : Sylow 2 G) (L V : Subgroup G) where
  space : Submodule (ZMod 2) (Additive (ReducedModule (L ⊔ (T : Subgroup G))))
  irrPlus : IsIrrPlusWith (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))
    ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) space
  image_eq : subspaceImage (L ⊔ (T : Subgroup G)) space = V

namespace ChosenModule
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

omit [Finite G] in
theorem le_reduced :
    V ≤ (ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype := by
  rw [← D.image_eq]
  exact map_mono (map_subtype_le _)

omit [Finite G] in
theorem elementary : IsElementaryAbelian 2 V := by
  let : IsElementaryAbelian 2
      ((ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype) :=
    IsElementaryAbelian.map _
  exact IsElementaryAbelian.of_le D.le_reduced

omit [Finite G] in
theorem le_core : V ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  D.le_reduced.trans (map_mono (reducedPSubgroup_le_pCore 2 _))

omit [Finite G] in
theorem le_sylow : V ≤ (T : Subgroup G) := by
  apply D.le_core.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
theorem core_centralizes : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    centralizer (V : Set G) := by
  apply le_centralizer_iff.mp
  apply D.le_reduced.trans
  exact (map_mono (reducedPSubgroup_le_centralizer_pCore 2 _)).trans
    (map_centralizer_le_centralizer_image _ _)

omit [Finite G] in
theorem ne_bot : V ≠ ⊥ := by
  intro he
  have hne : D.space ≠ ⊥ := Representation.BinaryOffender.IsIrrPlus.ne_bot
    (reducedRepresentation (L ⊔ (T : Subgroup G))) D.irrPlus.isIrrPlus
  apply hne
  apply bot_unique
  intro v hv
  have h : (v.toMul.val : G) ∈ V := D.image_eq ▸
    mem_map_of_mem _ (mem_map_of_mem _ hv)
  have hv1 : v.toMul = 1 := Subtype.ext (Subtype.ext (mem_bot.mp (he ▸ h)))
  exact congrArg Additive.ofMul hv1

omit [Finite G] in
theorem normalizes : L ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl v hv
  rw [← D.image_eq] at hv ⊢
  obtain ⟨w, ⟨a, ha, rfl⟩, rfl⟩ := hv
  let l' : (L ⊔ (T : Subgroup G) : Subgroup G) :=
    ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩
  have hh := (D.irrPlus.invariant (show l' ∈ L.subgroupOf _ from hl)
    (Additive.ofMul a)).mpr ha
  exact ⟨_, ⟨(reducedConjugation (L ⊔ (T : Subgroup G)) l') a, hh, rfl⟩, rfl⟩

end ChosenModule

/-- The structural prefix of 12.2.2(3), with its universal quantifiers.
The seven model alternatives remain the responsibility of the reduction owner. -/
def Structural1222 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L : Subgroup X),
    Hypothesis1223 K T L →
      (T : Subgroup X) ≤ normalizer (L : Set X) ∧
      Nonempty {V : Subgroup X // Nonempty (ChosenModule T L V)} ∧
      ∀ (V : Subgroup X), ChosenModule T L V →
        (T : Subgroup X) ≤ normalizer (V : Set X) ∧
        IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup X))) ∧
        (∀ g ∈ normalizer (L : Set X),
          V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          V.map (MulAut.conj g).toMonoidHom = V) ∧
        ((normalizer (L : Set X)) ≤ normalizer (V : Set X) ∨
          V ⊓ centralizer (L : Set X) = ⊥)

/-- All four alternatives of Theorem 12.2.13, with the original chosen V
and genuine block and global model identifications. -/
def Alternatives12213 (_T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  (∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G)) ∨
  (∃ d : ℕ, (d = 3 ∨ d = 4) ∧ ChapterC.IsLinearTwoBlock L d ∧
    ClassicalGroup.IsPSL G (d + 1) 2) ∨
  (ChapterC.IsLinearTwoBlock L 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
  (ChapterC.IsLinearTwoBlock L 4 ∧ Nonempty (G ≃* Sporadic.Mathieu.M24))

/-- The universal full earlier-source implication, not an escape certificate
for a particular Section 12.8 setup. -/
def Theorem12213 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 K T L → ChosenModule T L V → Alternatives12213 T L V

end CFSG.Quasithin.Chapter12.Section02
