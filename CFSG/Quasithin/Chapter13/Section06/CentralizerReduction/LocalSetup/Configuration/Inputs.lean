module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Geometry
public import CFSG.Quasithin.Chapter3.Defs

/-!
# Inputs and marked flags for the A₅ local configuration

`FlagSource` retains an unaligned actual module, the extension of its action
to N_G(V), and a T-invariant flag of orders two and four. It does not assert
any coordinate alignment or local Sylow centralizer conclusion. Its maps
are the module and normalizer actions in Notation 13.2.1 and the paragraph
preceding it. `FlagMarking` describes the alignment to be constructed.

`EarlierLocal` records precisely the specializations of earlier statements
used in the local reductions. The second maximal two-local over T is the
nonuniqueness conclusion of earlier Corollary 3.3.2(2) in the Fundamental Setup. The 13.5.10 specialization is at G₁ = C_G(z),
which is a member of the source family H_z. The section assembly owner must
supply these from the earlier source theorems; this module does not prove
those earlier theorems or claim the existence of a marked flag.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 12.2.5,
12.2.6, Notation 13.2.1, 13.2.3–6, 13.3.2/5, 13.5.10/12 and Corollary 3.3.2(2).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup Stellmacher ChapterB
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G]
namespace A5Module

/-- Earlier genuine module data with no chosen coordinate flag. -/
structure FlagSource (T : Sylow 2 G) (L V V₁ V₂ : Subgroup G) where
  module : Marking L V
  action_kernel : module.action.ker = pCore 2 L
  normalizerAction : normalizer (V : Set G) →* Equiv.Perm (Fin 5)
  normalizer_equivariant : ∀ (n : normalizer (V : Set G)) (x : Space),
    MulAut.conj (n : G) (module.map (Multiplicative.ofAdd x)) =
      module.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (normalizerAction n) x))
  action_agrees : ∀ (l : L) (hl : (l : G) ∈ normalizer (V : Set G)),
    normalizerAction ⟨l, hl⟩ = (module.action l).val
  T_normalizes : (T : Subgroup G) ≤ normalizer (V : Set G)
  V_le_T : V ≤ (T : Subgroup G)
  one_le_two : V₁ ≤ V₂
  two_le_V : V₂ ≤ V
  one_card : Nat.card V₁ = 2
  two_card : Nat.card V₂ = 4
  one_invariant : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  two_invariant : (T : Subgroup G) ≤ normalizer (V₂ : Set G)

/-- The output of the alignment construction, retaining its actual action
and two-core kernel. This record alone is not an existence theorem. -/
structure FlagMarking (T : Sylow 2 G) (L V V₁ V₂ : Subgroup G) where
  module : Marking L V
  action_kernel : module.action.ker = pCore 2 L
  line_eq : zpowers (markedZ module) = V₁
  vector_mem : markedV module ∈ V₂
  vector_not_mem : markedV module ∉ V₁
  z_central : markedZ module ∈ omegaOneCenterAmbient (T : Subgroup G)

end A5Module

/-- The earlier-source specializations consumed by the local construction.
No 13.6.2–6 conclusion is a field. -/
structure EarlierLocal (T : Sylow 2 G) (L M V V₂ V₃ : Subgroup G) (z : G) : Prop where
  maximal_overgroups : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M}
  other_local : ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ (T : Subgroup G) ≤ N ∧ N ≠ M
  T_normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  outside_centralizes : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  span_equivalence : IsMulCommutative (conjugateSpanBy V₃ (Gv z)) ↔
    IsMulCommutative (conjugateSpanBy V (Gv z))
  nonabelian_classification : ¬ IsMulCommutative (conjugateSpanBy V₃ (Gv z)) →
    ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3
  baumann_alternatives : baumann (T : Subgroup G) ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∨
    V ⊓ centralizer (baumann (T : Subgroup G) : Set G) = V₂
  baumann_normalizer : normalizer (baumann (T : Subgroup G) : Set G) ≤ M
  trivial_intersections : ∀ g ∈ M,
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V
  module_normalizer : normalizer (V : Set G) ≤ M

/-- The literal map from C_T(v) to C_G(v)/⟨v⟩. -/
def checkedSylowMap (T : Subgroup G) (v : G) : Tv T v →* Gcheck v :=
  (QuotientGroup.mk' (vLine v)).comp (inclusion inf_le_right)

/-- The checked Sylow map kills precisely the preimage of the specified v-line. -/
theorem checkedSylowMap_kernel (T : Subgroup G) (v : G) :
    (checkedSylowMap T v).ker = (vLine v).comap (inclusion inf_le_right) := by
  ext x
  change QuotientGroup.mk' (vLine v) (inclusion inf_le_right x) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

/-- The literal quotient image of any Sylow witness with ambient image C_T(v). -/
theorem checkedSylowMap_range (T : Subgroup G) (v : G) (P : Sylow 2 (Gv v))
    (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v) :
    (P : Subgroup (Gv v)).map (QuotientGroup.mk' (vLine v)) =
      (checkedSylowMap T v).range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyG : (y : G) ∈ Tv T v := hP ▸ (show (y : G) ∈
      (P : Subgroup (Gv v)).map (Gv v).subtype from ⟨y, hy, rfl⟩)
    exact ⟨⟨y, hyG⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : G) ∈ (P : Subgroup (Gv v)).map (Gv v).subtype := hP.symm ▸ y.property
    obtain ⟨z, hz, he⟩ := hy
    exact ⟨z, hz, congrArg (QuotientGroup.mk' (vLine v)) (Subtype.ext he)⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
