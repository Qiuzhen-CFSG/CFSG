module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Centralizing
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable

/-!
# Transvection recognition in the actual section U_H/V₁

`lemma_13_8_5` assembles all three source clauses under the standing §13.8
counterexample setup and universal earlier-theorem inputs. The acting group
is the literal H/O₂(H), and the module is the actual U_H/V₁ with its
conjugation action. Its normality and elementary abelianness follow from
the standing setup.

The normal closure of the supplied transvection cannot be solvable: B.1.8
gives one or two actual S₃ factors, the marked local geometry excludes two
factors, and the one-factor residual alternatives either force H≤M or fix
the generating seed. Nonsolvability then supplies a moved relative
C-component. G.6.4 recognizes its actual commutator section, and 13.7.6
and the proved module-extension results give H=KT and the full alternatives.

The conclusion retains actual S₆/S₇/L₄(2) equivalences with equivariant
natural or five-dimensional augmentation modules, the corresponding A₆
or concrete triple-cover quotient of L, and the two noncentral L₁-chief
factors in the S₆ case. Only the universal earlier results are explicit
inputs; no solvability, component, factor, residual or module-recognition
conclusion for the selected transvection is assumed.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, Lemma 13.8.5, printed pp.947–948.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open Component.RecognitionStep Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Aschbacher–Smith 13.8.5, conditional only on the standing source setup,
the actual conjugation action with a transvection, and universal earlier
results. `FullAlternatives` states clauses (2) and (3) together, preserving
the same actor equivalence in each module identification. The first clause
uses a C-component intrinsic to H, with its ambient image in the product.

The B.1.8 input is universal in both the finite solvable actor and its
finite binary module. The other earlier inputs are the exact G.6.4,
13.7.6 and marked local results specified in their source interfaces.
Every hypothesis needed to apply them to the selected H and transvection
is discharged by the two branch proofs. -/
theorem lemma_13_8_5
    (T : Sylow 2 G) {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hB18 : ∀ (B E : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
      (σ : Representation (ZMod 2) B E),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ →
        Nonempty (ChapterB.SolvableFFFactors σ))
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      (∃ t : Source.Hstar H, IsTransvection ρ t) →
      (∃ K : Subgroup H, K.IsCComponent ∧
        (H : Set G) = (K.map H.subtype : Set G) * (T : Set G)) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁
        (le_sup_left.trans hH.1.2) ρ := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  rintro ρ hρ ⟨t, ht⟩
  have hns := Solvable.source_normalClosure_not_solvable T d localEarlier
    (fun B _ _ _ σ => hB18 B (Additive (Source.Utilde H V₃ V₁)) σ)
    hH ρ hρ t ht
  exact Component.complete_conclusions_of_nonsolvable_closure T d earlier hG64 hH
    ρ hρ t ht hns

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

end
