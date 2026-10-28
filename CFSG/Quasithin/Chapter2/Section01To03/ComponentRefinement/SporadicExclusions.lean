module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M12
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HallJanko
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis

/-!
# Sporadic branch of component refinement

Source: Aschbacher–Smith, 2.3.9(7), printed p.526.

The concrete local calculations exclude M₁₂, M₂₄, J₂, J₄, HS, He and Ru.
For each specified quotient L/O₂(L), they construct overgroups of the actual
Sylow subgroup inside L ∨ S, with nontrivial self-centralizing two-cores and
no escaping allowed blocks. Together with C_G(z), these overgroups generate L.
The block input therefore puts L inside M, contradicting the local setup.

The final application to the sporadic alternative of 1.1.5(3)(f) retains an
actual isomorphism L/O₂(L) ≃ M₁₁, M₂₂ or M₂₃. The central two-kernel and
the literal inner action are retained throughout. Recognition and the
intersection calculations for these surviving models remain separate parts
of 2.3.9(7).
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup ClassificationModels

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {name : SporadicName}

/-- The seven concrete calculations supply the local cover for the actual
quotient and action, with all geometry and block premises discharged. -/
theorem LocalSetup.nonempty_sporadic_centralizerBlockCover
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z name)
    (hn : IsDiscardedSporadic name) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  cases name with
  | m11 | m22 | m23 | j3 => exact hn.elim
  | m12 => exact M12Exclusion.nonempty_centralizerBlockCover h d
  | m24 => exact M24Exclusion.nonempty_centralizerBlockCover h d
  | j2 => exact HallJanko.nonempty_centralizerBlockCover h d
  | j4 => exact JankoFour.nonempty_centralizerBlockCover h d
  | hs => exact HigmanSims.nonempty_centralizerBlockCover h d
  | he => exact HeldCase.nonempty_centralizerBlockCover h d
  | ru => exact RudvalisCase.nonempty_centralizerBlockCover h d

/-- The sporadic exclusion calculation on p.526: an actual component
quotient cannot be any of the seven discarded sporadic models. -/
theorem LocalSetup.false_of_discarded_sporadic
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z name)
    (hn : IsDiscardedSporadic name) : False := by
  obtain ⟨c⟩ := h.nonempty_sporadic_centralizerBlockCover d hn
  exact h.false_of_centralizerBlockCover c

/-- Restrict the source's sporadic list. J₃ is absent from 1.1.5(3)(f);
its exclusion is an earlier-source input, not an eighth block calculation. -/
theorem LocalSetup.sporadic_name_cases
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z name)
    (hn : name ≠ .j3) : name = .m11 ∨ name = .m22 ∨ name = .m23 := by
  cases name with
  | m11 => exact Or.inl rfl
  | m22 => exact Or.inr (Or.inl rfl)
  | m23 => exact Or.inr (Or.inr rfl)
  | j3 => exact (hn rfl).elim
  | m12 | m24 | j2 | j4 | hs | he | ru =>
    exact (h.false_of_discarded_sporadic d trivial).elim

/-- The surviving alternatives retain the original quotient isomorphism;
no assertion that the central two-kernel is trivial is used. -/
theorem LocalSetup.sporadic_quotient_cases
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z name)
    (hn : name ≠ .j3) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23) := by
  rcases h.sporadic_name_cases d hn with rfl | rfl | rfl
  · exact Or.inl ⟨d.quotientIso⟩
  · exact Or.inr (Or.inl ⟨d.quotientIso⟩)
  · exact Or.inr (Or.inr ⟨d.quotientIso⟩)

/-- Apply the exclusion to the literal sporadic model/action data of
1.1.5(3)(f). The order-two and Sylow-fixation clauses already follow from
`LocalSetup` for this action, so only its innerness is needed here. -/
theorem LocalSetup.sporadic_quotient_cases_of_inner_action
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hi : α ∈ (MulAut.conj (G := L)).range)
    (hm : ∃ name : SporadicName, name ≠ .j3 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M23) := by
  obtain ⟨name, hn, ⟨e⟩⟩ := hm
  exact h.sporadic_quotient_cases ⟨e, α, hα, hi⟩ hn

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
