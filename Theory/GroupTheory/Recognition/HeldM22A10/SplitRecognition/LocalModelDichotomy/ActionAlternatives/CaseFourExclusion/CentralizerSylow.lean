module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.CentralizerSylow.Action
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.Fusion
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The Case IV Sylow centralizer from finite automizer rigidity

The finite stabilizer hypothesis forces the faithful image of N_G(F) on F
to equal the image of T, hence N_G(F) = T. Inside C_G(d), F is therefore
self-normalizing, because C_T(d) = F. The normalizer condition for finite
two-groups makes F Sylow, so every Sylow two-subgroup of C_G(d) has order 16.

The last theorem applies this conclusion to the actual Thompson-transfer
contradiction in `Fusion`. Finite automizer rigidity remains an explicit
hypothesis; no ambient simplicity is needed until this final application.

Source: Janko, A characterization of the Mathieu simple groups, I,
J. Algebra 9 (1968), Section 1, printed p.3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .four)

variable (hfinite : ∀ X : Subgroup (MulAut BinaryFour), localAutomizer ≤ X →
  (∀ f : MulAut BinaryFour, f ∈ X → f automizerPoint = automizerPoint → f ∈ localAutomizer) →
    X = localAutomizer)

include D K hK R hfinite

/-- Finite stabilizer rigidity determines the whole ambient normalizer. -/
public theorem normalizer_Fg_eq_of_rigidity :
    normalizer (Fg D K hK R : Set G) = T D K hK R := by
  have hX := hfinite (normalizerAction D K hK R).range
    (localAutomizer_le_normalizerAction_range D K hK R)
    (normalizerAction_stabilizer D K hK R)
  apply le_antisymm _ (T_le_normalizer_Fg D K hK R)
  intro n hn
  apply (normalizerAction_mem_local_iff D K hK R ⟨n, hn⟩).mp
  rw [← hX]
  exact ⟨⟨n, hn⟩, rfl⟩

/-- The precise Sylow-centralizer order consumed by the Case IV fusion argument. -/
public theorem sylowCentralizer_card_of_rigidity :
    ∀ P : Sylow 2 (centralizer ({into D K hK R d} : Set G)), Nat.card P = 16 := by
  let C := centralizer ({into D K hK R d} : Set G)
  have hFC : Fg D K hK R ≤ C := by
    rw [← T_inter_centralizer_d D K hK R]
    exact inf_le_right
  have hp : IsPGroup 2 (Fg D K hK R) := IsPGroup.of_card (n := 4) (Fg_card D K hK R)
  have hn : normalizer ((Fg D K hK R).subgroupOf C : Set C) =
      (Fg D K hK R).subgroupOf C := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hFC, normalizer_Fg_eq_of_rigidity D K hK R hfinite]
    intro x hx
    exact (T_inter_centralizer_d D K hK R).le ⟨hx, x.property⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq
    ((Fg D K hK R).subgroupOf C) hp.comap_subtype hn
  have hcard : Nat.card S = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv).trans (Fg_card D K hK R))
  intro P
  exact (Nat.card_congr (P.equiv S).toEquiv).trans hcard

/-- The finite rigidity premise discharges the remaining premise of `Fusion`. -/
public theorem false_of_automizer_rigidity [IsSimpleGroup G] : False :=
  false_of_sylowCentralizer_card D K hK R
    (sylowCentralizer_card_of_rigidity D K hK R hfinite)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
