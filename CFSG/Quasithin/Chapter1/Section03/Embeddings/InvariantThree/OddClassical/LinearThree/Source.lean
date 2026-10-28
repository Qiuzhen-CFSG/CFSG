module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition

/-!
# Original odd linear branch of the intrinsic three-complement sieve

The proved scalar-cover theorem identifies every perfect central cover of
PSL₃ over a nonexceptional finite field. At field order three its scalar
center is trivial; at a larger split prime the covering group is SL₃ or
PSL₃. These two universal consequences discharge the earlier cover inputs
in the existing Sylow-pair calculation. The final source theorem retains
only the original pair and its actual odd-prime projective quotient model.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511, and I.1.3,
printed p.407. The unitary and other model branches remain separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
universe u

/-- The scalar center at field order three discharges the complete I.1.3 input. -/
theorem source_trivialThreeCover : TrivialThreeCover.{u} := by
  intro K _ _ hK hmodel
  let : IsQuasisimple K := hK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
    (F := F) (by omega) (by omega) e
  rw [hF] at hd
  have hc : Nat.card (center K) = 1 := Nat.dvd_one.mp (by norm_num at hd ⊢; exact hd)
  exact (center K).eq_bot_of_card_eq hc

/-- Every cover at a split odd prime has one of the two actual linear models. -/
theorem source_splitPrimeCover : Split.SplitPrimeCover.{u} := by
  intro p hp _ hlarge _ K _ _ hK hmodel
  let : IsQuasisimple K := hK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  by_cases hz : center K = ⊥
  · refine Or.inr ⟨F, inferInstance, inferInstance, hF, ?_⟩
    exact ⟨QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)⟩
  · have h2 : Nat.card F ≠ 2 := by omega
    have h4 : Nat.card F ≠ 4 := by
      rw [hF]
      intro he
      rw [he] at hp
      norm_num at hp
    obtain ⟨_, _, _, j, _⟩ :=
      Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 e hz
    exact Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨j.symm⟩⟩

/-- The original linear Sylow-pair alternative, with both cover premises proved. -/
theorem alternative_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) :=
  alternative source_trivialThreeCover source_splitPrimeCover h hp ho hm

/-- On the original intrinsic input, irreducibility eliminates the reducible
pair and yields the literal plane and invariant linear alternative of 1.3.4. -/
theorem of_local_input
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient L ⧸ center (XiQuotient L)) 3 p) :
    Alternatives 3 T P L := by
  have hTL : T ≤ normalizer L :=
    (le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  rcases alternative_of_source hi hp ho hm with hr | he
  · exact (not_pairReducible h hPL hTL (by simpa only [hS] using hr)).elim
  · exact ⟨plane_of_quotient_plane h hPL he.1, Or.inr ⟨hTL, Or.inl he.2⟩⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
