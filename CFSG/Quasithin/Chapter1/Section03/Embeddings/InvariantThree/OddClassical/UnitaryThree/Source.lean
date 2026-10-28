module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.PSU3.PrimeOddCenterCover

/-!
# Original odd unitary branch of the intrinsic three-complement sieve

The actual Sylow pair has trivial two-core, so its center has odd order.
The proved odd-center scalar-cover theorem therefore identifies its group
as SU₃ or PSU₃. This is exactly the cover information needed by the existing
monomial calculation; no universal theorem about covers with even center is
required. The original intrinsic irreducibility then excludes the unitary
central quotient for every odd prime fixed-field order.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511, and I.1.3(2),
printed p.407. The matrix field has order p² and conjugation x ↦ xᵖ.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The original trivial two-core supplies the odd-center cover hypothesis. -/
theorem model_of_pair
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    ModTwoExtraspecial.Model p Q := by
  let : IsQuasisimple Q := h.quasisimple
  obtain ⟨E, _, _, J, hE, hc, ⟨e⟩⟩ := hm
  by_cases hz : center Q = ⊥
  · exact Or.inr ⟨E, inferInstance, inferInstance, J, hE, hc,
      ⟨SporadicRemaining.equiv_of_center_eq_bot e hz⟩⟩
  · have hodd : Odd (Nat.card (center Q)) :=
      Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using SporadicRemaining.two_not_dvd_center_card h.twoCore)
    have hp2 : p ≠ 2 := by intro he; subst p; norm_num at ho
    obtain ⟨_, _, _, j, _⟩ :=
      HermitianForm.PrimeOddCenterCover.nontrivial_center_recognition J hp hp2 hE hc e hodd hz
    exact Or.inl ⟨E, inferInstance, inferInstance, J, hE, hc, ⟨j.symm⟩⟩

/-- All odd-prime unitary Sylow pairs are reducible, with the cover input discharged. -/
theorem reducible_of_source
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  obtain ⟨hlarge, hmod⟩ := nonreducible_psu_three_parameters h p hp ho hm hn
  rcases h.oddComplement with ⟨_, hcard⟩ | ⟨_, hcard, _⟩
  · exact hn (reducible_of_psu_three_mod_two_elementary h (by simpa using hcard)
      p hp ho hlarge hmod hm)
  · exact hn (ModTwoExtraspecial.reducible_of_model p hp ho hlarge hmod
      h (by simpa using hcard) (model_of_pair h hp ho hm))

/-- The literal intrinsic input excludes every odd-prime unitary central quotient. -/
theorem not_model_of_local_input
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSU (XiQuotient L ⧸ center (XiQuotient L)) 3 p := by
  intro hm
  have hTL : T ≤ normalizer L :=
    (le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  exact not_pairReducible h hPL hTL
    (by simpa only [hS] using reducible_of_source hi p hp ho hm)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree
