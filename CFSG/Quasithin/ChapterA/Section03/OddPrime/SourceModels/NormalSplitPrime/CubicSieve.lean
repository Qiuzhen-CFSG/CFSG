module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CatalogueSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.EvenLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CubicLie
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Mathieu
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# The remaining actor cases after the cubic field and cover calculations

Apply the original catalogue reduction to the actual component. At three,
PSL₂ and Suzuki have insufficient rank; the small derived and Tits rows have
two-group outer automorphism groups. Fixed-subfield nine-groups exclude the
symplectic, G₂, triality and Ree rows. Binary PSL₃ gives the complete PGL₃
star-residual alternative. The unitary rank calculation leaves only odd
fixed-field degree. The A₆-preimage exponent argument excludes the Mathieu
triple cover, leaving genuine signed classical cubic covers.

The final theorem preserves the noncubic even-characteristic rows and the two
unresolved cubic actor families explicitly. It does not claim the universal
A.3.18 result. The ordinary-root leaf applies this same reduction to its
literal Cartan extension. Source: Aschbacher–Smith A.3.18, pp.51–53, and
4.3.6, printed p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Chapter1.Section02.LocalModels

/-- The remaining cubic characteristic-two row, with its actual projective
unitary marking and the fixed-field parameter, not the coefficient-field size. -/
def CubicUnitaryModel (S : Type*) [Group S] : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU S 3 (2 ^ n)

variable {H : Type*} [Group H] [Finite H]

theorem cubic_alternatives_or_unitary_of_even_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (hz : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))))
    (hm : EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)))
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives 3 K ∨ CubicUnitaryModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := by
  let B := K ⧸ pCore 2 K
  let S := B ⧸ center B
  let : IsSimpleGroup S := IsQuasisimple.simple
  have hrS : 1 < primeRank 3 S := by
    have he := primeRank_eq_of_surjective_of_coprime 3 (QuotientGroup.mk' (center B))
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])
    have ht := primeRank_quotient_eq_of_isTwoGroup 3 (by decide : Odd 3)
      (pCore 2 K) pCore_isPGroup
    change primeRank 3 B = primeRank 3 S at he
    change primeRank 3 B = primeRank 3 K at ht
    rw [← he, ht]
    exact hr
  have hout : ¬ IsPGroup 2 (MulAut.Outer S) := by
    intro hh
    apply outer_not_twoGroup hH hK Nat.prime_three (by decide) hr hz a ha haK
    exact hh.of_injective (MulAut.centralQuotientOuter (MulEquiv.refl _))
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl _))
  rcases hm with hm | hm
  · cases hm with
    | linear n hn hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hb := Matrix.SL2.binary_odd_primeRank_le_one (F := F) (by decide : Odd 3)
      have he := primeRank_congr 3 (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
      rw [← he] at hb
      exact (not_lt_of_ge hb hrS).elim
    | unitary n hn hm =>
      have ho : Odd n := by
        obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
        apply BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity.odd_of_rank_two
          J (by omega) hF hc
        rw [← primeRank_congr 3 e]
        exact hrS
      exact Or.inr ⟨n, by have hh := Nat.odd_iff.mp ho; omega, ho, hm⟩
    | suzuki m hm he =>
      obtain ⟨e⟩ := he
      have hb := PrimeRank.eq_zero_iff_not_dvd_card.mpr
        (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).2
      have he := primeRank_congr 3 e
      rw [← he] at hb
      have hzero : primeRank 3 S = 0 := hb
      omega
  · cases hm with
    | linear n hn hm => exact Or.inl (alternatives_of_even_linear_cubic_model
        hH hK hr hz (by omega) hm a ha haK hgen)
    | symplectic n hn hm => exact (not_cubic_field_model hH hK hr hz a ha haK
        (.symplectic n hn hm)).elim
    | g2 n hn hm => exact (not_cubic_field_model hH hK hr hz a ha haK
        (.g2 n hn hm)).elim
    | triality n hn hm => exact (not_cubic_field_model hH hK hr hz a ha haK
        (.triality n hn hm)).elim
    | ree m hm he => exact (not_cubic_field_model hH hK hr hz a ha haK
        (.ree m hm he)).elim
    | symplectic_derived he =>
      obtain ⟨e⟩ := he
      let d := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      exact (hout ((IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_equiv
        (MulAut.outerCongr d).symm)).elim
    | g2_derived he =>
      obtain ⟨e⟩ := he
      exact (hout (Theory.SpecificGroups.BinaryComponentResidual.g2_outer_two.of_equiv
        (MulAut.outerCongr e).symm)).elim
    | tits he =>
      obtain ⟨e⟩ := he
      exact (hout (Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv
        (MulAut.outerCongr e).symm)).elim

/-- The original cubic split domain now leaves only odd-degree unitary action
or an actual classical cubic cover. The linear result is the full
source alternative, including the literal ambient star residual. -/
theorem cubic_alternatives_or_unitary_or_classical_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : 1 < primeRank 3 K)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives 3 K ∨
      (Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))) ∧
        CubicUnitaryModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
      (Nat.card (center (twoCoreComponent K)) = 3 ∧
        ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
          IsSLSign (twoCoreComponent K) unitary 3 q) := by
  rcases alternatives_or_even_or_cubic_center hH hK Nat.prime_three (by decide) hr a ha haK hgen
    with halt | ⟨hz, hm⟩ | ⟨_, hc, hm⟩
  · exact Or.inl halt
  · have hz' : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))) := by
      rwa [← Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
    rcases cubic_alternatives_or_unitary_of_even_model hH hK hr hz' hm a ha haK hgen with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hz', h⟩)
  · rcases hm with hm | hm
    · exact Or.inr (Or.inr ⟨hc, hm⟩)
    · exact (not_mathieu_twoCore_cover hH hK hr a ha haK hm).elim

/-- The still-open actor cases after the fixed-subfield and Mathieu exclusions.
This is a remainder, not a replacement for any source alternative. -/
def ActorRemainder (p : ℕ) (K : Subgroup H) : Prop :=
  (p ≠ 3 ∧ Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) ∧
    EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))) ∧
    CubicUnitaryModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
  (p = 3 ∧ Nat.card (center (twoCoreComponent K)) = 3 ∧
    ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
      IsSLSign (twoCoreComponent K) unitary 3 q)

/-- The complete current reduction on the original split-prime hypotheses.
Final assembly still has to discharge the three retained actor cases. -/
theorem alternatives_or_actor_remainder
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ ActorRemainder p K := by
  by_cases hp3 : p = 3
  · cases hp3
    rcases cubic_alternatives_or_unitary_or_classical_cover hH hK hr a ha haK hgen
      with h | ⟨hz, hm⟩ | ⟨hz, hm⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hz, hm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hz, hm⟩))
  · rcases alternatives_or_even_or_cubic_center hH hK hp ho hr a ha haK hgen
      with h | ⟨hz, hm⟩ | ⟨hp3', _, _⟩
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨hp3, ?_, hm⟩)
      rwa [← Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
    · exact (hp3 hp3').elim

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
