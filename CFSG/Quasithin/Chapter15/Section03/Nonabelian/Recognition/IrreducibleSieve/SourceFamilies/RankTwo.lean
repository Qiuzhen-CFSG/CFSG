module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.EvenDegree
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.G2
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.ExceptionalTwisted
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Alternating
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Every characteristic-two rank-two model is excluded in the source sieve

Each literal constructor of Theorem C is dispatched to an exclusion for the
original faithful action and elementary actor. The binary symplectic derived
carrier is transported through its proved equivalence with A₆. All other
quotients and exceptional derived carriers are retained by their family proofs.

Source: Aschbacher--Smith, G.9.3, printed pp.354--357, and the irreducible
branch of 15.3.58, printed p.1149.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The quotient-first derived group over F₂ is the actual A₆ carrier. -/
theorem SourceData.not_symplecticFour_derived_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K)
    (model : Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := model
  exact SourceFamilies.Alternating.not_six_component h hK
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)

/-- Every literal characteristic-two rank-two model from Theorem C is
impossible for the original irreducible source action. -/
theorem SourceData.not_rankTwo_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    {n : ℕ} (model : ChapterA.Section02.IsTheoremCRankTwoModel K n) : False := by
  cases model with
  | linear hn hm => exact h.not_linearThree_source hK hn hm
  | symplectic hn hm => exact h.not_symplecticFour_component hK hn hm
  | g2 hn hm => exact h.not_g2_component hK hn hm
  | triality hn hm => exact h.not_triality_model hK hq hsimple hnonab hn hm
  | ree_f4 m hm _ he => exact h.not_ree_f4_model hK hq hsimple hnonab hm he
  | symplectic_derived _ hm => exact h.not_symplecticFour_derived_component hK hm
  | g2_derived _ hm => exact h.not_g2_derived_component hK hm
  | tits _ hm => exact h.not_tits_model hK hq hsimple hnonab hm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
