module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Application
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SmallBinaryCases
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

/-!
# The irreducible sieve in 15.3.58

The shared input retains the actual elementary actor, marked central involution,
quadratic form, Sylow fixed line, and all three prime-to-three restrictions.
Minimal normality and actual conjugation compare the two component restrictions,
and all hypotheses for G.9.3 are constructed using the original actor and the
literal SQTK cover. The four model sieves exclude all eighteen alternatives,
including the ten-dimensional L₅ modules and every field parameter. Case (14)
identifies only the component action with the nine-dimensional tensor action.

`G93SourceTheorem` is the universal earlier classification input, independent
of all Chapter 15 geometric restrictions. It retains every source alternative
and the original actor rank. `SourceData.false_of_G93` constructs its application
hypotheses and discharges every model exclusion. `source_irreducible_false`
specializes this contradiction to the literal action on `U/Z` and constructs
the SQTK cover from the original centralizer. The parent assembly still supplies
the earlier local data, minimal-normal reduction, and this universal G.9.3 input;
no proof of the universal classification itself is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149;
G.9.1 and G.9.3, pp.351–357. The correction to case (14) is explained in
`docs/quasithin-proof-basis.md`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open CFSG.Quasithin.ChapterG.Section09
open scoped IsMulCommutative

universe u w f

/-- The exhaustive G.9.3 conclusion, grouped only to share the four proved
sieves. The groups and modules are identified by actual equivalences in each
alternative. Cases (0)–(2), (6),(8)–(10), (3)–(5),(11)–(13), and
(7),(14)–(17) occur in the four respective disjuncts. In (14) the identification
concerns the component join `K`, not the entire ambient actor `H`. -/
def Alternative {H : Type u} [Group H] {W : Type w}
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  MathieuCases.Alternative ρ K m ∨
    NaturalCases.Alternative.{u, w, f} ρ K m ∨
    SmallBinaryCases.Alternative ρ K m ∨ TensorCases.Alternative ρ K m

/-- The adequate universal G.9.3 statement, with the corrected component-action
conclusion in case (14). This is an explicit earlier source witness, not an axiom
or a classification proof. Its only premises are G.9.1 and G.9.3, packaged by
`ComponentHypothesis`; none of `SourceData` or `ComponentData` is assumed.
The source application instantiates `C` with the full known-simple class. -/
def G93SourceTheorem (C : GroupClass.{u}) : Prop :=
  ∀ {H : Type u} [Group H] [Finite H]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (X L K : Subgroup H) (m : ℕ),
    ComponentHypothesis C ρ X L K m → Alternative.{u, w, f} ρ K m

variable {H : Type u} [Group H] [Finite H]
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H}
  {T : Sylow 2 H} {v : H} {s : ℕ}

/-- Every alternative is impossible with the source geometry. All model
calculations, including involution placement in the component where needed,
are discharged in the four family sieves. -/
theorem SourceData.not_alternative (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) : ¬ Alternative.{u, w, f} ρ K (s + 1) := by
  rintro (hm | hn | hb | ht)
  · exact MathieuCases.exclude h hK hm
  · exact NaturalCases.exclude h hK hn
  · exact SmallBinaryCases.exclude h hK hb
  · exact TensorCases.exclude h hK ht

/-- The K*-irreducible branch of 15.3.58 is impossible, conditional only on
the universal earlier G.9.3 theorem and the stated source inputs. The original
actor has rank `s + 1`; the SQTK cover and every component-application
hypothesis are supplied to G.9.3 before all alternatives are eliminated. -/
theorem SourceData.false_of_G93 {C : GroupClass.{u}}
    (hG93 : G93SourceTheorem.{u, w, f} C)
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hcover : Nonempty (SQTKCover C H)) : False := by
  obtain ⟨L, hL⟩ := h.componentHypothesis hK hcover
  exact h.not_alternative hK (hG93 ρ X L K (s + 1) hL)

/-- The actual Chapter 15 consumer: exclude irreducibility on the literal
`U/Z`, using the canonical centralizer-to-`H/O₂(H)` SQTK cover. The source
setup and normal-reduction owners supply `h` and `hK`; the only earlier
classification input is the universal `hG93`. -/
theorem source_irreducible_false {G : Type u} [Group G] [Finite G]
    (C : GroupClass.{u}) (hG93 : G93SourceTheorem.{u, u, f} C)
    (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    {X K : Subgroup (ActorQuotient Z)} {T : Sylow 2 (ActorQuotient Z)}
    {v : ActorQuotient Z} {s : ℕ}
    (h : SourceData (actorRepresentation Z ZS hkernel) X T v s)
    (hK : ComponentData (actorRepresentation Z ZS hkernel) K)
    (hcover : IsSQTK C (centralizerH Z)) : False :=
  h.false_of_G93 hG93 hK ⟨actorSQTKCover C Z hcover⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
