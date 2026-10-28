module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.TorusSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore

/-!
# Abelianness of the original SL₃ natural closure

This is the SL₃ branch of 11.5.7 on the original chosen module. The
three-dimensional field flag identifies V₃ with V. The proved 11.5.5
application then supplies the closure's two-core containment, Frattini
bound and centrality modulo V₁. Under nonabelianness, the constructed
Cartan frame and its natural/dual layers give S ≤ O₂(G₁) and S=S₂.
The block argument excludes the field-four exceptional extension and
proves K=L₁, the original core identities and the two-copy natural action.
Its actual odd-order multiplicity image gives the even-degree contradiction;
the odd-degree contradiction uses T∩K and the proved centralizer normalization.

The explicit boundary consists of preceding Chapter 11 conclusions:
the marked field flag and local irreducibility, the relative-component
alternatives of 11.1.2 and 11.4.1, G₁=KYM₁ from 11.4.3(2), the natural
sum from 11.5.5(3), the two Cartan bounds of 11.5.6(4–5), and the original
outside-H selection and Sylow-normalizer bound. The flag is genuine
geometric data; `Geometry` itself only names the original subgroups.
Their discharge belongs to `qt-d-1222-natural-closure` and
`qt-d-1222-natural-closure-cartan`; the natural-sum producer is
`qt-d-1222-cartan-natural-sum`. No conclusion of this SL₃ branch is assumed.

All quotients, residuals and right conjugates are those of the original
geometry. In particular L₁ is the solvable residual, and no equality
W=T∩L is used. Source: Aschbacher–Smith, combined manuscript, 11.5.7,
printed pp.781–782; G.2.5, printed pp.335–336.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open LocalGeometry LocalGeometry.Components

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

/-- The SL₃ closure conclusion of 11.5.7, conditional only on the named
preceding source conclusions. The marked three-conjugate hypothesis, core
collapse, exceptional exclusion, multiplicity and both parity contradictions
are constructed and applied in the proof. -/
theorem isMulCommutative_of_source
    (b : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (b.space 0))
    (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (b.space 2))
    (f : E.ClosureFlag)
    (hX : IsCartan T L E.X) (hXG : E.X ≤ E.G₁)
    (hnormal : Source.NormalComponentIn E.G₁ E.K)
    (hcases : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcartan : ∀ A : Subgroup G, A ≤ (T : Subgroup G) → A = ⁅A,E.X⁆ →
      (frattini A).map A.subtype ≤ E.G₁.pCoreIn 2 → ⁅A,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsum : ∀ hK : E.K = E.L₁, ∃ r : ℕ,
      Nonempty (ActionEquiv (Block.Multiplicity.action E f hK)
        (repeated (linearNatural E.input.field 2) r)))
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁)
    (hrespoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K,outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hNT : normalizer (T : Set G) ≤ E.M) : IsMulCommutative E.W := by
  classical
  by_contra hn
  have hG₁ : IsSQTK KnownSimple.IsKnownSimple E.G₁ :=
    E.input.source.simpleQTKE.twoLocal_sqtk
      (D.centralQuotientPreimage_twoLocal E.point f.point_nonzero)
  have hseed := Block.Multiplicity.seed_eq E m b hthree
  have hUW : E.U = E.W := by
    change conjugateSpanBy E.V₃ E.G₁ = conjugateSpanBy V E.G₁
    rw [hseed]
  obtain ⟨hcore, _, hfrattini, hcentral⟩ := E.globalClosure_core_and_frattini
    f.point_nonzero f.point_le_seed f.point_ne_seed f.sylow_normalizes_point
    f.local_normalizes_seed f.seed_irreducible
  rw [hUW] at hcore hfrattini hcentral
  have hUT : E.W ≤ (T : Subgroup G) := by
    have ht := pCoreIn_le_sylow E.G₁ (T.subtype f.sylow_normalizes_point)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le f.sylow_normalizes_point] at ht
    exact hcore.trans ht
  have hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V := by
    simpa only [hseed] using f.seed_irreducible
  have hdim : Module.finrank E.input.field.Carrier (b.space 0) = 1 := b.dimension 0
  obtain ⟨x, y, _, _, ⟨d⟩, _, _, _, _, _, _, hcollapse⟩ :=
    exists_source_three_conjugates E m (b.space 0) hdim hpoint
      f.sylow_normalizes_point hX hXG hirr hUT hn hfrattini hcore hgen hcartan hcoreX
      hcentral
  obtain ⟨hK, _, _, _, _, _, ⟨pair⟩, _, _, _, hWK, _, hWL, _, hLV,
      _, _, _, _, _, _, _, _, _, _, hsplit⟩ :=
    Block.source_conclusions E d hG₁ hnormal hUT hfrattini hcollapse hcases htriangle
      f m b hpoint hthree hsum
  rcases Nat.even_or_odd E.input.field.degree with heven | hodd
  · obtain ⟨_, _, _, _, _, hab⟩ := Outside.multiplicity_structure_of_source E m pair
      (b.space 0) hdim hpoint hH hHG hXG hK hrespoint hselect hWK hLV hsplit
    exact Outside.TorusSylow.even_contradiction E m hX hH hHG hXG hK hWL hLV hWK
      heven hab
  · exact Outside.TorusSylow.odd_contradiction E m b hpoint hH hHG hK
      hrespoint hselect hWL hLV hWK hsplit hNT hodd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
