module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.CubicField
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.SourceReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.PairAction

/-!
# The moving-component branch of 13.6.6

Under the actual local source inputs, a moving component has the two-element
orbit supplied by 1.2.1(3). The residual alternatives exclude the normal cases,
and the complete model comparison leaves binary PSL₂ or Suzuki. Specializing
universal 1.2.2(a) excludes PSL₂ by the marked involution centralizer.

The Suzuki equivalence is adjusted by an explicitly constructed automorphism
so that an actual cubic element of Lᵥ acts by an order-three field automorphism.
Both factors of the orbit's center quotient use these same coordinates. The
factor embeddings, component permutation and source field exponent are retained.
The full source assembly still supplies the earlier local/model/residual inputs
and universal 1.2.2(a); the independent SuzukiPair owner proves the Borel
contradiction. This conditional reduction does not itself prove Tv normalizes K.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 13.6.6,
printed p.927. Centers are retained, including source m=3.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open A5Module BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The actual paired configuration required by the Borel contradiction.
The natural number `parameter` is the matrix parameter; the source field
degree is `2 * parameter + 1`. Both factors use the same component model
as the literal residual action. -/
structure SuzukiPairConfiguration (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hn : residual s ≤ X K) where
  parameter : ℕ
  positive : 1 ≤ parameter
  model : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup parameter
  coordinates : PairCoordinates K (localT T (markedV s)) model
  cubic : CubicFieldAction K (residual s) hn parameter model

variable {s : Marking L V} {T : Subgroup G} {K : Subgroup (Gv (markedV s))}
  {hn : residual s ≤ X K}

/-- The paired-Borel marking on the literal ambient component orbit. -/
noncomputable def SuzukiPairConfiguration.ambientMarking
    (c : SuzukiPairConfiguration s T K hn) :
    SuzukiPair.Marking T (K.map (Gv (markedV s)).subtype) (markedV s) :=
  c.coordinates.ambientMarking c.positive

/-- Both ambient component factors, with the actual moving element and permutation. -/
theorem SuzukiPairConfiguration.nonempty_ambientFactors
    (c : SuzukiPairConfiguration s T K hn) :
    Nonempty (SuzukiPair.PairFactors c.ambientMarking) :=
  c.coordinates.nonempty_ambientFactors c.positive

/-- The actual order-three element of Lᵥ acts on the first coordinate by the
same order-three field automorphism used to construct the component model. -/
theorem SuzukiPairConfiguration.ambientCubic
    (c : SuzukiPairConfiguration s T K hn) (hK : IsComponent (Gv (markedV s)) K)
    (hi : (X K).index = 2) :
    ∃ g : G, g ∈ Lv L (markedV s) ∧ orderOf g = 3 ∧
      ∃ hg : g ∈ normalizer
          (SuzukiPair.orbit T (K.map (Gv (markedV s)).subtype) (markedV s) : Set G),
        ∀ x : SuzukiPair.orbit T (K.map (Gv (markedV s)).subtype) (markedV s),
          (c.ambientMarking.quotientMap
            ((SuzukiPair.orbit T (K.map (Gv (markedV s)).subtype) (markedV s)).normalizerMonoidHom
              ⟨g, hg⟩ x)).1 =
            suzukiFieldAut c.parameter c.cubic.field
              (c.ambientMarking.quotientMap x).1 := by
  have hm : ¬ localT T (markedV s) ≤ X K :=
    fun h => c.coordinates.moved (h c.coordinates.moving.property)
  let := moving_orbit_normal K (localT T (markedV s)) hi hm
  have hd : (c.cubic.cubic : Gv (markedV s)) ∈
      normalizer (componentOrbit K (localT T (markedV s)) : Set (Gv (markedV s))) :=
    le_normalizer_of_normal (mem_top _)
  refine ⟨((c.cubic.cubic : Gv (markedV s)) : G), c.cubic.cubic.property, ?_,
    ambientOrbit_normalizes hd, ?_⟩
  · exact (orderOf_injective ((Gv (markedV s)).subtype.comp (residual s).subtype)
      ((Gv (markedV s)).subtype_injective.comp (residual s).subtype_injective)
      c.cubic.cubic).trans c.cubic.cubic_order
  · intro x
    have he := c.coordinates.ambientMarking_first_action c.positive hK hi
      (residual s) hn c.cubic.cubic hd x
    rw [c.cubic.action_eq] at he
    exact he

/-- Odd-core vanishing controls the retained center of the actual ambient pair. -/
theorem SuzukiPairConfiguration.ambientCenter_two [Finite G]
    (c : SuzukiPairConfiguration s T K hn)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥) (hi : (X K).index = 2) :
    IsPGroup 2 (center (SuzukiPair.orbit T (K.map (Gv (markedV s)).subtype) (markedV s))) := by
  have hm : ¬ localT T (markedV s) ≤ X K :=
    fun h => c.coordinates.moved (h c.coordinates.moving.property)
  exact (moving_orbit_center_two K (localT T (markedV s)) hodd hi hm).of_equiv
    (centerCongr (ambientOrbitEquiv T (markedV s) K))

universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}
open InitialSieve

/-- Construct the paired Suzuki configuration from the complete earlier local
inputs. The field exponent is preserved, and the actual cubic field action
forces it to be divisible by three. Central covers are retained throughout. -/
theorem exists_suzukiPairConfiguration (d : Setup κ T s) (earlier : Earlier122A κ G)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hres : ResidualAlternatives s K i.action m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    primeRank 3 K ≤ 1 ∧
      ∃ c : SuzukiPairConfiguration s (T : Subgroup G) K i.action.residual_normalizes,
        m = 2 * c.parameter + 1 ∧ 3 ∣ m := by
  have hrank := moving_rank_one K i.action i.moving hres
  have comparison := ModelComparison.source_comparison i
  obtain ⟨n, hn, hm, ⟨e₀⟩⟩ := comparison.model.resolve_left
    (not_psl2_of_source d earlier i hcard)
  have hKD : ⁅K, residual s⁆ ≠ ⊥ := by
    rw [i.action.commutator_residual]
    exact i.component.isCComponent.ne_bot
  obtain ⟨eK, ⟨cubic⟩⟩ := exists_cubicFieldAction K (residual s) i.component
    i.action.residual_normalizes (residual_twoPerfect s) hcard hKD n hn e₀
  obtain ⟨coordinates⟩ := exists_pairCoordinates K (localT (T : Subgroup G) (markedV s))
    i.component comparison.index i.moving eK
  exact ⟨hrank, ⟨n, hn, eK, coordinates, cubic⟩, hm,
    hm.symm ▸ cubic.three_dvd_degree⟩

/-- The actual configuration consumed by the independent paired-Suzuki Borel
branch: its literal ambient marking, both factors, central kernel and cubic
field action. All extra local inputs are earlier source inputs, not the pair
identification or its action. -/
theorem exists_ambientSuzukiPair (d : Setup κ T s) (earlier : Earlier122A κ G)
    {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (i : ModelComparison.SourceInput s (T : Subgroup G) K m)
    (hres : ResidualAlternatives s K i.action m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    ∃ p : SuzukiPair.Marking (T : Subgroup G) (K.map (Gv (markedV s)).subtype) (markedV s),
      m = 2 * p.parameter + 1 ∧ 3 ∣ m ∧ Nonempty (SuzukiPair.PairFactors p) ∧
      IsPGroup 2 (center (SuzukiPair.orbit (T : Subgroup G)
        (K.map (Gv (markedV s)).subtype) (markedV s))) ∧
      ∃ g : G, g ∈ Lv L (markedV s) ∧ orderOf g = 3 ∧
        ∃ hg : g ∈ normalizer (SuzukiPair.orbit (T : Subgroup G)
            (K.map (Gv (markedV s)).subtype) (markedV s) : Set G),
          ∃ σ : BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * p.parameter + 1) ≃ₐ[ZMod 2]
              BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * p.parameter + 1),
            orderOf σ = 3 ∧
              ∀ x : SuzukiPair.orbit (T : Subgroup G) (K.map (Gv (markedV s)).subtype) (markedV s),
                (p.quotientMap ((SuzukiPair.orbit (T : Subgroup G)
                  (K.map (Gv (markedV s)).subtype) (markedV s)).normalizerMonoidHom ⟨g, hg⟩ x)).1 =
                    suzukiFieldAut p.parameter σ (p.quotientMap x).1 := by
  obtain ⟨_, c, hm, hthree⟩ := exists_suzukiPairConfiguration d earlier i hres hcard
  have hi := (ModelComparison.moving_index_and_model _ K i.moving i.localModels).1
  obtain ⟨g, hg, hg3, hgN, hact⟩ := c.ambientCubic i.component hi
  exact ⟨c.ambientMarking, hm, hthree, c.nonempty_ambientFactors,
    c.ambientCenter_two i.oddCore hi, g, hg, hg3, hgN,
    c.cubic.field, c.cubic.field_order, hact⟩

/-- Consumer of the complete published large-field branch, including all
simple/two-cover alternatives and the literal central four-group. -/
theorem exists_suzukiPairConfiguration_of_largeField (d : Setup κ T s)
    (earlier : Earlier122A κ G) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (h115 : Chapter15.Section03.Candidates.ComponentStructure.ModelAction115 K
      (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩))
    (hmove : ¬ localT (T : Subgroup G) (markedV s) ≤ X K)
    (h121 : K.Normal ∨
      (Set.range fun g : Gv (markedV s) => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (K ⧸ pCore 2 K))
    (hlarge : LargeField K a)
    (hres : ∀ m, 1 < m → BinaryModelAt (NormalizerAction.componentImage K) m →
      EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K →
      ResidualAlternatives s K a m)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    primeRank 3 K ≤ 1 ∧
      Nonempty (SuzukiPairConfiguration s (T : Subgroup G) K a.residual_normalizes) := by
  obtain ⟨m, hm, hb, hE⟩ := hlarge
  let i : ModelComparison.SourceInput s (T : Subgroup G) K m :=
    ⟨hK, hodd, ⟨d.sylow, (localT_eq_sylow _ _ d.sylow d.sylow_image).symm⟩,
      a, h115, hmove, h121, hm, hb, hE⟩
  obtain ⟨hrank, c, _, _⟩ := exists_suzukiPairConfiguration d earlier i
    (hres m hm hb hE) hcard
  exact ⟨hrank, ⟨c⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
