module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The symplectic Hall plane on the chosen Chapter12 module

The literal residual quotient constructs the original right Hall group as E₉
in the Sp₄(4) row, including its required source marking. Applying the original E₂₇ obstruction excludes cubic
actors, and hence the two alternating containing models at the smaller
changed Sylow, including for selected parabolic factors. No identification
of the selected factor with the generating H-component is assumed.

For the general marked symplectic row, divisibility of the right field
degree by the original left degree two or four proves normalization of the
actual residual from local control. Both marked and intrinsic-residual applications are supplied. For an A₅
selected factor, the alternating exclusions hold at every symplectic field
size. The remaining field comparison and source rows belong to the same
Cartan local-to-global assembly.

Source: Aschbacher–Smith 5.1.10, 5.2.2 and 12.2.2,
printed pp.634,648–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The prescribed right Hall plane and the source E₂₇ obstruction on the actual chosen module. -/
theorem rankOne_symplectic_four_hall_and_actor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧ p ≠ 3 := by
  have hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hB,hBc⟩ := c.right_cubic_plane_of_symplectic_four hi.sylow_normalizes hH hgen hC hc hF e he
  exact ⟨hB,hBc,c.symplectic_four_actor_not_cubic hi hd hH hgen hC hc hF e he⟩

/-- Normalization of the literal residual in the marked symplectic small-degree branch. -/
theorem rankOne_cartan_normalizes_of_symplectic_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hsmall : n = 2 ∨ n = 4) (hnf : n ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F) : A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany hn hpsl).cartan_normalizes_of_symplectic_small_degree
    hH hgen c hcontrol hsmall hnf hC hc hf hF e he

/-- The original symplectic four-field row excludes alternating containers
without asserting that the selected parabolic factor is an H-component. -/
theorem rankOne_prime_symplectic_four_not_alternating_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R K : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hSyl : Chapter1.IsSylowIn 2 (Prime.normalizingSylow T R)
      (Prime.generated L H D R ⊔ Prime.normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ Prime.generated L H D R ⊔ Prime.normalizingSylow T R)
    (hK : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) :=
  d.symplectic_four_not_alternating_seven_container
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen c hd hz
    hC hc hF e he hSyl hRK hKX hK hKn


/-- The original symplectic residual quotient constructs the prescribed Hall plane. -/
theorem rankOne_symplectic_residual_hall_plane
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 :=
  c.right_cubic_plane_of_symplectic_residual
    (M.rankOne_generic_input_of_many h hmany hn hpsl).sylow_normalizes hH hgen hm

/-- Normalization from the actual residual model, without a separate source marking. -/
theorem rankOne_cartan_normalizes_of_symplectic_residual_small_degree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hsmall : n = 2 ∨ n = 4) (hf : 1 < f) (hnf : n ∣ f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) :=
  (M.rankOne_generic_input_of_many h hmany hn hpsl).cartan_normalizes_of_symplectic_residual_small_degree
    hH hgen c hcontrol hsmall hf hnf hm

/-- Both alternating containing models are excluded in the original Sp₄(4)
residual row, retaining the actual changed Sylow and selected parabolic factor. -/
theorem rankOne_prime_symplectic_residual_not_alternating_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R K : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (Prime.normalizingSylow T R)
      (Prime.generated L H D R ⊔ Prime.normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ Prime.generated L H D R ⊔ Prime.normalizingSylow T R)
    (hK : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) :=
  d.symplectic_residual_not_alternating_container
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen c hd hz hm
    hSyl hRK hKX hK hKn

/-- The A₅ parabolic branch excludes alternating containers over every
original symplectic field, without equating any field parameters. -/
theorem rankOne_prime_A5_symplectic_residual_not_alternating_container
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {R K : Subgroup G} (d : Prime.LocalData T L H B D R)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥)
    (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (Prime.normalizingSylow T R)
      (Prime.generated L H D R ⊔ Prime.normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ Prime.generated L H D R ⊔ Prime.normalizingSylow T R)
    (hK : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (Prime.generated L H D R ⊔ Prime.normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) :=
  d.A5_right_symplectic_residual_not_alternating_container
    (M.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen c hd hz hf hm hA5
    hSyl hRK hKX hK hKn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
