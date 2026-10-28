module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Basic
public import Theory.GroupTheory.NilpotentCommutingFamily
public import Theory.GroupTheory.PrimeOrderConjugation
public import Theory.GroupAction.ThreeSupportDisplacement

/-!
# The maximal-family normalizer argument for small supports

A commuting subfamily has independent actors and supports under the local
support-rigidity premise. Choose a maximal such family: its join contains
exactly its canonical members, and conjugation by the normalizer permutes them.
The generic nilpotent normalizer theorem reduces global commutation to proving
that canonical actors normalizing this join centralize every chosen factor.

If a canonical actor moves a chosen factor, its odd order gives three distinct
successive conjugates. Their independent supports force the displacement to
have at least the square of the allowed support cardinality, a contradiction.
Thus each normalizing actor fixes, and hence centralizes, every chosen factor.
The nilpotent reduction then proves global commutation from local rigidity.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.12(1–2), printed pp.183–184.
-/

namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]

/-- Each canonical prime-order actor is abelian. -/
public theorem smallSupportFactor_le_centralizer_self
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) :
    X ≤ Subgroup.centralizer (X : Set G) := by
  let _ : IsCyclic X := smallSupportFactor_isCyclic hk hX
  exact Subgroup.le_centralizer X

/-- Local rigidity makes the actors and supports of any commuting subfamily independent. -/
public theorem smallSupport_commuting_subfamily_independent
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hlocal : ∀ X ∈ smallSupportFactors G V k,
      ∀ Y ∈ smallSupportFactors G V k, X ≠ Y →
      X ≤ Subgroup.centralizer (Y : Set G) →
      commutatorAction Y V ≤ FixedPoints.subgroup X V)
    (Δ : Set (Subgroup G)) (hΔ : Δ ⊆ smallSupportFactors G V k)
    (hcomm : Subgroup.IsCommutingFamily Δ) :
    iSupIndep (fun X : Δ => X.val) ∧
      iSupIndep (fun X : Δ => commutatorAction X.val V) := by
  have hcop (X : Δ) := smallSupportFactor_coprime hk (hΔ X.property)
  have hcross (X Y : Δ) (hne : X ≠ Y) :
      commutatorAction Y.val V ≤ FixedPoints.subgroup X.val V :=
    hlocal X.val (hΔ X.property) Y.val (hΔ Y.property)
      (fun heq => hne (Subtype.ext heq)) (hcomm X.val X.property Y.val Y.property)
  exact ⟨ActionSupport.actors_iSupIndep _ hcop hcross,
    ActionSupport.supports_iSupIndep _ hcop hcross⟩

/-- Choose a maximal commuting family, identify its canonical factors inside the
join, and obtain actual independence of both the actors and supports. -/
public theorem smallSupport_exists_maximal_commuting_family
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hlocal : ∀ X ∈ smallSupportFactors G V k,
      ∀ Y ∈ smallSupportFactors G V k, X ≠ Y →
      X ≤ Subgroup.centralizer (Y : Set G) →
      commutatorAction Y V ≤ FixedPoints.subgroup X V) :
    ∃ Δ : Set (Subgroup G),
      Maximal (fun Δ => Δ ⊆ smallSupportFactors G V k ∧
        Subgroup.IsCommutingFamily Δ) Δ ∧
      (∀ X ∈ smallSupportFactors G V k, X ∈ Δ ↔ X ≤ sSup Δ) ∧
      iSupIndep (fun X : Δ => X.val) ∧
      iSupIndep (fun X : Δ => commutatorAction X.val V) := by
  obtain ⟨Δ, hmax⟩ := Subgroup.exists_maximal_commuting_subfamily (smallSupportFactors G V k)
  refine ⟨Δ, hmax, ?_, smallSupport_commuting_subfamily_independent hk hlocal Δ hmax.1.1 hmax.1.2⟩
  intro X hX
  exact Subgroup.mem_maximal_commuting_subfamily_iff_le_join
    (fun _ hY => smallSupportFactor_le_centralizer_self hk hY) hmax hX

/-- The nilpotent normalizer argument reduces global commutation to the action
calculation for canonical actors normalizing a maximal commuting join. -/
public theorem smallSupport_commutingFamily_of_normalizer_centralizes
    [Finite G] {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hstep : ∀ Δ,
      Maximal (fun Δ => Δ ⊆ smallSupportFactors G V k ∧
        Subgroup.IsCommutingFamily Δ) Δ →
      ∀ X ∈ smallSupportFactors G V k,
        X ≤ Subgroup.normalizer ((sSup Δ : Subgroup G) : Set G) →
      ∀ Y ∈ Δ, X ≤ Subgroup.centralizer (Y : Set G)) :
    ∀ X ∈ smallSupportFactors G V k, ∀ Y ∈ smallSupportFactors G V k,
      X ≤ Subgroup.centralizer (Y : Set G) := by
  exact Subgroup.commutingFamily_of_normalizer_centralizes
    (smallSupportFactors G V k) (smallSupportGroup G V k) rfl
    (fun _ hX g => smallSupportFactors_conjBy hX g)
    (fun _ hX => smallSupportFactor_le_centralizer_self hk hX) hstep

/-- A canonical actor normalizing a maximal commuting join centralizes its factors. -/
public theorem smallSupportFactor_centralizes_of_le_normalizer
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hlocal : ∀ X ∈ smallSupportFactors G V k,
      ∀ Y ∈ smallSupportFactors G V k, X ≠ Y →
      X ≤ Subgroup.centralizer (Y : Set G) →
      commutatorAction Y V ≤ FixedPoints.subgroup X V)
    {Δ : Set (Subgroup G)}
    (hmax : Maximal (fun Δ => Δ ⊆ smallSupportFactors G V k ∧
      Subgroup.IsCommutingFamily Δ) Δ)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k)
    (hXN : X ≤ Subgroup.normalizer ((sSup Δ : Subgroup G) : Set G))
    {Y : Subgroup G} (hY : Y ∈ Δ) :
    X ≤ Subgroup.centralizer (Y : Set G) := by
  have hp : (2 * k + 1).Prime := by rcases hk with rfl | rfl <;> decide
  have hpodd : 2 * k + 1 ≠ 2 := by rcases hk with rfl | rfl <;> decide
  apply Subgroup.le_centralizer_of_prime_card_of_le_normalizer Y X hp
    (hmax.1.1 hY).2.1 hX.2.1
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change Y.conjBy g = Y
  by_contra hmove
  have hconj {Z : Subgroup G} (hZ : Z ∈ Δ) : Z.conjBy g ∈ Δ :=
    Subgroup.conj_mem_maximal_commuting_subfamily (F := smallSupportFactors G V k)
      (fun _ hZ a => smallSupportFactors_conjBy (V := V) hZ a)
      (fun _ hZ => smallSupportFactor_le_centralizer_self (V := V) hk hZ) hmax hZ (hXN hg)
  have hY₁ := hconj hY
  have hY₂ := hconj hY₁
  obtain ⟨hne₀₁, hne₀₂, hne₁₂⟩ :=
    Subgroup.conjBy_three_pairwise_ne_of_mem_prime_card Y X hp hpodd hX.2.1 hg hmove
  let i₀ : Δ := ⟨Y, hY⟩
  let i₁ : Δ := ⟨Y.conjBy g, hY₁⟩
  let i₂ : Δ := ⟨(Y.conjBy g).conjBy g, hY₂⟩
  have hi₀₁ : i₀ ≠ i₁ := fun h => hne₀₁ (congrArg Subtype.val h)
  have hi₀₂ : i₀ ≠ i₂ := fun h => hne₀₂ (congrArg Subtype.val h)
  have hi₁₂ : i₁ ≠ i₂ := fun h => hne₁₂ (congrArg Subtype.val h)
  have hind := (smallSupport_commuting_subfamily_independent (V := V) hk hlocal Δ
    hmax.1.1 hmax.1.2).2
  have hdis₀ : Disjoint (commutatorAction Y V)
      (commutatorAction (Y.conjBy g) V ⊔
        commutatorAction ((Y.conjBy g).conjBy g) V) := by
    exact (hind i₀).mono_right (sup_le
      (le_iSup₂_of_le i₁ hi₀₁.symm le_rfl)
      (le_iSup₂_of_le i₂ hi₀₂.symm le_rfl))
  have hdis₁ : Disjoint (commutatorAction (Y.conjBy g) V)
      (commutatorAction ((Y.conjBy g).conjBy g) V) :=
    (hind i₁).mono_right (le_iSup₂_of_le i₂ hi₁₂.symm le_rfl)
  have hbound := commutatorAction_card_ge_mul_of_three_supports X g hg
    (commutatorAction Y V) (commutatorAction (Y.conjBy g) V)
    (commutatorAction ((Y.conjBy g).conjBy g) V)
    (smallSupport_support_conjBy Y g) (smallSupport_support_conjBy (Y.conjBy g) g)
    hdis₀ hdis₁
  rw [(hmax.1.1 hY).2.2, (hmax.1.1 hY₁).2.2, hX.2.2] at hbound
  have hlt : 2 ^ (2 * k) < 2 ^ (2 * k) * 2 ^ (2 * k) := by
    rcases hk with rfl | rfl <;> norm_num
  exact (Nat.not_le_of_lt hlt) hbound

/-- Local support rigidity forces all canonical small-support factors to commute. -/
public theorem smallSupport_commutingFamily_of_local_rigidity
    [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hlocal : ∀ X ∈ smallSupportFactors G V k,
      ∀ Y ∈ smallSupportFactors G V k, X ≠ Y →
      X ≤ Subgroup.centralizer (Y : Set G) →
      commutatorAction Y V ≤ FixedPoints.subgroup X V) :
    ∀ X ∈ smallSupportFactors G V k, ∀ Y ∈ smallSupportFactors G V k,
      X ≤ Subgroup.centralizer (Y : Set G) := by
  apply smallSupport_commutingFamily_of_normalizer_centralizes hk
  intro Δ hmax X hX hXN Y hY
  exact smallSupportFactor_centralizes_of_le_normalizer hk hlocal hmax hX hXN hY


end CFSG.Quasithin.ChapterD
