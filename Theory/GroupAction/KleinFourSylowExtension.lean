module
public import Theory.GroupAction.KleinFourReturningPoint
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Sylow extensions of a full four-group action

For a full action on a four-group with two-group kernel, a nonidentity
point stabilizer is a two-group of index three. If a two-subgroup R fixes
that point, normalizes the original actor Y₀ and the plane, and contains
this point stabilizer, then R is Sylow in Y₀R. The plane centralizer in
Y₀R lies in R and equals its two-core.

The proof uses the actual conjugation action. Orbit-stabilizer gives the
index three, and product decomposition in Y₀R puts every element of the
plane centralizer in R. These are the group-theoretic steps in the
construction of Y in Aschbacher–Smith, proof of 14.7.32, printed p.1058.
-/

public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The point stabilizer for a full four-group action with two-group kernel. -/
theorem full_four_action_point_stabilizer (Y P : Subgroup G) [IsKleinFour P]
    (σ : Y →* MulAut P) (hσ : Function.Surjective σ)
    (hk : IsPGroup 2 σ.ker)
    (hconj : ∀ (y : Y) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹)
    (z : P) (hz : z ≠ 1) :
    IsPGroup 2 (Y ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) ∧
      (centralizer ({(z : G)} : Set G)).relIndex Y = 3 := by
  classical
  let : MulAction Y P := MulAction.compHom P σ
  let D : Subgroup Y := MulAction.stabilizer Y z
  have hD : D = (centralizer ({(z : G)} : Set G)).subgroupOf Y := by
    ext y
    change σ y z = z ↔ (y : G) ∈ centralizer ({(z : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have he := congrArg Subtype.val hh
      rw [hconj] at he
      exact (mul_inv_eq_iff_eq_mul.mp he)
    · intro hh
      apply Subtype.ext
      rw [hconj, hh, mul_inv_cancel_right]
  have hp : IsPGroup 2 D := by
    have hi := IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one (D.map σ) hz
      (by rintro f ⟨y,hy,rfl⟩; exact hy)
    have hpre := hi.comap_of_ker_isPGroup σ hk
    rw [comap_map_eq] at hpre
    exact hpre.to_le le_sup_left
  have horb : MulAction.orbit Y z = ({1} : Set P)ᶜ := by
    ext w
    constructor
    · rintro ⟨y,rfl⟩ he
      exact hz ((σ y).injective (he.trans (map_one _).symm))
    · intro hw
      let a : MulAut P := IsKleinFour.mulEquiv (Equiv.swap z w)
        (Equiv.swap_apply_of_ne_of_ne (Ne.symm hz) (Ne.symm hw))
      obtain ⟨y,hy⟩ := hσ a
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨y,by change σ y z = w; rw [hy]; exact Equiv.swap_apply_left z w⟩
  refine ⟨?_,?_⟩
  · have he : D.map Y.subtype = Y ⊓ centralizer ({(z : G)} : Set G) := by
      rw [hD,subgroupOf_map_subtype,inf_comm]
    exact he ▸ hp.map Y.subtype
  · change ((centralizer ({(z : G)} : Set G)).subgroupOf Y).index = 3
    rw [←hD, MulAction.index_stabilizer,horb,Set.ncard_compl,IsKleinFour.card_four,
      Set.ncard_singleton]

/-- A point-fixing two-subgroup containing the original point stabilizer
is Sylow in the extended actor, whose plane kernel is its two-core. -/
theorem full_four_action_sylow_extension (Y₀ R P : Subgroup G) [IsKleinFour P]
    (σ : Y₀ →* MulAut P) (hσ : Function.Surjective σ)
    (hk : IsPGroup 2 σ.ker)
    (hconj : ∀ (y : Y₀) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹)
    (z : P) (hz : z ≠ 1)
    (hY₀N : Y₀ ≤ normalizer (P : Set G))
    (hR : IsPGroup 2 R) (hRN : R ≤ normalizer (P : Set G))
    (hRY : R ≤ normalizer (Y₀ : Set G))
    (hRz : R ≤ centralizer ({(z : G)} : Set G))
    (hpoint : Y₀ ⊓ centralizer ({(z : G)} : Set G) ≤ R) :
    (∃ S : Sylow 2 (Y₀ ⊔ R : Subgroup G),
      (S : Subgroup (Y₀ ⊔ R : Subgroup G)).map (Y₀ ⊔ R : Subgroup G).subtype = R) ∧
      (Y₀ ⊔ R : Subgroup G) ⊓ centralizer (P : Set G) = (Y₀ ⊔ R : Subgroup G).pCoreIn 2 := by
  let Y := Y₀ ⊔ R
  have hYN : Y ≤ normalizer (P : Set G) := sup_le hY₀N hRN
  obtain ⟨_,hind⟩ := full_four_action_point_stabilizer Y₀ P σ hσ hk hconj z hz
  have hSylow := IsPGroup.exists_sylow_sup_of_coprime_index Y₀ R hR hRY
    ((centralizer ({(z : G)} : Set G)).subgroupOf Y₀)
    (by change ¬ 2 ∣ (centralizer ({(z : G)} : Set G)).relIndex Y₀; rw [hind]; decide)
    (by rw [subgroupOf_map_subtype,inf_comm]; exact hpoint)
  have hCR : Y ⊓ centralizer (P : Set G) ≤ R := by
    intro x hx
    have hx' : x ∈ ((Y₀ ⊔ R : Subgroup G) : Set G) := hx.1
    rw [coe_mul_of_right_le_normalizer_left Y₀ R hRY] at hx'
    obtain ⟨y,hy,r,hr,rfl⟩ := hx'
    have hyr : y*r ∈ centralizer ({(z : G)} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr z.property) hx.2
    have hyz : y ∈ centralizer ({(z : G)} : Set G) := by
      have he := (centralizer ({(z : G)} : Set G)).mul_mem hyr
        ((centralizer ({(z : G)} : Set G)).inv_mem (hRz hr))
      simpa only [mul_inv_cancel_right] using he
    exact R.mul_mem (hpoint ⟨hy,hyz⟩) hr
  let τ := P.normalizerMonoidHom.comp (inclusion hYN)
  have hτ : Function.Surjective τ :=
    full_conjugation_surjective_overgroup Y₀ Y P le_sup_left hYN σ hσ hconj
  have hker : τ.ker = (centralizer (P : Set G)).subgroupOf Y := by
    dsimp [τ]
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  refine ⟨hSylow,le_antisymm ?_ ?_⟩
  · exact le_pCoreIn_of_normalizes (hR.to_le hCR) inf_le_left
      ((le_inf Y.le_normalizer (hYN.trans (normalizer_le_normalizer_centralizer P))).trans
        inf_normalizer_le_normalizer_inf)
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := IsKleinFour.twoCore_le_ker_of_surjective P τ hτ hy
    rw [hker] at hh
    exact ⟨y.property,hh⟩

end Subgroup
