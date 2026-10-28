module
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SemilinearFixedPointCentralizer

/-!
# Extending a marked component module across a commuting factor

If two subgroups generate an actor and the second centralizes the marked
module, the original conjugation action is exactly the representation of the
first quotient factor. A two-subgroup of its normalizer has a nonzero fixed
vector when the whole module is marked with trivial kernel.
The application is the paired geometry in Aschbacher--Smith 10.1.1--2,
printed pp.741--742.
-/

public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {L K R W : Subgroup G} [IsElementaryAbelian 2 W]
  {ρ : Representation (ZMod 2) L V}
  (d : BinaryConjugationSection L W ⊥ ρ)

/-- Extend the literal module to a generated pair, with the second factor
acting trivially, while retaining the prescribed quotient map. -/
theorem original_action_eq_quotient
    (hgen : L ⊔ K = R) (hRW : R ≤ normalizer (W : Set G))
    (hKW : K ≤ centralizer (W : Set G))
    (f : R →* J) (σ : Representation (ZMod 2) J V)
    (hL : ∀ l : L, σ (f ⟨l,(le_sup_left.trans (le_of_eq hgen)) l.property⟩) = ρ l)
    (hK : ∀ k : K, f ⟨k,(le_sup_right.trans (le_of_eq hgen)) k.property⟩ = 1)
    (r : R) (w : W) :
    (d.coordinates (W.normalizerMonoidHom (inclusion hRW r) w)).toAdd =
      σ (f r) (d.coordinates w).toAdd := by
  obtain ⟨τ,hτ⟩ := d.exists_original_quotient_action hRW
    (by rw [normalizer_eq_top]; exact le_top)
  have htop : L.subgroupOf R ⊔ K.subgroupOf R = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (le_sup_left.trans (le_of_eq hgen)),
      map_subgroupOf_eq_of_le (le_sup_right.trans (le_of_eq hgen)),
      ←MonoidHom.range_eq_map, range_subtype, hgen]
  have heq : L.subgroupOf R ⊔ K.subgroupOf R ≤ τ.eqLocus (σ.comp f) := by
    apply sup_le
    · intro l hl
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
      have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
      rw [←hv,hτ]
      change _ = σ (f l) _
      rw [hL ⟨l,hl⟩]
      exact d.equivariant ⟨l,hl⟩ w
    · intro k hk
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
      have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
      rw [←hv,hτ]
      change _ = σ (f k) _
      rw [hK ⟨k,hk⟩,map_one,Module.End.one_apply]
      congr 2
      apply Subtype.ext
      change (k : G)*(w : G)*(k : G)⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr (hKW hk w w.property).symm
  have he : τ r = σ (f r) := heq (htop.symm ▸ mem_top r)
  rw [←he,hτ]

/-- The original two-subgroup stabilizer has a nonidentity fixed vector in a
whole marked module. The conclusion concerns actual commuting elements. -/
theorem exists_nonidentity_fixed [Finite V] [Nontrivial V]
    (P : Subgroup G) (hPW : P ≤ normalizer (W : Set G)) (hP : IsPGroup 2 P) :
    ∃ w : W, d.coordinates w ≠ 1 ∧ (w : G) ∈ centralizer (P : Set G) := by
  obtain ⟨τ,hτ⟩ := d.exists_original_quotient_action hPW
    (by rw [normalizer_eq_top]; exact le_top)
  obtain ⟨v,hv,hPv⟩ := SemilinearFixedPointCentralizer.exists_nonzero_fixed τ ⊤
    (hP.of_injective (⊤ : Subgroup P).subtype (⊤ : Subgroup P).subtype_injective)
  obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
  have hi : Function.Injective d.coordinates :=
    (MonoidHom.ker_eq_bot_iff d.coordinates).mp (by rw [d.kernel_eq,bot_subgroupOf])
  refine ⟨w,fun he => hv (congrArg Multiplicative.toAdd (hw.symm.trans he)),?_⟩
  intro p hp
  have he := hPv (⟨⟨p,hp⟩,mem_top _⟩ : (⊤ : Subgroup P))
  rw [←show (d.coordinates w).toAdd = v from congrArg Multiplicative.toAdd hw,hτ] at he
  have hh := congrArg Subtype.val (hi (Multiplicative.toAdd.injective he))
  change p*(w : G)*p⁻¹ = w at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
end Representation.BinaryConjugationSection
