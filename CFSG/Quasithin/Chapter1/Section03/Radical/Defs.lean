module

public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The radical families in §1.3

The construction is exactly Ξ_p(L) = O²(X_p), where X_p is the full inverse
image of Ω₁(O_p(L/O₂(L))). The radical family retains nonquasisimplicity,
local-family membership, and the odd Fitting prime. The starred family uses
normality in a member of L*, with the relative inclusion stated explicitly.

The elementary facts below establish characteristic invariance, two-perfectness,
nontrivial two-core of Ξ_p(L)T, and the precise omega image. Identifying that
image with the entire p-core would fail for homocyclic groups of higher exponent.
The quotient shape and irreducibility in Lemma 1.3.3 require the earlier
structural alternatives and are not asserted by these definitions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.509 and 512–514, definitions preceding Lemma 1.3.3 and Proposition 1.3.8.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G]

/-- The subgroup Ω₁(O_p(L/O₂(L))) embedded in L/O₂(L). -/
def xiOmegaCore (p : ℕ) (L₀ : Subgroup G) : Subgroup (XiQuotient L₀) :=
  (omega (pCore p (XiQuotient L₀)) (p := p) 1).map (pCore p (XiQuotient L₀)).subtype

instance xiOmegaCore_characteristic (p : ℕ) (L₀ : Subgroup G) :
    (xiOmegaCore p L₀).Characteristic := by
  let := omega_characteristic (pCore p (XiQuotient L₀)) (p := p) 1
  exact Subgroup.characteristic_of_characteristic_of_characteristic

/-- The full inverse image X_p in L of Ω₁(O_p(L/O₂(L))). -/
def xiPPreimage (p : ℕ) (L₀ : Subgroup G) : Subgroup L₀ :=
  (xiOmegaCore p L₀).comap (QuotientGroup.mk' (pCore 2 L₀))

instance xiPPreimage_characteristic (p : ℕ) (L₀ : Subgroup G) :
    (xiPPreimage p L₀).Characteristic :=
  Characteristic.comap_quotient_mk inferInstance

/-- The two-residual O²(X_p), still as a subgroup of L. -/
def xiPIn (p : ℕ) (L₀ : Subgroup G) : Subgroup L₀ :=
  (pResidual 2 (xiPPreimage p L₀)).map (xiPPreimage p L₀).subtype

instance xiPIn_characteristic (p : ℕ) (L₀ : Subgroup G) :
    (xiPIn p L₀).Characteristic := by
  exact Subgroup.characteristic_of_characteristic_of_characteristic

/-- Ξ_p(L) in the ambient group, as defined before Lemma 1.3.3. -/
def XiP (p : ℕ) (L₀ : Subgroup G) : Subgroup G := (xiPIn p L₀).map L₀.subtype

/-- All source restrictions on the components and primes defining Ξ_rad. -/
def XiRad (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ L₀ ∈ L G T, ¬ Theory.GroupTheory.IsQuasisimple (XiQuotient L₀) ∧
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      X = XiP p L₀}

/-- Ξ*_rad consists of radical members normal in some member of L*.
Normality here is in L, not in the ambient group G. -/
def XiRadStar (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ XiRad G T ∧ ∃ L₀ ∈ LStar G T, X ≤ L₀ ∧ (X.subgroupOf L₀).Normal}

theorem XiP_le (p : ℕ) (L₀ : Subgroup G) : XiP p L₀ ≤ L₀ := map_subtype_le _

theorem XiP_subgroupOf (p : ℕ) (L₀ : Subgroup G) :
    (XiP p L₀).subgroupOf L₀ = xiPIn p L₀ := by
  change ((xiPIn p L₀).map L₀.subtype).comap L₀.subtype = xiPIn p L₀
  rw [comap_map_eq, ker_subtype, sup_bot_eq]

instance XiP_characteristic (p : ℕ) (L₀ : Subgroup G) :
    ((XiP p L₀).subgroupOf L₀).Characteristic := by
  rw [XiP_subgroupOf]
  infer_instance

theorem normalizer_le_normalizer_XiP (p : ℕ) (L₀ : Subgroup G) :
    normalizer (L₀ : Set G) ≤ normalizer (XiP p L₀ : Set G) :=
  normalizer_le_normalizer_characteristic_image L₀ (xiPIn p L₀)

theorem XiP_invariant (p : ℕ) {L₀ T : Subgroup G}
    (hT : T ≤ normalizer (L₀ : Set G)) : T ≤ normalizer (XiP p L₀ : Set G) :=
  hT.trans (normalizer_le_normalizer_XiP p L₀)

theorem XiP_isPPerfect [Finite G] (p : ℕ) (L₀ : Subgroup G) :
    IsPPerfect 2 (XiP p L₀) := by
  have h := isPPerfect_embedded_pResidual 2 (xiPPreimage p L₀)
  exact h.of_surjective ((xiPIn p L₀).equivMapOfInjective L₀.subtype
    L₀.subtype_injective).toMonoidHom
    ((xiPIn p L₀).equivMapOfInjective L₀.subtype L₀.subtype_injective).surjective


/-- Taking O² does not change the odd omega image. This is Ω₁(O_p),
not the full p-core when the homocyclic exponent is greater than p. -/
theorem xiPIn_map_quotient [Finite G] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (L₀ : Subgroup G) :
    (xiPIn p L₀).map (QuotientGroup.mk' (pCore 2 L₀)) = xiOmegaCore p L₀ := by
  unfold xiPIn
  rw [map_embedded_pResidual]
  have he : (xiPPreimage p L₀).map (QuotientGroup.mk' (pCore 2 L₀)) =
      xiOmegaCore p L₀ := map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _) _
  rw [he]
  have hω : IsPGroup p (xiOmegaCore p L₀) :=
    ((pCore_isPGroup (p := p) (G := XiQuotient L₀)).to_subgroup _).map _
  have hr : pResidual 2 (xiOmegaCore p L₀) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact (hω.orderOf_coprime (Nat.coprime_two_right.mpr hp) x).symm
  rw [hr]
  exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)


/-- The local-family Sylow condition makes Ξ_p(L)T a member of H. -/
theorem XiP_join_mem_H (p : ℕ) {L₀ T : Subgroup G} (hL : L₀ ∈ L G T) :
    XiP p L₀ ⊔ T ∈ H G := by
  obtain ⟨P, hP⟩ := hL.2.1
  have hcoreT : (L₀ ⊔ T).pCoreIn 2 ≤ T := by
    simpa only [hP] using pCoreIn_le_sylow (L₀ ⊔ T) P
  have hjoin : XiP p L₀ ⊔ T ≤ L₀ ⊔ T := sup_le_sup_right (XiP_le p L₀) T
  have hcore : (L₀ ⊔ T).pCoreIn 2 ≤ (XiP p L₀ ⊔ T).pCoreIn 2 :=
    (le_inf (hcoreT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hjoin)
  exact fun he => hL.2.2 (bot_unique (he ▸ hcore))

end CFSG.Quasithin.Chapter1
