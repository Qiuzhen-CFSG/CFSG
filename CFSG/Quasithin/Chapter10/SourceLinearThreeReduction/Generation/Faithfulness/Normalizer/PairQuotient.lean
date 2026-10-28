module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalGeometry
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank

/-!
# The literal product quotient of a nonnormal component orbit

The original two conjugate C-components have simple two-core quotients.
Their product identifies L₀/O₂(L₀) with two copies of L/O₂(L), preserving
the quotient maps on L and on its chosen conjugate. The odd actor's fixed
perfect residual covers this quotient, so its odd ranks retain both factors.
This supplies the ranks used by the nonnormal 4.4.12 local exclusions.

Source: Aschbacher--Smith 10.1.1 and 4.4.5, 4.4.10--12, printed
pp.741,620--622. The construction extends the checked marked A₅ product
argument without an A₅ identification.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The product map preserves the literal quotient and the chosen conjugation. -/
theorem source_nonnormal_original_product_quotient (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∃ q : localOrbit T L →* (L ⧸ pCore 2 L) × (L ⧸ pCore 2 L),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ =
        (QuotientGroup.mk' _ l,1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) =
        (1,QuotientGroup.mk' _ l)) := by
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut R := ((MulAut.conj t).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  let := D.quasisimple
  let Q := L ⧸ pCore 2 L
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : IsSimpleGroup Q := ((QuotientGroup.quotientMulEquivOfEq
    (source_nonnormal_component_core_center D hn)).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨q,hq,hk,hfirst,hsecond⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  refine ⟨q,hq,hk,?_,?_⟩
  · intro l
    exact hfirst (a.symm l)
  · intro l
    have hh := hsecond (b (a.symm l))
    change q (originalConjugateOrbitInclusion ht l) =
      (1,eA (QuotientGroup.mk' _ (b.symm (b (a.symm l))))) at hh
    rw [b.symm_apply_apply] at hh
    exact hh

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
include D hn

/-- The full original orbit quotient, with neither factor replaced by a family tag. -/
theorem source_nonnormal_orbit_product_equiv :
    Nonempty ((localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
      ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L))) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_,_⟩ := source_nonnormal_original_product_quotient D hn ht htn
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩

/-- The fixed residual has the same literal two-factor quotient as L₀. -/
theorem source_nonnormal_oddActorResidual_product_equiv
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L))) := by
  obtain ⟨a,_⟩ := source_oddActorResidual_orbit_quotient_equiv D B hBC hodd
  obtain ⟨b⟩ := source_nonnormal_orbit_product_equiv D hn
  exact ⟨a.trans b⟩

/-- Every odd prime rank of the fixed residual is the sum of the original two ranks. -/
theorem source_nonnormal_oddActorResidual_primeRank
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    primeRank p F = 2 * primeRank p (L ⧸ pCore 2 L) := by
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  obtain ⟨a⟩ := source_nonnormal_oddActorResidual_product_equiv D hn B hBC hodd
  change primeRank p F = 2 * primeRank p (L ⧸ pCore 2 L)
  rw [←primeRank_quotient_eq_of_isTwoGroup p hp (pCore 2 F) pCore_isPGroup,
    primeRank_congr p a,primeRank_prod_eq_add,two_mul]

/-- In particular each odd divisor of the original component order has rank at least two. -/
theorem source_nonnormal_oddActorResidual_primeRank_ge_two
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    2 ≤ primeRank p F := by
  dsimp only
  rw [source_nonnormal_oddActorResidual_primeRank D hn B hBC hodd hp]
  have hr : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
    fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  omega

omit hn in
/-- A nontrivial perfect component quotient supplies an odd prime divisor. -/
theorem source_component_quotient_has_odd_prime :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (L ⧸ pCore 2 L) := by
  let Q := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have hnot : ¬ IsPGroup 2 Q := fun h => Group.IsPerfect.not_isNilpotent Q h.isNilpotent
  have hsub : ¬ (Nat.card Q).primeFactors ⊆ (2 : ℕ).primeFactors := by
    simpa only [←isPGroup_iff_primeFactors_card_subset (G := Q) (by decide : 2 ≠ 0)] using hnot
  obtain ⟨p,hpd,hp2⟩ := Finset.not_subset.mp hsub
  obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hpd
  have hne : p ≠ 2 := by
    intro he
    subst p
    exact hp2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩)
  exact ⟨p,hp,hp.odd_of_ne_two hne,hd⟩

end CFSG.Quasithin.Chapter10
