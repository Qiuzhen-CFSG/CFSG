module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.SmallBound
public import Theory.GroupTheory.SylowNormalSupplementProduct
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# Normal-subgroup and component reductions for F.6.17

The original normal subgroup containing just one local residual supplements
the other vertex. Its product with the other two-core is normal and has that
literal two-core as a Sylow subgroup. This proves F.6.13(1) independently of
the recognition argument in clause (2).

If the first vertex fails characteristic two, its residual is genuinely cubic.
The Frattini argument makes the opposite core elementary; the proved coset
bound and its index two in T give order at most eight and rank at most three.
For a normal component containing both residuals, the layer and two-residual
are that component; a trivial three-complement core also identifies F*.

Source: Aschbacher--Smith F.6.13 and F.6.17, printed pp.307,309,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The exact Sylow intersection supplied by F.6.7 when the second residual escapes. -/
theorem sylow_in_normal_eq_right_core_intersection
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    ∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype =
      (pCore 2 G₂).map G₂.subtype ⊓ X := by
  have hc := (h.right_subnormal_core_iff_not_residual_le X
    (Normal.isSubnormal inferInstance)).mpr h₂
  obtain ⟨_, he, S, hS⟩ := (h.symm.left_subnormal_intersection_iff X
    (Normal.isSubnormal inferInstance)).mp hc
  refine ⟨S, ?_⟩
  rw [hS, subgroupOf_map_subtype]
  exact he.symm

/-- F.6.13(1), retaining the original normal subgroup and literal core. -/
theorem normal_subgroup_rigidity_setup
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    X ⊔ G₂ = ⊤ ∧ (X ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).Normal ∧
      ∃ S : Sylow 2 (X ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G),
        (S : Subgroup (X ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G)).map
          (X ⊔ (pCore 2 G₂).map G₂.subtype : Subgroup G).subtype =
          (pCore 2 G₂).map G₂.subtype := by
  let Q := (pCore 2 G₂).map G₂.subtype
  have hgen : X ⊔ G₂ = ⊤ := top_unique (h.left_residual_sup_right ▸ sup_le_sup_right h₁ G₂)
  refine ⟨hgen, ?_, ?_⟩
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (le_sup_left.trans (X ⊔ Q).le_normalizer)
      ((le_inf le_normalizer_of_normal h.symm.left_core_normalized).trans
        (normalizer_inf_normalizer_le_normalizer_sup X Q))
  · obtain ⟨P, hP⟩ := sylow_in_normal_eq_right_core_intersection h X h₂
    let S : Sylow 2 Q := Classical.choice inferInstance
    apply IsPGroup.exists_sylow_sup_of_normal_sylow_images X Q Q
      (pCore_isPGroup.map G₂.subtype) le_sup_right P S
    · exact hP.le.trans inf_le_left
    · exact map_subtype_le _

/-- The exceptional first vertex supplies the actual cubic equivalence. -/
theorem left_residual_cubic_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) := by
  have hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 :=
    (Nat.card_congr (equivMapOfInjective (pResidual 2 G₁)
      G₁.subtype G₁.subtype_injective).symm.toEquiv).trans (h.local_residual_order_three hbad)
  exact ⟨mulEquivOfPrimeCardEq hc (by simp)⟩

/-- In the exceptional-left branch the original opposite core is elementary of rank at most three. -/
theorem right_core_small_elementary_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      Nat.card ((pCore 2 G₂).map G₂.subtype) ≤ 8 ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 := by
  let Q := (pCore 2 G₂).map G₂.subtype
  let T := G₁ ⊓ G₂
  have hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 :=
    (Nat.card_congr (equivMapOfInjective (pResidual 2 G₁)
      G₁.subtype G₁.subtype_injective).symm.toEquiv).trans (h.local_residual_order_three hbad)
  refine ⟨right_core_elementary_of_left_residual_card_three h hcore hc, ?_⟩
  have hQT : Q ≤ T := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hi : (Q.subgroupOf T).index = 2 := by
    change ((pCore 2 G₂).map G₂.subtype).relIndex (G₁ ⊓ G₂) = 2
    simpa only [inf_comm G₂ G₁] using h.symm.left_core_index
  have hcard := (Q.subgroupOf T).index_mul_card
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv] at hcard
  have hT := h.intersection_card_le_sixteen_of_not_characteristic_two hcore hbad
  have hQ : Nat.card Q ≤ 8 := by change Nat.card T ≤ 16 at hT; omega
  refine ⟨hQ, ?_⟩
  apply (primeRank_le_iff_elementary_card_le Q).mpr
  intro E _
  exact (card_le_card_group E).trans hQ

/-- A normal quasisimple component containing both local residuals is the
actual layer and two-residual. With O₃′(G)=1 it is also F*(G), as in F.6.17(1). -/
theorem quasisimple_residual_of_both_local_containments
    (h : IsGoldschmidtTriple G₁ G₂) (hprime : pPrimeCore 3 G = ⊥)
    (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (h₂ : (pResidual 2 G₂).map G₂.subtype ≤ K) :
    pResidual 2 G = K ∧ generalizedFitting G = K ∧ IsQuasisimple (pResidual 2 G) := by
  have hL : pResidual 2 G ≤ K := h.twoResidual_eq_sup ▸ sup_le h₁ h₂
  have hq : IsPGroup 2 (G ⧸ K) := by
    let f := QuotientGroup.map (pResidual 2 G) K (MonoidHom.id G) hL
    have hf : Function.Surjective f := QuotientGroup.map_surjective_of_surjective
      (pResidual 2 G) K (MonoidHom.id G) (QuotientGroup.mk'_surjective K) hL
    exact (isPGroup_quotient_pResidual 2).of_surjective f hf
  obtain ⟨hE, hR, _⟩ := SimpleSocle.layer_residuals K hq
  have hF : fittingSubgroup G ≤ K := by
    rw [Fitting_eq_pcore G 3 hprime, ← hR]
    exact Noncyclic.threeCore_le_twoResidual
  have hFG : generalizedFitting G = K := by
    rw [generalizedFitting, hE, sup_eq_right.mpr hF]
  exact ⟨hR, hFG, hR.symm ▸ inferInstance⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
