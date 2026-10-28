module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.Quasithin.Rank

/-!
# Local-family hypotheses in the fixed-line centralizer

The fixed line Z₁ has order two and is centralized by I = LS. Its
centralizer therefore has nontrivial two-core, contains Y₊S, and is outside M.
The genuine preliminary 15.3.11(1) makes S Sylow there. Relative normality
of L in I promotes its Thompson C-component property to the exact local
family used by 1.2.4. The standing simple-QTKE hypothesis supplies SQTK,
including in the quotient by the two-core, so the universal A.3.12
containment theorem lifts L to a unique C-component of C_G(Z₁).

The larger-component exclusions are not asserted here. They require the
marked diagram action and the actual A.3.12 model alternatives.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(3), printed p.1133; 1.2.4, p.505; A.3.12, pp.47–48.
-/

public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

universe u
variable {G : Type u} [Group G]

/-- The definition of the fixed plane makes S centralize it. -/
theorem sylow_le_fixedPlane_centralizer (d : LocalData G) :
    d.S ≤ centralizer (d.ZS : Set G) :=
  le_centralizer_iff.mp (show d.ZS ≤ centralizer (d.S : Set G) from inf_le_right)

/-- The fixed-line identity and I = LS place I in the line centralizer. -/
theorem overgroup_le_fixedLine_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁) :
    I ≤ centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) := by
  rw [hI]
  exact sup_le (le_centralizer_iff.mp (hfixed.ge.trans inf_le_right))
    ((sylow_le_fixedPlane_centralizer d).trans (centralizer_le inf_le_left))

/-- The central line of order two lies in the two-core of its centralizer. -/
theorem fixedLine_le_centralizer_core (d : LocalData G)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2) :
    d.ZS ⊓ d.V₁ ≤
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)).pCoreIn 2 := by
  let Z₁ := d.ZS ⊓ d.V₁
  let _ : IsCyclic Z₁ := isCyclic_of_prime_card hcard
  apply le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) hcard)
    Z₁.le_centralizer
  exact Subgroup.centralizer_le_normalizer _

/-- The line centralizer belongs to the genuine outside family H⁺. -/
theorem fixedLine_centralizer_mem_outside (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2) :
    centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) ∈ d.Hplus := by
  have hIC := overgroup_le_fixedLine_centralizer d c hjoin hfixed
  refine ⟨⟨?_, hI.1.2.trans hIC⟩, fun hCM => c.outside ((component_le c).trans (hIC.trans hCM))⟩
  intro hbot
  have hzbot : d.ZS ⊓ d.V₁ = ⊥ :=
    eq_bot_iff.mpr ((fixedLine_le_centralizer_core d hcard).trans hbot.le)
  simp only [hzbot, Subgroup.card_bot] at hcard
  omega

/-- Apply the universal preliminary 15.3.11(1) to the proved outside member. -/
theorem fixedLine_centralizer_sylow (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (h11_1 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J) :
    Chapter1.IsSylowIn 2 d.S (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) :=
  h11_1 _ (fixedLine_centralizer_mem_outside d hI c hjoin hfixed hcard)

/-- The standing simple-QTKE hypothesis supplies the actual SQTK input. -/
theorem fixedLine_centralizer_sqtk [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (d : LocalData G)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2) :
    IsSQTK 𝒦 (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) := by
  let Z₁ := d.ZS ⊓ d.V₁
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : Z₁)).mp hcard
  have hzorder : orderOf (z : G) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, fun he => hz (Subtype.ext he)⟩
    have hp : z ^ Nat.card Z₁ = 1 := pow_card_eq_one'
    rw [hcard] at hp
    exact congrArg Subtype.val hp
  let C := centralizer (Z₁ : Set G)
  let D := centralizer ({(z : G)} : Set G)
  have hCD : C ≤ D := centralizer_le (Set.singleton_subset_iff.mpr z.property)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hCD)).mp
    ((hG.involution_centralizer_sqtk hzorder).subgroup (C.subgroupOf D))

/-- The two-core quotient still satisfies both SQTK clauses. -/
theorem fixedLine_centralizer_quotient_sqtk [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (d : LocalData G)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    IsSQTK 𝒦 (C ⧸ pCore 2 C) := by
  have hC := fixedLine_centralizer_sqtk hG d hcard
  exact ⟨odd_primeRank_le_two_quotient hC.stronglyQuasithin _ (by
    intro p hp ho
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n), hC.isKGroup.quotient _⟩

/-- Relative normality promotes the Thompson C-component to a C-component of I. -/
theorem component_isCComponent_in_overgroup (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal) :
    (c.L.subgroupOf I).IsCComponent := by
  have htop : (⊤ : Subgroup c.L).IsCComponent := by
    simpa only [subgroupOf_self] using
      c.component.subgroupOf_of_le (show c.L ≤ c.L from le_rfl) c.le_thompson
  have htop' := htop.map_equiv (subgroupOfEquivOfLe (component_le c)).symm
  rw [map_top_of_surjective _ (subgroupOfEquivOfLe (component_le c)).symm.surjective] at htop'
  simpa only [← MonoidHom.range_eq_map, range_subtype] using
    Subgroup.IsCComponent.map_subtype hnormal.isSubnormal htop'

/-- All three conditions of the Chapter 1 local family hold in the line centralizer. -/
theorem component_mem_fixedLine_local_family (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (hnormal : (c.L.subgroupOf I).Normal) (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (h11_1 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J) :
    c.L ∈ Chapter1.LIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) d.S := by
  refine ⟨(component_le c).trans (overgroup_le_fixedLine_centralizer d c hjoin hfixed), ?_⟩
  change (c.L.subgroupOf (c.L ⊔ d.S)).IsCComponent ∧
    Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) ∧ (c.L ⊔ d.S).pCoreIn 2 ≠ ⊥
  rw [← hjoin]
  exact ⟨component_isCComponent_in_overgroup d c hnormal, h11_1 I hI, hI.1.1⟩

/-- The containment part of 1.2.4 in the actual line centralizer. Only the
universal earlier classification statement remains an input. -/
theorem existsUnique_component_over_fixedLine [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (h11_1 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J) :
    ∃! K : Subgroup G, K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) ∧ c.L ≤ K := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  have hIC : I ≤ C := overgroup_le_fixedLine_centralizer d c hjoin hfixed
  have hLC : c.L ≤ C := (component_le c).trans hIC
  obtain ⟨P, hP⟩ := fixedLine_centralizer_sylow d hI c hjoin hfixed hcard h11_1
  have hSC : d.S ≤ C := hP ▸ map_subtype_le (P : Subgroup C)
  have hPeq : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hP
  apply (Chapter1.existsUnique_cComponentsIn_iff hLC).mp
  apply Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12 hA312
    (fixedLine_centralizer_quotient_sqtk hG d hcard) P
  rw [hPeq]
  exact (Chapter1.mem_LIn_iff_subgroupOf hSC hLC).mp
    (component_mem_fixedLine_local_family d hI c hnormal hjoin hfixed h11_1)

/-- Dedekind decomposition in the fixed-plane centralizer, using relative normality. -/
theorem fixedPlane_centralizer_decomposition (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S) :
    I ⊓ centralizer (d.ZS : Set G) = (c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S := by
  have hSI : d.S ≤ I := hjoin ▸ le_sup_right
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    hSI.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal)
  have hSC := sylow_le_fixedPlane_centralizer d
  apply le_antisymm
  · rintro x ⟨hxI, hxC⟩
    have hxprod : x ∈ (c.L : Set G) * (d.S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left c.L d.S hSL]
      rwa [← hjoin]
    obtain ⟨l, hl, s, hs, rfl⟩ := hxprod
    have hlC : l ∈ centralizer (d.ZS : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer (d.ZS : Set G)).mul_mem hxC
          ((centralizer (d.ZS : Set G)).inv_mem (hSC hs))
    exact mul_mem_sup ⟨hl, hlC⟩ hs
  · exact sup_le (le_inf (inf_le_left.trans (component_le c)) inf_le_right)
      (le_inf hSI hSC)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
