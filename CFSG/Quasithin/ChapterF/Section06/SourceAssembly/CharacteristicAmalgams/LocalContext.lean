module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Stellmacher.SectionEight.GeneratedContext
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PCoreSurjective

/-!
# Local graph hypotheses for characteristic-two Goldschmidt vertices

A genuine Goldschmidt triple with both vertices of characteristic two gives
the local hypotheses of Stellmacher Section Seven. The common Sylow has
prime index three in each vertex, so it is the unique maximal overgroup
of itself. Each local two-core is nontrivial and self-centralizing.
The actual S₃ quotients also supply the two quotient facts in the local
Section Eight context; their Frattini subgroups are trivial.

Source: Aschbacher–Smith F.6.1–F.6.4 and Stellmacher, Journal of Algebra
190 (1997), Section 7 and (6.3). No ambient Hypothesis Two is imposed.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher Stellmacher.SectionsFiveToSeven Stellmacher.Later
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem coatom_of_index_three {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (hi : K.index = 3) : IsCoatom K := by
  refine ⟨?_, ?_⟩
  · intro ht
    rw [ht, index_top] at hi
    omega
  · intro M hKM
    have hd := index_dvd_of_le hKM.le
    rw [hi] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact index_eq_one.mp h1
    · have hh := index_strictAnti hKM
      omega

private theorem core_nontrivial (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting G₁ = pCore 2 G₁) :
    (pCore 2 G₁).map G₁.subtype ≠ ⊥ := by
  intro hh
  have hc : pCore 2 G₁ = ⊥ := (map_eq_bot_iff_of_injective _ G₁.subtype_injective).mp hh
  have hcent := h.local_core_selfCentralizing hgood
  rw [hc] at hcent
  have ht : (⊤ : Subgroup G₁) = ⊥ := le_bot_iff.mp (by
    intro x _
    apply hcent
    intro y hy
    have hyone : y = 1 := hy
    simp [hyone])
  have hcard := congrArg (fun K : Subgroup G₁ => Nat.card K) ht
  rw [card_top, card_bot] at hcard
  have horder := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  rw [hc, card_bot, hcard] at horder
  norm_num at horder

private theorem local_PFamily (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting G₁ = pCore 2 G₁) :
    G₁ ∈ PFamily ⊤ (G₁ ⊓ G₂) := by
  obtain ⟨T,hT⟩ := h.intersection_sylow
  have hTG : (T : Subgroup G) ≤ G₁ := hT.symm.le.trans inf_le_left
  let P := T.subtype hTG
  have hPS : (P : Subgroup G₁).map G₁.subtype = G₁ ⊓ G₂ := by
    change ((T : Subgroup G).subgroupOf G₁).map G₁.subtype = _
    rw [map_subgroupOf_eq_of_le hTG, hT]
  have hPco : IsCoatom (P : Subgroup G₁) :=
    coatom_of_index_three _ (SymmetricThreeTwoCore.sylow_index_three h.quotient_left.some P)
  have hPSnative : (G₁ ⊓ G₂).subgroupOf G₁ = (P : Subgroup G₁) := by
    change (G₁ ⊓ G₂).subgroupOf G₁ = (T : Subgroup G).subgroupOf G₁
    rw [hT]
  refine ⟨⟨le_top, ⟨inf_le_left,P,hPS⟩, core_nontrivial h hgood, ?_⟩,
    inf_le_left, (P : Subgroup G₁), hPco, hPSnative.le, ?_⟩
  · intro he
    have hi := h.left_core_index
    change (twoCoreIn G₁).relIndex (G₁ ⊓ G₂) = 2 at hi
    rw [he, relIndex_self] at hi
    norm_num at hi
  · intro M hM hSM
    exact (hPco.le_iff_eq hM.1).mp (hPSnative ▸ hSM)

/-- The genuine local hypotheses needed for the coset graph argument. -/
theorem IsGoldschmidtTriple.sectionSeven_of_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂) :
    SectionSevenHypotheses G (G₁ ⊓ G₂) G₁ G₂ := by
  refine ⟨?_, local_PFamily h hgood₁, ?_, h.generated,
    h.local_solvable, h.symm.local_solvable,
    h.local_core_selfCentralizing hgood₁, h.symm.local_core_selfCentralizing hgood₂, hcore⟩
  · intro hT
    exact core_nontrivial h hgood₁
      (le_bot_iff.mp (hT ▸ h.local_twoCore_le_intersection))
  · simpa only [inf_comm G₂ G₁] using local_PFamily h.symm hgood₂

private theorem nativeSL2_of_perm_three {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    IsSL2Two ((H ⧸ pCore 2 H) ⧸ frattini (H ⧸ pCore 2 H)) := by
  let X := H ⧸ pCore 2 H
  let P : Sylow 2 X := default
  have hX : Nat.card X = 6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hX]
    decide +kernel
  have hi : (P : Subgroup X).index = 3 := by
    have hh := (P : Subgroup X).card_mul_index
    rw [hP, hX] at hh
    omega
  have hPhi : frattini X ≤ (P : Subgroup X) := frattini_le_coatom (coatom_of_index_three _ hi)
  have hPhiP : IsPGroup 2 (frattini X) := P.isPGroup'.of_injective
    (inclusion hPhi) (inclusion_injective hPhi)
  have hXcore : pCore 2 X = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hq := QuotientGroup.mk'_surjective (pCore 2 H)
    have hk : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have he := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
    rw [map_comap_eq_self_of_surjective hq] at he
    exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hPhibot : frattini X = ⊥ := by
    apply le_bot_iff.mp
    rw [← hXcore]
    exact le_sSup ⟨inferInstance, hPhiP⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hPhibot).trans
    (QuotientGroup.quotientBot.trans (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm))⟩

/-- Both local quotient facts are proved from the literal S₃ quotient maps. -/
theorem IsGoldschmidtTriple.sixThree_local (h : IsGoldschmidtTriple G₁ G₂) :
    SixThreeLocalData (G₁ ⊓ G₂) G₁ G₂ := by
  constructor
  · intro _
    constructor
    · exact ⟨1, ⟨h.quotient_left.some.trans nonempty_dihedralThreeEquivPerm.some.symm⟩⟩
    · exact ⟨1, ⟨h.quotient_right.some.trans nonempty_dihedralThreeEquivPerm.some.symm⟩⟩
  · intro _
    exact ⟨nativeSL2_of_perm_three h.quotient_left.some,
      nativeSL2_of_perm_three h.quotient_right.some⟩

end CFSG.Quasithin.ChapterF
