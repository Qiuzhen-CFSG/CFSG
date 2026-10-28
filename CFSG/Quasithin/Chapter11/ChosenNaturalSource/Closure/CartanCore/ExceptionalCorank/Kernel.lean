module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.LocalClosure
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.ElementaryAbelian.RankOneImageCriterion
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The kernel step in the exceptional elementary-corank argument

For the literal outside subgroup H₁, O²(H₁) ≤ K forces L₁ < K by the
residual--Sylow supplement. The kernel C = C_R₁(K/O₂(K)) is normalized
by T. Its commutator with O²(H₁) lies in H₁ ∩ O₂(K), a normal two-subgroup
of H₁. Thus C O₂(H₁) is a normal two-subgroup of H₁ and C ≤ O₂(H₁).
This uses only relative normality of K, and does not assume its quotient
centerless; in particular it preserves the odd-kernel extension cases.

The final lemma transfers a rank bound for an elementary subgroup's actual
action image to the original subgroup corank. Constructing that rank bound
in both exceptional models remains separate; this is not full 11.5.6(6).
Source: Aschbacher--Smith, 11.5.6(6), printed pp.780--781 (PDF pp.797--798).
-/

@[expose] public noncomputable section

open Subgroup
open scoped commutatorElement

private theorem normalized_two_subgroup_le_core {J : Type*} [Group J] [Finite J]
    (S : Sylow 2 J) (C : Subgroup J) (hC : IsPGroup 2 C)
    (hn : (S : Subgroup J) ≤ normalizer (C : Set J))
    (hc : ⁅C, pResidual 2 J⁆ ≤ pCore 2 J) : C ≤ pCore 2 J := by
  let B := C ⊔ pCore 2 J
  have hB : IsPGroup 2 B := hC.to_sup_of_normal_right pCore_isPGroup
  have hnB : normalizer (B : Set J) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    refine sup_le ?_ ?_
    · exact le_normalizer_sup_of_commutator_le C (pResidual 2 J) C (pCore 2 J) le_rfl hc
    · exact (le_inf hn le_normalizer_of_normal).trans
        (normalizer_inf_normalizer_le_normalizer_sup C (pCore 2 J))
  let : B.Normal := normalizer_eq_top_iff.mp hnB
  exact le_sup_left.trans (le_sSup ⟨inferInstance, hB⟩)

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The outside condition rules out K = L₁ using O²(H₁), not O₂(H₁). -/
theorem local_lt_closure_of_residual_le (H : Subgroup G)
    (hH : H ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
      (E.M : Set G))
    (hr : (pResidual 2 H).map H.subtype ≤ E.K) : E.L₁ < E.K := by
  apply lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁)
  intro he
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hgen := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hgen
  apply hH.2
  rw [← hgen]
  exact sup_le ((hr.trans_eq he.symm).trans (E.L₁_le.trans L.le_normalizer))
    D.sylow_normalizes_component

/-- The literal R₁ action kernel is contained in the intrinsic core of H₁. -/
theorem quotientCentralizer_le_localCore (hT : (T : Subgroup G) ≤ E.G₁) (H : Subgroup G)
    (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K) :
    E.R₁ ⊓ coreQuotientCentralizer E.K ≤ H.pCoreIn 2 := by
  let C := E.R₁ ⊓ coreQuotientCentralizer E.K
  have hCH : C ≤ H := inf_le_left.trans ((pCoreIn_le 2 _).trans hLH)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hLH
  have hNR : (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
    ((le_sup_right : (T : Subgroup G) ≤ E.L₁ ⊔ (T : Subgroup G)).trans
      (E.L₁ ⊔ (T : Subgroup G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hNC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf hNR ((hT.trans E.G₁_normalizes_K).trans
      (normalizer_normalizes_coreQuotientCentralizer E.K))).trans
        inf_normalizer_le_normalizer_inf
  have hBC : H ⊓ E.K.pCoreIn 2 ≤ H.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 E.K).to_le inf_le_right) inf_le_left
    exact (le_inf H.le_normalizer ((hHG.trans E.G₁_normalizes_K).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans
        inf_normalizer_le_normalizer_inf
  have hcn : (T.subtype hTH : Subgroup H) ≤ normalizer (C.subgroupOf H : Set H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hNC ht) x
  have hcomm : ⁅C.subgroupOf H, pResidual 2 H⁆ ≤ pCore 2 H := by
    apply commutator_le.mpr
    intro c hc r hr'
    have hh : (⁅c, r⁆ : H).val ∈ H.pCoreIn 2 := by
      apply hBC
      refine ⟨(⁅c, r⁆ : H).property, ?_⟩
      exact coreQuotientCentralizer_commutator hc.2 (hr (mem_map_of_mem _ hr'))
    obtain ⟨x, hx, he⟩ := hh
    exact (Subtype.ext he : x = ⁅c,r⁆) ▸ hx
  have hle := normalized_two_subgroup_le_core (T.subtype hTH) (C.subgroupOf H)
    ((isPGroup_pCoreIn 2 _).to_le inf_le_left).comap_subtype hcn hcomm
  have hm := map_mono (f := H.subtype) hle
  rwa [map_subgroupOf_eq_of_le hCH] at hm


/-- Restriction of the actual normalizer action to the source radical R₁. -/
def radicalCoreAction (hT : (T : Subgroup G) ≤ E.G₁) :
    E.R₁ →* MulAut (E.K ⧸ pCore 2 E.K) :=
  (coreQuotientAction E.K).comp (inclusion
    (((pCoreIn_le 2 _).trans (sup_le E.L₁_le_G₁ hT)).trans E.G₁_normalizes_K))

/-- The embedded kernel is precisely the source quotient centralizer in R₁. -/
theorem radicalCoreAction_kernel_map (hT : (T : Subgroup G) ≤ E.G₁) :
    (E.radicalCoreAction hT).ker.map E.R₁.subtype =
      E.R₁ ⊓ coreQuotientCentralizer E.K := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨r.property, ⟨_,hr,rfl⟩⟩
  · rintro ⟨hx, g,hg,hgx⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change coreQuotientAction E.K _ = 1
    have he : (inclusion
      (((pCoreIn_le 2 _).trans (sup_le E.L₁_le_G₁ hT)).trans E.G₁_normalizes_K)
      (⟨x,hx⟩ : E.R₁)) = g := Subtype.ext hgx.symm
    exact (congrArg (coreQuotientAction E.K) he).trans hg

/-- Transfer of the elementary action bound; the exceptional model must supply `hi`. -/
theorem elementary_corank_le_one_of_action_rank (hT : (T : Subgroup G) ≤ E.G₁) (H : Subgroup G)
    (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁)
    (hi : Group.rank ((A.subgroupOf E.R₁).map (E.radicalCoreAction hT)) ≤ 1) :
    ChapterE.subgroupCorank A (A ⊓ H.pCoreIn 2) ≤ 1 := by
  let B := A.subgroupOf E.R₁
  let f := E.radicalCoreAction hT
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hA
  have hcard := (IsElementaryAbelian.rank_map_le_one_iff_card_le_twice_kernel B f).mp hi
  have hC : (B ⊓ f.ker).map E.R₁.subtype ≤ A ⊓ H.pCoreIn 2 := by
    apply le_inf
    · exact (map_mono (f := E.R₁.subtype) inf_le_left).trans_eq
        (map_subgroupOf_eq_of_le hA)
    · exact (map_mono (f := E.R₁.subtype) inf_le_right).trans
        ((E.radicalCoreAction_kernel_map hT).le.trans (E.quotientCentralizer_le_localCore hT H hLH hHG hr))
  have hc : Nat.card A ≤ 2 * Nat.card (A ⊓ H.pCoreIn 2 : Subgroup G) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hcard
    have hcmp := card_le_of_le hC
    rw [card_map_of_injective E.R₁.subtype_injective] at hcmp
    omega
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ H.pCoreIn 2) A bot_le inf_le_left
  have hpos : 0 < Nat.card (A ⊓ H.pCoreIn 2 : Subgroup G) := Nat.card_pos
  have hidx : (A ⊓ H.pCoreIn 2).relIndex A ≤ 2 := by
    simp only [relIndex_bot_left] at hprod
    nlinarith
  change Nat.log 2 ((A ⊓ H.pCoreIn 2).relIndex A) ≤ 1
  exact (Nat.log_mono_right hidx).trans (by decide)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
