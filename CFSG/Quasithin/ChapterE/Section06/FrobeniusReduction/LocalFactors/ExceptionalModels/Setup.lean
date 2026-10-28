module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Enlargement
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupAction.NormalizerFixedCentralizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections


/-!
# The two-central involution in the exceptional E.6.25 enlargement

An index-two subspace W of U admits a generator t of U/W. Elementary
abelianity makes t an involution, and V centralizes the common Sylow subgroup
Q. Thus C_G(U) = C_G(W) ∩ C_G(t). Component membership is restricted to this
actual relative centralizer.

Uniqueness in 1.2.4 implies that t normalizes the containing C-component J:
it centralizes L, so conjugation preserves the unique C-component containing
L. The identity C_V(J) = W makes the induced involution nontrivial. Subnormal
Sylow restriction supplies a Sylow subgroup of J fixed pointwise by it.
No model identification or incompatible-rank premise enters this argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
E.6.25, printed p.256 (PDF p.267), and 1.2.4, printed p.505.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
variable {G : Type*} [Group G] {U W : Subgroup G}

private theorem index_two_section (hWU : W ≤ U) (hi : W.relIndex U = 2) :
    ∃ t ∈ U, t ∉ W ∧ W ⊔ zpowers t = U := by
  obtain ⟨t, ht, hnot, hcoset⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hi
  refine ⟨t, ht, hnot, le_antisymm (sup_le hWU (zpowers_le.mpr ht)) ?_⟩
  intro x hx
  rcases hcoset x hx with hxt | hxW
  · have hx' := (W ⊔ zpowers t).mul_mem
      (show x * t ∈ W ⊔ zpowers t from (le_sup_left : W ≤ W ⊔ zpowers t) hxt)
      ((W ⊔ zpowers t).inv_mem ((le_sup_right : zpowers t ≤ W ⊔ zpowers t)
        (mem_zpowers t)))
    simpa only [mul_inv_cancel_right] using hx'
  · exact (le_sup_left : W ≤ W ⊔ zpowers t) hxW

private theorem centralizer_section {t : G} (he : W ⊔ zpowers t = U) :
    centralizer (U : Set G) = centralizer (W : Set G) ⊓ centralizer ({t} : Set G) := by
  apply le_antisymm
  · have hWU : W ≤ U := he ▸ (le_sup_left : W ≤ W ⊔ zpowers t)
    refine le_inf (Subgroup.centralizer_le hWU) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx t
        (he ▸ (le_sup_right : zpowers t ≤ W ⊔ zpowers t) (mem_zpowers t))).symm
  · apply le_centralizer_iff.mpr
    rw [← he]
    refine sup_le (le_centralizer_iff.mp inf_le_left) (zpowers_le.mpr ?_)
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx.2

variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}

/-- Construct the involution representing U/W, retaining its centrality in Q. -/
theorem exists_two_central_section (h : HypothesisE61 K T M V)
    (hUV : U ≤ V) (hWU : W ≤ U) (hi : W.relIndex U = 2) :
    ∃ t ∈ U, t ∉ W ∧ orderOf t = 2 ∧
      t ∈ sylowCentralizer (T : Subgroup G) V ∧
      t ∈ centralizer (sylowCentralizer (T : Subgroup G) V : Set G) ∧
      W ⊔ zpowers t = U ∧
      centralizer (U : Set G) =
        centralizer (W : Set G) ⊓ centralizer ({t} : Set G) := by
  let _ := h.elementary
  obtain ⟨t, ht, hnot, he⟩ := index_two_section hWU hi
  have hne : t ≠ 1 := fun he => hnot (he ▸ W.one_mem)
  have hpow : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t (hUV ht)
  have ho : orderOf t = 2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
    (orderOf_dvd_of_pow_eq_one hpow) |>.resolve_left
      (fun he => hne (orderOf_eq_one_iff.mp he))
  exact ⟨t, ht, hnot, ho, h.le_sylowCentralizer (hUV ht),
    (le_centralizer_iff.mp inf_le_right) (hUV ht), he, centralizer_section he⟩

variable {L J : Subgroup G}

omit [Finite G] in
/-- Ordinary component membership restricts to the actual involution centralizer in J. -/
theorem component_restrict_section {t : G}
    (he : centralizer (U : Set G) =
      centralizer (W : Set G) ⊓ centralizer ({t} : Set G))
    (hL : IsComponentIn L (centralizer (U : Set G)))
    (hLJ : L ≤ J) (hJ : J ≤ centralizer (W : Set G)) :
    IsComponentIn L (J ⊓ centralizer ({t} : Set G)) := by
  apply hL.restrict
  · exact le_inf hLJ (hL.1.trans (he ▸ inf_le_right))
  · rw [he]
    exact inf_le_inf_right _ hJ

omit [Finite G] in
/-- The analogous restriction for the relative C-component family. -/
theorem cComponent_restrict_section {t : G}
    (he : centralizer (U : Set G) =
      centralizer (W : Set G) ⊓ centralizer ({t} : Set G))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hLJ : L ≤ J) (hJ : J ≤ centralizer (W : Set G)) :
    L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)) := by
  have hLC : L ≤ J ⊓ centralizer ({t} : Set G) :=
    le_inf hLJ (hL.1.trans (he ▸ inf_le_right))
  refine ⟨hLC, hL.2.subgroupOf_of_le hLC ?_⟩
  rw [he]
  exact inf_le_inf_right _ hJ

omit [Finite G] in
private theorem unique_cComponent_normalized {B C : Subgroup G}
    (hC : C.IsCComponent) (hBC : B ≤ C)
    (hunique : ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = C)
    {a : G} (ha : a ∈ centralizer (B : Set G)) : a ∈ normalizer (C : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hunique _ (hC.map_equiv (MulAut.conj a))
  intro b hb
  refine ⟨b, hBC hb, ?_⟩
  change a * b * a⁻¹ = b
  rw [← mem_centralizer_iff.mp ha b hb, mul_inv_cancel_right]

omit [Finite G] in
private theorem relative_unique_cComponent_normalized {H : Subgroup G}
    (hBH : L ≤ H) (hJ : J ∈ Chapter1.cComponentsIn H) (hLJ : L ≤ J)
    (hunique : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn H ∧ L ≤ D → D = J) :
    H ⊓ centralizer (L : Set G) ≤ normalizer (J : Set G) := by
  have hex : ∃! D : Subgroup G, D ∈ Chapter1.cComponentsIn H ∧ L ≤ D :=
    ⟨J, ⟨hJ, hLJ⟩, hunique⟩
  obtain ⟨D, hD, huniq⟩ := (Chapter1.existsUnique_cComponentsIn_iff hBH).mpr hex
  have he : J.subgroupOf H = D := huniq _ ⟨hJ.2, comap_mono hLJ⟩
  have hrel : ∀ C : Subgroup H, C.IsCComponent → L.subgroupOf H ≤ C →
      C = J.subgroupOf H := fun C hC hLC => (huniq C ⟨hC, hLC⟩).trans he.symm
  intro a ha
  have hca : (⟨a, ha.1⟩ : H) ∈ centralizer (L.subgroupOf H : Set H) := by
    intro l hl
    exact Subtype.ext (mem_centralizer_iff.mp ha.2 l hl)
  have hn := unique_cComponent_normalized hJ.2 (comap_mono hLJ) hrel hca
  have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hn)
  rw [map_subgroupOf_eq_of_le hJ.1] at hm
  exact hm

/-- Ambient conjugation gives a nontrivial involution fixing a genuine Sylow subgroup. -/
theorem cComponent_sylow_fixed_action {H Q : Subgroup G}
    (hQ : Chapter1.IsSylowIn 2 Q H)
    (hJ : J ∈ Chapter1.cComponentsIn H) {t : G}
    (hn : t ∈ normalizer (J : Set G))
    (htQ : t ∈ centralizer (Q : Set G))
    (ht : orderOf t = 2) (hne : t ∉ centralizer (J : Set G)) :
    ∃ a : MulAut J, orderOf a = 2 ∧
      (∀ x : J, (a x : G) = t * (x : G) * t⁻¹) ∧
      (∃ S : Sylow 2 J, ∀ x ∈ (S : Subgroup J), a x = x) ∧
      a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J := by
  let n : normalizer (J : Set G) := ⟨t, hn⟩
  let a := J.normalizerMonoidHom n
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow]
    have hn2 : n ^ 2 = 1 := Subtype.ext (by
      change t ^ 2 = 1
      rw [← ht]
      exact pow_orderOf_eq_one t)
    rw [hn2, map_one]
  have ha1 : a ≠ 1 := by
    intro he
    apply hne
    have hnker : n ∈ J.normalizerMonoidHom.ker := he
    rwa [normalizerMonoidHom_ker] at hnker
  have hao : orderOf a = 2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
    (orderOf_dvd_of_pow_eq_one ha2) |>.resolve_left
      (fun he => ha1 (orderOf_eq_one_iff.mp he))
  obtain ⟨S, hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hQ hJ.1 hJ.2.subnormal
  refine ⟨a, hao, (fun _ => rfl), ⟨S, ?_⟩, ?_⟩
  · intro x hx
    have hxQ : (x : G) ∈ Q := (hS ▸ mem_map_of_mem J.subtype hx).1
    apply Subtype.ext
    change t * (x : G) * t⁻¹ = (x : G)
    rw [← mem_centralizer_iff.mp htQ x hxQ, mul_inv_cancel_right]
  · ext x
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff]
    rw [← Subtype.coe_inj]
    change t * (x : G) * t⁻¹ = (x : G) ↔ (x : G) * t = t * (x : G)
    rw [mul_inv_eq_iff_eq_mul, eq_comm]

/-- Construct the actual Sylow-central involutory action on the enlarged C-component. -/
theorem exceptional_involution_action (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalContainment K)
    (hU : U ∈ obstructionFamily M V) (hW : W ∈ obstructionFamily M V)
    (hWU : W ≤ U) (hi : W.relIndex U = 2)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (W : Set G)))
    (hLJ : L ≤ J) (hfixed : V ⊓ centralizer (J : Set G) = W) :
    ∃ t ∈ U, t ∉ W ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set G) ∧
      centralizer (U : Set G) =
        centralizer (W : Set G) ⊓ centralizer ({t} : Set G) ∧
      L ∈ Chapter1.cComponentsIn (J ⊓ centralizer ({t} : Set G)) ∧
      ∃ a : MulAut J, orderOf a = 2 ∧
        (∀ x : J, (a x : G) = t * (x : G) * t⁻¹) ∧
        (∃ S : Sylow 2 J, ∀ x ∈ (S : Subgroup J), a x = x) ∧
        a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf J := by
  let _ := h.elementary
  obtain ⟨t, htU, hnot, ht, _, htQ, _, he⟩ :=
    exists_two_central_section h hU.1 hWU hi
  obtain ⟨J₀, hJ₀, huniq⟩ := exists_containing_cComponent h earlier hU hW hWU hL
  have hJJ : J = J₀ := huniq J ⟨hJ, hLJ⟩
  have hn := relative_unique_cComponent_normalized
    (hL.1.trans (Subgroup.centralizer_le hWU)) hJ hLJ
    (fun D hD => (huniq D hD).trans hJJ.symm)
  have htL : t ∈ centralizer (L : Set G) := (le_centralizer_iff.mp hL.1) htU
  have htH : t ∈ centralizer (W : Set G) :=
    (V.le_centralizer.trans (Subgroup.centralizer_le hW.1)) (hU.1 htU)
  have htN := hn ⟨htH, htL⟩
  have htJ : t ∉ centralizer (J : Set G) := fun hc =>
    hnot (hfixed ▸ (show t ∈ V ⊓ centralizer (J : Set G) from ⟨hU.1 htU, hc⟩))
  exact ⟨t, htU, hnot, ht, htN, he,
    cComponent_restrict_section he hL hLJ hJ.1,
    cComponent_sylow_fixed_action (h.sylow_obstruction hW) hJ htN htQ ht htJ⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
