module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.NormalComplements

/-!
# The order-two centralizer factor in the Suzuki argument

The embedded Suzuki subgroup restrictions discharge every model premise of
Lemma 14.7(a). If |U| > 2, they supply a nontrivial odd complement Y in J,
and the invariant elementary complement A of T in S has order q.

For E = M°A, the earlier involution-fusion statement sends a nonidentity
element of A to an involution w in D and hence in J. Normalizer control on
⟨w⟩ puts the conjugate of E inside N_G(L), where Sylow conjugacy puts it
inside T. Since z belongs to E, product disconnection forces the resulting
conjugator into M. Elementary abelianness and the bound |U| ≤ q then give
E conjugate to M°U. Solvable Hall conjugacy corrects this conjugator and
forces E = M°U, contradicting the complement property.

This reconstructs the omitted conjugator explanation at the extracted end
of GLS4, Chapter 2, Lemma 14.8. The only extra earlier-source premise is the
specified Lemma 12.11 fusion statement; its producer remains with the
parent source assembly. Source: `refs/KGroup/GLS4/Chapter2.tex`,
Lemmas 14.7–14.8, approximately lines 2570–2600.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup PFAppendixIII Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

private theorem elementary_conjugate_into_T
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (h12 : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hzE : z ∈ E)
    {a : G} (haE : a ∈ E) (ha1 : a ≠ 1) (haZ : a ∉ Z) :
    ∃ x ∈ M, E.conjBy x ≤ g.T := by
  have ha : PFAppendixIII.IsInvolution a := ⟨ha1, elemPow_eq_one_of_isElementaryAbelian a haE⟩
  obtain ⟨w, hwD, haw⟩ := h12 a ha haZ
  obtain ⟨b, hb⟩ := isConj_iff.mp haw
  change MulAut.conj b a = w at hb
  have hw : PFAppendixIII.IsInvolution w := by
    constructor
    · intro hw1
      exact ha.ne_one ((MulAut.conj b).injective
        (hb.trans (hw1.trans (map_one (MulAut.conj b)).symm)))
    · rw [← hb, ← map_pow, ha.sq_eq_one, map_one]
  have hwJ := d.involution_mem_centralizer hwD hw
  have hcyc : zpowers w ≠ ⊥ := by
    intro he
    exact hw.ne_one (mem_bot.mp (he ▸ mem_zpowers w))
  have hCN : centralizer ({w} : Set G) ≤
      normalizer (residualGenerated M z t : Set G) := by
    have hh := (Subgroup.centralizer_le_normalizer (zpowers w : Set G)).trans
      (g.normalizer_control _ (zpowers_le.mpr hwJ) hcyc)
    rwa [zpowers_eq_closure, centralizer_closure] at hh
  let N := normalizer (residualGenerated M z t : Set G)
  have hEN : E.conjBy b ≤ N := by
    rintro x ⟨v, hv, rfl⟩
    apply hCN
    apply mem_centralizer_singleton_iff.mpr
    have hc : Commute v a := congrArg E.subtype
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative E) ⟨v, hv⟩ ⟨a, haE⟩)
    simpa only [MulEquiv.coe_toMonoidHom, hb] using (hc.map (MulAut.conj b).toMonoidHom).eq
  have hEp : IsPGroup 2 ((E.conjBy b).subgroupOf N) :=
    ((IsElementaryAbelian.isPGroup 2 E).map (MulAut.conj b).toMonoidHom).comap_subtype
  obtain ⟨V, hV⟩ := g.T_sylow
  obtain ⟨R, hR⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N R V
  have hmap : ((E.conjBy b).subgroupOf N).map (MulAut.conj c).toMonoidHom ≤
      (V : Subgroup N) := by
    rw [← hc]
    exact map_mono hR
  have hET : E.conjBy ((c : G) * b) ≤ g.T := by
    have hh := map_mono (f := N.subtype) hmap
    rw [map_subgroupOf_map_conj_eq hEN, hV] at hh
    rw [conjBy_mul]
    exact hh
  refine ⟨(c : G) * b, ?_, hET⟩
  apply (d.minimal.disconnected.conjugate_mem_iff z d.z_mem d.z_mem_M _).mp
  exact g.S_le_M (g.T_lt_S.le (hET (mem_map_of_mem _ hzE)))

private theorem complement_card
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    {A : Subgroup G} (hdis : Disjoint g.T A)
    (hprod : (g.S : Set G) = (g.T : Set G) * (A : Set G)) :
    Nat.card A = 2 ^ (2 * m + 1) := by
  have hc := card_set_mul_mul_card_inf g.T A
  rw [← hprod, hdis.eq_bot, card_bot, mul_one] at hc
  change Nat.card g.S = Nat.card g.T * Nat.card A at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := g.T))
  rw [← hc, d.card_S g s, g.card_T]
  ring

private theorem central_product_card {H A : Subgroup G}
    (hc : A ≤ centralizer (H : Set G)) (hd : Disjoint H A) :
    Nat.card (H ⊔ A : Subgroup G) = Nat.card H * Nat.card A := by
  have he := card_set_mul_mul_card_inf H A
  rw [← coe_mul_of_right_le_normalizer_left H A
    (hc.trans (Subgroup.centralizer_le_normalizer _)), hd.eq_bot, card_bot, mul_one] at he
  exact he

/-- GLS4, Chapter 2, Lemma 14.7(a). The embedded Suzuki subgroup supplies
all cyclicity, order and fixed-point restrictions on the odd complement. -/
public theorem Context.invariantElementaryComplement_of_normal_complement
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hYodd : Odd (Nat.card Y))
    (hJ : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G))
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    InvariantElementaryComplement g Y := by
  obtain ⟨hcyc, hdvd, hfree⟩ := d.normal_complement_restrictions g f hf hU Y hYJ hYne hYodd hJ
  exact d.invariantElementaryComplement g hsemi f hf s Y hYJ hYne hYodd hJ hU
    hcyc hdvd hfree

/-- GLS4, Chapter 2, Lemma 14.8, with only the specified earlier-source
involution-fusion premise in addition to the local and Sylow geometry. -/
public theorem Context.U_card_eq_two
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (h12 : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w) : Nat.card g.U = 2 := by
  have hlow := d.two_le_U_card g
  by_contra hne
  have hlarge : 2 < Nat.card g.U := by omega
  have hUn := d.U_normal_centralizer_of_two_lt_card g f hf hlarge
  obtain ⟨Y, hYJ, hYne, hYodd, hJprod⟩ := s.exists_nontrivial_odd_complement g
  obtain ⟨A, hAS, hAe, hdis, hprod, hnorm⟩ :=
    d.invariantElementaryComplement_of_normal_complement g hsemi f hf s Y hYJ hYne hYodd
      hJprod hUn
  let A0 := closure (Z ∩ (M : Set G))
  let E := A0 ⊔ A
  let F := A0 ⊔ g.U
  let := hAe
  let : IsElementaryAbelian 2 A0 := (d.closure_elementary_card g).1
  have hAC : A ≤ centralizer (A0 : Set G) := hAS.trans (s.S_le_closure_centralizer g)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hA0T : A0 ≤ g.T := g.closure_le_P.trans (by rw [g.P_eq]; exact inf_le_left)
  have hEcard : Nat.card E = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [central_product_card hAC (hdis.mono_left hA0T),
      (d.closure_elementary_card g).2, complement_card d g s hdis hprod, pow_two]
  have hFcard : Nat.card F = 2 ^ (2 * m + 1) * Nat.card g.U := by
    rw [central_product_card g.U_le_closure_centralizer g.closure_disjoint_U,
      (d.closure_elementary_card g).2]
  have hAne : A ≠ ⊥ := by
    intro he
    apply g.T_lt_S.not_ge
    intro x hx
    obtain ⟨v, hv, a, ha, rfl⟩ := (Set.ext_iff.mp hprod x).mp hx
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    change v * a ∈ g.T
    rw [ha1, mul_one]
    exact hv
  obtain ⟨a, ha1⟩ := ne_bot_iff_exists_ne_one.mp hAne
  have ha1' : (a : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have haZ : (a : G) ∉ Z := by
    intro haZ
    have haT := hA0T (subset_closure ⟨haZ, g.S_le_M (hAS a.property)⟩)
    exact ha1' (mem_bot.mp (hdis.eq_bot ▸ (show (a : G) ∈ g.T ⊓ A from ⟨haT, a.property⟩)))
  obtain ⟨x, hxM, hET⟩ := elementary_conjugate_into_T d g h12 E
    (mem_sup_left (subset_closure ⟨d.z_mem, d.z_mem_M⟩))
    (mem_sup_right a.property) ha1' haZ
  have hEFle : E.conjBy x ≤ F := by
    rintro v ⟨v, hv, rfl⟩
    apply g.square_one_mem_closure_sup_U (hET (mem_map_of_mem _ hv))
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian v hv, map_one]
  have hEF : E.conjBy x = F := by
    apply eq_of_le_of_card_ge hEFle
    change Nat.card F ≤ Nat.card (E.map (MulAut.conj x).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj x).injective, hEcard, hFcard, pow_two]
    exact Nat.mul_le_mul_left _ (d.U_card_le g f hf)
  have hYE : Y ≤ normalizer (E : Set G) := by
    apply (le_inf ?_ (le_sup_right.trans hnorm)).trans
      (normalizer_inf_normalizer_le_normalizer_sup A0 A)
    exact (hYJ.trans (centralizer_le d.distinguished_le_residual)).trans
      (Subgroup.centralizer_le_normalizer _)
  have heq : E = F := complement_conjugate_eq_of_normal_complement d g s hUn
    E Y hYJ hYne hYodd hJprod hYE x hxM hEF
  have hAT : A ≤ g.T :=
    (show A ≤ E from le_sup_right).trans (heq ▸ sup_le hA0T g.U_le_T)
  apply g.T_lt_S.not_ge
  intro v hv
  obtain ⟨w, hw, a, ha, rfl⟩ := (Set.ext_iff.mp hprod v).mp hv
  exact g.T.mul_mem hw (hAT ha)

end BenderSuzuki.ZD.SuzukiExclusion
