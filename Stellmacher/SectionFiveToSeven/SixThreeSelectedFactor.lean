module
public import Stellmacher.SectionFiveToSeven.SixOneBaumannSylow
public import Stellmacher.SectionFiveToSeven.PFamilyInjective
public import Stellmacher.SectionTwo.BaumannOmegaSelectedModule
public import Stellmacher.SL2FrattiniUniqueMaximal

/-!
# The actual ambient selected factor for (6.3)

Under Hypothesis Two, assume J(S) is not contained in O₂(P₁). Select a
native subgroup K of P₁ with its supplied Sylow two-subgroup T. Under the
original inclusion f into H, T has image B(S), K lies in the P₁-normal
closure of B(S), and K together with S generates P₁. Retain K's nested
SL₂(2) Frattini quotient. Its ambient image belongs to the local family
over B(S), and W = [Ω₁(Z(B(S))), O²(f(K))] has order four, lies in B(S),
and is normalized by that normal closure. Its fixed subgroup on Ω₁(Z(B(S)))
has relative index two.

The native local-data theorem supplies the Section Two hypotheses. Apply
the selected omega-module theorem to the normal closure Z of Ω₁(Z(B)),
using the exact quotient by C(Z). Its four-element module lies in the
normal elementary subgroup Z ≤ K, so the two-core of K is nontrivial.
The nested SL₂ quotient has even order; divisibility of quotient orders
and the odd Sylow index show that T cannot equal that core. The nested
Frattini condition supplies unique maximal containment and hence actual
local-family membership. Injective maps then transport the omega/residual
commutator, its cardinality, normalizer, and centralizer index to H.

This is the opening selection in Stellmacher (6.3), using (2.2), journal
pp.20 and 31; source: refs/latex/stellmacher-n-group.tex. The conclusion
retains the literal omega commutator and the native nested quotient; no
order-four assertion about the full core/residual commutator is made.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem closure_map_subtype {H : Type*} [Group H]
    (X P : Subgroup H) (hXP : X ≤ P) :
    (Subgroup.normalClosure (X.subgroupOf P : Set P)).map P.subtype =
      conjugateClosure X P := by
  rw [Subgroup.normalClosure, MonoidHom.map_closure, conjugateClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    refine ⟨a, ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val ha.symm
  · rintro ⟨a, z, rfl⟩
    let zP : P := ⟨z, hXP z.property⟩
    refine ⟨a * zP * a⁻¹, ?_, rfl⟩
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨zP, z.property, isConj_iff.mpr ⟨a, rfl⟩⟩

private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A K : Subgroup G) :
    (A ⊓ Subgroup.centralizer (K : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (K.map f : Set H) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, ?_⟩
    change f a ∈ Subgroup.centralizer (K.map f : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 k hk)
  · rintro _ ⟨⟨a, ha, rfl⟩, hcent⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change a ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply hf
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp hcent (f k) (Subgroup.mem_map_of_mem f hk)

public theorem sixThree_selected_factor
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hJ : ¬ elementaryAbelianMaxJ S ≤ twoCoreIn P1) :
    ∃ (K : Subgroup P1) (T : Sylow 2 K),
      let f := P1.subtype.comp K.subtype
      let W := ⁅omegaOneCenter (baumannIn S), twoResidualIn f.range⁆
      (T : Subgroup K).map f = baumannIn S ∧
      f.range ≤ sectionSixL (baumannIn S) P1 ∧ f.range ⊔ S = P1 ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      f.range ∈ PFamily (⊤ : Subgroup H) (baumannIn S) ∧
      Nat.card W = 4 ∧ W ≤ baumannIn S ∧
      sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W : Set H) ∧
      (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (f.range : Set H)).relIndex
        (omegaOneCenter (baumannIn S)) = 2 := by
  classical
  obtain ⟨_hSP1, SP, hSP⟩ := h.fiveOne.P1_mem.1.2.1
  obtain ⟨hsec, hcore, hnot, hunique⟩ := sixOne_native_local_data S0 S P1 P2 h hJ SP hSP
  let B : Subgroup P1 := (SP : Subgroup P1) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (SP : Subgroup P1)) : Set P1)
  let L := Subgroup.normalClosure (B : Set P1)
  let Z := Subgroup.normalClosure (omegaOneCenterAmbient B : Set P1)
  let _ : Z.Normal := Subgroup.normalClosure_normal
  have hBm : B.map P1.subtype = baumannIn S := by
    rw [baumann_map_injective P1.subtype P1.subtype_injective, hSP]
    rfl
  have hBL : baumannIn S ≤ P1 := hBm ▸ Subgroup.map_subtype_le B
  have hBsub : (baumannIn S).subgroupOf P1 = B := by
    rw [← hBm]
    exact Subgroup.comap_map_eq_self_of_injective P1.subtype_injective _
  have hLm : L.map P1.subtype = sectionSixL (baumannIn S) P1 := by
    dsimp only [L]
    rw [← hBsub]
    exact closure_map_subtype (baumannIn S) P1 hBL
  let C := Subgroup.centralizer (Z : Set P1)
  let _ : C.Normal := Subgroup.normal_centralizer
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  let _ := centralizerQuotientAction Z Subgroup.normalClosure_normal q hq hker
  obtain ⟨hZe, hZB, _hBinf, n, D, K, T, i, _hprod, _hDin, _hDF, _hDn, _hmod,
      hBK, hKL, hT, hA, hgen, _hKi, _hRi, hcomm, hcard, hnorm, hindex⟩ :=
    SectionTwo.baumann_omega_selected_module hsec SP hcore hnot hunique B L Z rfl rfl rfl q hq hker
  let _ : IsElementaryAbelian 2 Z := hZe
  let f : K →* H := P1.subtype.comp K.subtype
  have hf : Function.Injective f := P1.subtype_injective.comp K.subtype_injective
  have hTm : (T : Subgroup K).map f = baumannIn S := by
    rw [show f = P1.subtype.comp K.subtype from rfl, ← Subgroup.map_map, hT, hBm]
  have hfrange : f.range = K.map P1.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hgenm : f.range ⊔ S = P1 := by
    rw [hfrange, ← hSP, ← Subgroup.map_sup, hgen,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let W0 := ⁅Z, twoResidualAmbient K⁆
  let W := ⁅omegaOneCenter (baumannIn S), twoResidualIn f.range⁆
  have hW0Z : W0 ≤ Z := Subgroup.commutator_le_left _ _
  have hZK : Z ≤ K := hZB.trans hBK
  have hZcore : Z ≤ twoCoreAmbient K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hZK]
    exact Subgroup.map_mono (show Z.subgroupOf K ≤ pCore 2 K from
      le_sSup ⟨(inferInstance : Z.Normal).subgroupOf K,
        (IsElementaryAbelian.isPGroup 2 Z).comap_of_injective K.subtype K.subtype_injective⟩)
  have hQne : pCore 2 K ≠ ⊥ := by
    intro hb
    have hWbot : W0 = ⊥ := by
      apply le_bot_iff.mp
      have hc := hW0Z.trans hZcore
      simpa only [twoCoreAmbient, hb, Subgroup.map_bot] using hc
    have hc := Subgroup.card_eq_one.mpr hWbot
    change Nat.card W0 = 4 at hcard
    omega
  have hTnot : (T : Subgroup K) ≠ pCore 2 K := by
    intro heq
    apply T.not_dvd_index
    rw [heq, Subgroup.index_eq_card]
    have hdvd := (frattini (K ⧸ pCore 2 K)).card_quotient_dvd_card
    rw [SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hA] at hdvd
    exact dvd_trans (by decide : 2 ∣ 6) hdvd
  have hFamily := pFamily_range_of_injective f hf T (baumannIn S) hTm hQne hTnot
    (isUniqueMaximalContaining_of_sl2Two_frattini T hA)
  have hOmap : (omegaOneCenterAmbient B).map P1.subtype = omegaOneCenter (baumannIn S) := by
    rw [← omegaOneCenterAmbient_map_injective P1.subtype P1.subtype_injective, hBm]
    rfl
  have hWmap : W0.map P1.subtype = W := by
    dsimp only [W0, W]
    rw [← hcomm, Subgroup.map_commutator, hOmap]
    congr 1
    exact map_twoResidualAmbient_of_subgroup_image K P1.subtype f.range hfrange.symm
  have hWcard : Nat.card W = 4 := by
    rw [← hWmap, Subgroup.card_map_of_injective P1.subtype_injective]
    exact hcard
  have hWB : W ≤ baumannIn S := by
    rw [← hWmap, ← hBm]
    exact Subgroup.map_mono (hW0Z.trans hZB)
  have hWnorm : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W : Set H) := by
    rw [← hLm]
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨l, hl, rfl⟩ x hx
    rw [← hWmap] at hx ⊢
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨l * w * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hnorm hl) w).mp hw, by simp⟩
  have hfixed : (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (f.range : Set H)).relIndex
      (omegaOneCenter (baumannIn S)) = 2 := by
    rw [hfrange, ← hOmap, ← map_inf_centralizer P1.subtype P1.subtype_injective,
      Subgroup.relIndex_map_map_of_injective _ _ P1.subtype_injective]
    exact hindex
  exact ⟨K, T, hTm, hfrange ▸ (Subgroup.map_mono hKL).trans_eq hLm,
    hgenm, hA, hFamily, hWcard, hWB, hWnorm, hfixed⟩

end Stellmacher.SectionsFiveToSeven

