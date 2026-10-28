module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianMathieu
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Source geometry of the nonabelian point span

The original higher-rank hypotheses construct the commutator form, full
transvection action, fixed line and exact rank identity on U/Z(U). All
parabolic generation, core, relative normality and kernel premises are
supplied by the earlier source setup, with the original quotient maps.

When Z(U) is larger than V₁, a trivial dotted conjugate center would force
the normal point component into M by local uniqueness, contradicting the
proved normal-case abelianity. When Z(U)=V₁, the preimage of a dotted point
centralizer embeds in the tilded-plane centralizer. Its cyclic Sylow
three-group bounds the quotient's three-rank. Together these prove the
center-detection implication needed by the A₇ and orthogonal calculations.

Source: Aschbacher--Smith 12.8.11,12.8.13(4,8) and 12.9.4,
printed pp.854--857,859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

private structure Geometry (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    [IsElementaryAbelian 2 F.Uhat] where
  two : IsPGroup 2 F.U
  phi : frattini F.U = (F.Vi 1).subgroupOf F.U
  comm : ⁅F.U,F.U⁆ ≤ F.Vi 1
  squares : ∀ u ∈ F.U, u^2 ∈ F.Vi 1
  center : V ⊓ F.ZU = F.Vi 1
  span : F.U = conjugateSpanBy (F.Vi 2) F.H
  form : F.UhatCommutatorForm comm
  ile : F.I₂ L ≤ F.Gi 2
  inormal : ((F.I₂ L).subgroupOf (F.Gi 2)).Normal
  icore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2
  iquotient : Nonempty ((F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
  split : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g
  enormal : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal
  elementary : let := enormal
    IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g))
  disjoint : Disjoint (conjugate (F.Vi 1) g) F.ZU
  cut : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1
  conjugate_cut : conjugate F.ZU g ⊓ F.U =
    (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g
  kernel : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g

omit [Finite G] in
private theorem quotient_elementary_transport (E A B : Subgroup G) (he : A = B)
    [_hA : (E.subgroupOf A).Normal] [_hB : (E.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (A ⧸ E.subgroupOf A)] :
    IsElementaryAbelian 2 (B ⧸ E.subgroupOf B) := by
  subst B
  infer_instance

private theorem geometry {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nonempty (Geometry F L g) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hJ := h.point_mem_Hz F earlier.alternatives
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  obtain ⟨hc,hs⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hv := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have hspan := F.U_eq_plane_span L hn h.chosen.normalizes
    (F.localKernel_irreducible L hn h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  have hcore := F.localKernel_eq_pCore h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L hJ
  let B := F.localKernel_markedForm (by omega) htwo hphi hc
  obtain ⟨e,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hIC,hindex,_⟩ :=
    F.binary_generation hn L h.chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT earlier.structural) hc hs hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hIC hindex
  have hnE := F.binary_source_E_normal_in_core L h.chosen.normalizes g hgP hgen.symm hc
  have heE := F.binary_source_quotient_elementary L h.chosen.normalizes g hgP hgen.symm hIC
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hc hs
  have hcenters := F.binary_source_center_calculations hn L h.chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes earlier.structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT earlier.structural) hv hc hs hspan hne g hgP hgH hcore B
  have hnS : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal := hsplit ▸ hnE
  let := hnS
  refine ⟨⟨htwo,hphi,hc,hs,hv,hspan,B,hIG,hIN,hIC,⟨e⟩,hsplit,hnS,?_,?_,
    hcenters.1,?_,?_⟩⟩
  · let := hnE
    let := heE
    exact quotient_elementary_transport (F.E g) _ _ hsplit
  · exact disjoint_iff.mpr (F.parabolic_displaced_centers hn L h.chosen.normalizes
      hv g hgP hgH).1
  · simpa only [inf_comm] using hcenters.2.2.2.2.2.2.2.2.1
  · exact (F.binary_source_action_kernel_intersections hn L h.chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
      hc hs hspan hne hv g hgP hgH).1

private theorem binary_primeRank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : primeRank 2 A = finrank (ZMod 2) (Additive A) := by
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le A hc.le)
  have hh := (primeRank_le_iff_elementary_card_le A).mp (le_refl (primeRank 2 A))
    (⊤ : Subgroup A) (IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective)
  rw [card_top,hc] at hh
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh

omit [Finite G] in
private theorem Geometry.form_zero (F : InvariantFlag T V n) (g : G)
    [IsElementaryAbelian 2 F.Uhat] (d : Geometry F L g) (a b : F.U) :
    d.form.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
  rw [show d.form.form (hatElement F a) (hatElement F b) = _ from d.form.evaluation a b]
  change d.form.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff d.form.valueEquiv d.form.valueEquiv.injective, Subtype.ext_iff]
  change ⁅(a:G),(b:G)⁆ = 1 ↔ a*b=b*a
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩

omit [Finite G] in
private theorem Geometry.form_preserves (F : InvariantFlag T V n) (hn : 1 ≤ n) (g : G)
    [IsElementaryAbelian 2 F.Uhat] (d : Geometry F L g) (t : F.TerminalHdot)
    (v w : Additive F.Uhat) :
    d.form.form (F.terminalRepresentation t v) (F.terminalRepresentation t w) = d.form.form v w := by
  obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker t
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center F.U) v.toMul
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center F.U) w.toMul
  have hv : v = hatElement F a := (congrArg Additive.ofMul ha).symm
  have hw : w = hatElement F b := (congrArg Additive.ofMul hb).symm
  rw [hv,hw]
  have action (c : F.U) : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker t)
      (hatElement F c) = hatElement F (F.uAction t c) := by
    apply Additive.toMul.injective
    exact (F.terminalRepresentation_apply_mk t (hatElement F c)).trans
      (F.terminalHatAction_apply_mk t c)
  rw [action,action]
  rw [show d.form.form (hatElement F (F.uAction t a)) (hatElement F (F.uAction t b)) = _
      from d.form.evaluation (F.uAction t a) (F.uAction t b),
    show d.form.form (hatElement F a) (hatElement F b) = _ from d.form.evaluation a b]
  apply congrArg (fun z : F.Vi 1 => (d.form.valueEquiv z).toAdd)
  apply Subtype.ext
  have hc : (t : G) ∈ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 hn) t.property
  have hh := hc ⁅(a:G),(b:G)⁆ (d.comm (commutator_mem_commutator a.property b.property))
  change ⁅(F.uAction t a:G),(F.uAction t b:G)⁆ = ⁅(a:G),(b:G)⁆
  rw [F.uAction_apply,F.uAction_apply]
  calc
    ⁅(t:G) * a * (t:G)⁻¹,(t:G) * b * (t:G)⁻¹⁆ =
        (t:G) * ⁅(a:G),(b:G)⁆ * (t:G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    _ = ⁅(a:G),(b:G)⁆ := by rw [←hh,mul_inv_cancel_right]

/-- The actual nonabelian parabolic has the source three-rank bound, with
all generation, normality and quotient premises supplied by the original setup. -/
theorem nonabelian_tilde_plane_three_rank {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    primeRank 3 F.terminalTildePlaneCentralizer ≤ 1 := by
  let := h.chosen.elementary
  let := nonabelian_hat_elementary h earlier F hne
  obtain ⟨d⟩ := geometry h earlier F hne g hgP hgH
  exact F.lemma_12_8_13_eight h.source.simpleQTKE.quasithin
    (by have := h.rank; omega) L d.ile d.inormal d.icore d.iquotient

/-- Full transvections, fixed space and exact rank on the literal nonabelian
quotient. All earlier parabolic and center-intersection premises are discharged. -/
theorem nonabelian_transvection_geometry {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
    let := hX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
      (v : hatSpace F (F.E g)),
      B.Nondegenerate ∧ B.IsAlt ∧
      (∀ a u w, B (F.terminalRepresentation a u) (F.terminalRepresentation a w) = B u w) ∧
      (v : Additive F.Uhat) ≠ 0 ∧
      hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {(v : Additive F.Uhat)} ∧
      F.X g ≤ (T : Subgroup G) ∧
      (∀ e ∈ hatSpace F (F.E g), ∀ f ∈ hatSpace F (F.E g), B e f = 0) ∧
      (∀ x : F.terminalDot (F.X g), ∃ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)),
        φ v = 0 ∧ ∀ e : hatSpace F (F.E g), F.terminalRepresentation x e =
          (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) ∧
      (∀ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 →
        ∃ x : F.terminalDot (F.X g), ∀ e : hatSpace F (F.E g),
          F.terminalRepresentation x e = (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) ∧
      hatSpace F (F.E g) ⊓ BinaryOffender.fixedSpace F.terminalRepresentation
        (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      ⁅F.W,F.X g⁆ ≤ F.E g ∧
      hatSpace F F.W = (B (v : Additive F.Uhat)).ker ∧
      finrank (ZMod 2) (hatSpace F (F.E g)) +
        finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
          (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) =
        finrank (ZMod 2) (Additive F.Uhat) - 1 := by
  let := h.chosen.elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  obtain ⟨d⟩ := geometry h earlier F hne g hgP hgH
  let := d.enormal
  let := d.elementary
  have hg := F.P_le_G₂ hn L h.chosen.normalizes hgP
  let hX := Xdot_uhatAction_elementary F g hg
  refine ⟨hX,?_⟩
  let := hX
  obtain ⟨v,hv,hline,htrans,hfull⟩ := full_transvection_action F hn g hg d.comm d.center
    d.disjoint d.cut d.conjugate_cut d.form.form (d.form_zero F g)
    d.form.nondegenerate d.form.alternating.isRefl
  refine ⟨d.form.form,v,d.form.nondegenerate,d.form.alternating,d.form_preserves F (by omega) g,
    hv,hline.symm,?_,?_,htrans,hfull,?_,commutator_W_X_le_E F g,?_,?_⟩
  · exact F.X_le_T_of_parabolic_core L g d.ile
      ((normal_subgroupOf_iff_le_normalizer d.ile).mp d.inormal) d.split
  · have hp : (frattini F.U).map F.U.subtype = F.Vi 1 := by
      rw [d.phi]
      exact map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
        (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    exact Ehat_totally_isotropic F (by omega) g d.two hp d.disjoint d.form.form (d.form_zero F g)
  · have hf := EhatFixed_eq_plane F g hg d.comm d.disjoint d.cut d.conjugate_cut
      d.form.form (d.form_zero F g) d.form.nondegenerate d.form.alternating.isRefl
    rw [←hf]
    ext x
    simp only [EhatFixed,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
      LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]
    rfl
  · rw [What_eq_orthogonal F d.form.form (d.form_zero F g),← hline]
    ext w
    simp only [LinearMap.BilinForm.mem_orthogonal_iff,Submodule.mem_span_singleton,
      LinearMap.mem_ker]
    constructor
    · intro hh
      exact hh _ ⟨1,one_smul _ _⟩
    · rintro hh _ ⟨a,rfl⟩
      simp only [map_smul,LinearMap.smul_apply,hh,smul_zero]
  · have hk : ∀ x : F.H, (x:G) ∈ F.X g → (F.uhatAction x = 1 ↔ (x:G) ∈ F.E g) := by
      intro x hx
      constructor
      · intro he
        exact d.kernel.le ⟨hx,⟨x,he,rfl⟩⟩
      · intro he
        obtain ⟨_,y,hy,hey⟩ := d.kernel.ge he
        exact (Subtype.ext hey : y = x) ▸ hy
    have hr := transvection_rank_identity F hn g hg d.center d.disjoint d.cut d.conjugate_cut hk
      d.form.form (d.form_zero F g) d.form.nondegenerate
    let : IsElementaryAbelian 2 (hatImage F (F.E g)) :=
      IsElementaryAbelian.of_injective (hatImage F (F.E g)).subtype (hatImage F (F.E g)).subtype_injective
    let : IsElementaryAbelian 2 (XdotCenterQuotient F F.uhatAction g) :=
      IsElementaryAbelian.quotient _
    dsimp only at hr
    rw [binary_primeRank,binary_primeRank,binary_primeRank] at hr
    have he : finrank (ZMod 2) (Additive (hatImage F (F.E g))) =
        finrank (ZMod 2) (hatSpace F (F.E g)) := by
      apply Nat.pow_right_injective (by decide : 2 ≤ 2)
      have hA := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (hatImage F (F.E g)))
      have hB := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F (F.E g))
      simp only [Nat.card_zmod] at hA hB
      dsimp only
      rw [←hA,←hB]
      exact (Nat.card_congr Additive.toMul).trans (card_hatSpace F (F.E g)).symm
    rwa [he] at hr

/-- In the original degrees four and five, a nontrivial center modulo V₁
has nontrivial image under the action of its conjugate on U/Z(U).
The proof uses the actual normal point component and the original uniqueness
hypothesis, rather than adding a center-detection premise. -/
theorem nonabelian_conjugate_center_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (hZ : F.Vi 1 < F.ZU) :
    F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  let := h.chosen.elementary
  let := nonabelian_hat_elementary h earlier F hne
  obtain ⟨d⟩ := geometry h earlier F hne g hgP hgH
  intro hzero
  have hgN := F.P_le_seed_normalizer L h.chosen.normalizes hgP
  have hg2 := F.P_le_G₂ (by omega) L h.chosen.normalizes hgP
  have hZH := (F.conjugate_ZU_le_X g).trans (F.X_le_H g hg2)
  have hZU : conjugate F.ZU g ≤ F.U := by
    intro z hz
    have hzq : QuotientGroup.mk' F.terminalHatAction.ker ⟨z,hZH hz⟩ ∈
        F.terminalDot (conjugate F.ZU g) := mem_map_of_mem _ hz
    rw [hzero,mem_bot] at hzq
    have hk : (⟨z,hZH hz⟩ : F.H) ∈ F.uhatAction.ker :=
      (QuotientGroup.eq_one_iff _).mp hzq
    exact (inf_le_left.trans inf_le_left : F.E g ≤ F.U)
      (d.kernel.le ⟨F.conjugate_ZU_le_X g hz,⟨⟨z,hZH hz⟩,hk,rfl⟩⟩)
  obtain ⟨⟨hprod,_,_⟩,hLC⟩ := h.localKernel_center_product earlier F hne g hgP hgH hZU
  let A := Section08.centerIn (F.I₂ L)
  have hAne : A ≠ ⊥ := by
    intro he
    change Section08.centerIn (F.I₂ L) = ⊥ at he
    have heZ : F.ZU = F.Vi 1 := by simpa only [he,bot_sup_eq] using hprod
    exact hZ.ne heZ.symm
  have hAZ : A ≤ F.ZU := le_sup_left.trans hprod.ge
  have hAU : A ≤ F.U := hAZ.trans (map_subtype_le _)
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) := by
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp hLC).trans (Subgroup.centralizer_le_normalizer _)
    · exact ((F.invariant 2).trans
        ((normal_subgroupOf_iff_le_normalizer d.ile).mp d.inormal)).trans
          (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))
  have hAM : normalizer (A : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    · exact (d.two.to_subgroup (A.subgroupOf F.U)).of_equiv (subgroupOfEquivOfLe hAU)
    · exact hAne
    · exact hLT
  have hLZ : F.Li L 1 ≤ centralizer (F.ZU : Set G) := by
    have hLA := ((F.Li_le L 1).trans inf_le_left).trans
      (commutator_eq_bot_iff_le_centralizer.mp hLC)
    have hLP := ((F.Li_le L 1).trans inf_le_right).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by omega)))
    apply le_centralizer_iff.mpr
    rw [hprod]
    exact sup_le (le_centralizer_iff.mp hLA) (le_centralizer_iff.mp hLP)
  obtain ⟨C⟩ := componentGeometry earlier h hn F
  let D := C.K1.subgroupOf F.H
  let R := ((centralizer (F.ZU : Set G)).subgroupOf F.H).subgroupOf D
  have hHN : F.H ≤ normalizer (F.ZU : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_characteristic_image F.U (Subgroup.center F.U))
  let : R.Normal := normal_subgroupOf_of_le_normalizer (by
    intro c hc z
    exact ((hHN.trans (normalizer_le_normalizer_centralizer F.ZU))
      (C.point_le hc)) (z.val : G))
  have hR : R = ⊤ := by
    by_contra hr
    let := C.component.isSolvable_of_subnormal_lt_top (inferInstance : R.Normal).isSubnormal hr
    let f : F.Li L 1 →* R :=
      { toFun := fun x => ⟨⟨⟨x,(F.Li_le L 1 x.property).2⟩,C.contains x.property⟩,hLZ x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b he
      exact Subtype.ext (congrArg (fun r : R => (((r : D) : F.H) : G)) he)
    have hi : ComponentIndex n 1 := by
      rcases hn with rfl | rfl
      · exact Or.inr ⟨rfl,Or.inl rfl⟩
      · exact Or.inl ⟨rfl,by decide,by decide⟩
    exact Chapter1.mem_L_not_isSolvable (Li_mem_local h earlier F 1 hi)
      (Group.isSolvable_of_isSolvable_injective hf)
  have hKM : C.K1 ≤ normalizer (L : Set G) := by
    intro x hx
    have hr : (⟨⟨x,C.point_le hx⟩,hx⟩ : D) ∈ R := hR.symm ▸ mem_top _
    exact hAM ((Subgroup.centralizer_le_normalizer (A : Set G))
      ((centralizer_le hAZ) (show x ∈ centralizer (F.ZU : Set G) from hr)))
  have hi : ComponentIndex n 1 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inl rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  have he := component_eq_of_le_normalizer h earlier F 1 hi
    ⟨C.point_le,C.component⟩ C.contains hKM
  exact hne (point_span_abelian_of_point_residual_normal h hn earlier F (he ▸ C.normal))

/-- When the whole center is V₁, the preimage of a hatted point centralizer
embeds in the literal tilded-plane centralizer. Its cyclic Sylow three-group
therefore bounds the quotient's three-rank. -/
theorem nonabelian_point_three_rank_of_center_eq {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hZ : F.ZU = F.Vi 1) : primeRank 3 (F.terminalPointCentralizer v) ≤ 1 := by
  let := h.chosen.elementary
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let A := (F.terminalPointCentralizer v).comap q
  have hAC : A.map F.H.subtype ≤ F.terminalTildePlaneCentralizer := by
    rintro _ ⟨t,ht,rfl⟩
    refine ⟨t,?_,rfl⟩
    intro y hy
    obtain ⟨u,hu,rfl⟩ := hy
    let c : F.U := ⟨u,le_conjugateSpanBy V F.H (F.le_seed 2 hu)⟩
    have hc : hatElement F c ∈ Submodule.span (ZMod 2) {v} :=
      hline ▸ show hatElement F c ∈ hatSpace F (F.Vi 2) from ⟨c,hu,rfl⟩
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hc
    have htfix : F.terminalRepresentation (q t) v = v := ht
    have hfix : F.terminalRepresentation (q t) (hatElement F c) = hatElement F c := by
      rw [←ha,map_smul,htfix]
    have he : QuotientGroup.mk' (Subgroup.center F.U) (F.uAction t c) =
        QuotientGroup.mk' (Subgroup.center F.U) c := by
      have hh := congrArg Additive.toMul hfix
      rw [F.terminalRepresentation_apply_mk] at hh
      change F.terminalHatAction t (QuotientGroup.mk' (Subgroup.center F.U) c) =
        QuotientGroup.mk' (Subgroup.center F.U) c at hh
      rw [F.terminalHatAction_apply_mk] at hh
      exact hh
    have hk := QuotientGroup.eq_iff_div_mem.mp he
    have hm : ⁅(t:G),(u:G)⁆ ∈ F.Vi 1 := by
      rw [←hZ]
      refine ⟨F.uAction t c / c,hk,?_⟩
      change (t:G) * (u:G) * (t:G)⁻¹ / (u:G) = ⁅(t:G),(u:G)⁆
      simp only [commutatorElement_def, div_eq_mul_inv]
    have hmH : ⁅t,u⁆ ∈ (F.Vi 1).subgroupOf F.H := hm
    have he' := (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H) ⁅t,u⁆).mpr hmH
    rw [←QuotientGroup.mk'_apply,map_commutatorElement] at he'
    exact (commutatorElement_eq_one_iff_mul_comm.mp he').symm
  let f : A →* F.terminalTildePlaneCentralizer :=
    (F.H.subtype.comp A.subtype).codRestrict _ (fun x => hAC (mem_map_of_mem _ x.property))
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : F.terminalTildePlaneCentralizer => (z:G)) he))
  have hr : primeRank 3 A ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 f hf).trans
      (nonabelian_tilde_plane_three_rank h earlier F hne g hgP hgH)
  let r : A →* F.terminalPointCentralizer v :=
    (q.comp A.subtype).codRestrict _ (fun x => x.property)
  have hs : Function.Surjective r := by
    intro x
    obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker x.val
    exact ⟨⟨t,show q t ∈ F.terminalPointCentralizer v from ht ▸ x.property⟩,Subtype.ext ht⟩
  let S : Sylow 3 A := Classical.choice inferInstance
  exact S.primeRank_le_one_of_surjective (S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) r hs

/-- The source implication needed in the natural A₇ calculation: a point
centralizer of three-rank greater than one forces a nontrivial dotted
conjugate center. No terminal detection hypothesis remains. -/
theorem nonabelian_conjugate_center_detected
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hr : 1 < primeRank 3 (F.terminalPointCentralizer v)) :
    F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  intro hz
  have hZ : F.ZU = F.Vi 1 := by
    by_contra he
    let := h.chosen.elementary
    have hp := F.point_le_ZU (by omega : 1 ≤ n)
    exact nonabelian_conjugate_center_ne_bot h hn earlier F hne g hgP hgH
      (lt_of_le_of_ne hp (Ne.symm he)) hz
  exact (not_lt_of_ge (nonabelian_point_three_rank_of_center_eq h earlier F hne
    g hgP hgH v hline hZ)) hr

omit [Finite G] in
/-- The Sylow subgroup fixes the unique nonzero point of the hatted plane. -/
theorem sylow_fixes_plane_hat_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v := by
  rintro _ ⟨t,ht,rfl⟩
  have hvP : v ∈ hatSpace F (F.Vi 2) := hline ▸ Submodule.mem_span_singleton_self v
  obtain ⟨u,hu,he⟩ := (show v.toMul ∈ hatImage F (F.Vi 2) from hvP)
  have himage : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker t) v ∈
      hatSpace F (F.Vi 2) := by
    refine ⟨F.uAction t u,?_,?_⟩
    · exact (mem_normalizer_iff.mp (F.invariant 2 ht) u).mp hu
    · rw [F.terminalRepresentation_apply_mk,←he,F.terminalHatAction_apply_mk]
      congr 1
  rw [hline] at himage
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp himage
  have hnon : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker t) v ≠ 0 := by
    intro hz
    have he := congrArg (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker t)⁻¹) hz
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at he
    exact hv he
  have ha01 : a = 0 ∨ a = 1 := by
    have hh := ZMod.val_lt a
    have hh' : a.val = 0 ∨ a.val = 1 := by omega
    rcases hh' with hh' | hh'
    · left
      apply ZMod.val_injective
      simpa only [ZMod.val_zero] using hh'
    · right
      apply ZMod.val_injective
      simpa only [ZMod.val_one] using hh'
  rcases ha01 with rfl | rfl
  · exact (hnon (by simpa only [zero_smul] using ha.symm)).elim
  · simpa only [one_smul] using ha.symm

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
