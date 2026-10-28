module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.FamilySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.StabilizerSource
public import Theory.GroupTheory.FourFamilyAction.LargeMixedNormalizer
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Geometry

/-!
# The actual mixed core and Thompson normalizer in the double linear branch

The first mixed join is the two-core of L1 J(S). The marked quadratic action
identifies its centralizer description, so both L1 and the original block
stabilizer normalize it. If the Thompson normalizer were larger than M0,
the four-point action would make this mixed normalizer too large. The
source elementary-core theorem then contradicts its noncommuting module
pair. Thus N_T(J(S))=M0 before constructing any torus. The independent
Thompson rank count implies M0=T by the two-group normalizer condition.

Source: Aschbacher–Smith, double linear case of 2.4.7, pp.540–541,
using the marked C.5.6(7) family and 2.4.3 maximality.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem map_centralizer_subgroup (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro g hg
  refine ⟨e.symm g,?_,e.apply_symm_apply g⟩
  intro a ha
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hg (e a) (mem_map_of_mem _ ha)

omit [Finite G] in
private theorem opposite_fixed (U : Subgroup G) (x : G)
    (hsq : U.conjBy (x^2) = U)
    (hfix : U ⊓ centralizer (U.conjBy x⁻¹ : Set G) = U ⊓ U.conjBy x⁻¹) :
    U.conjBy x⁻¹ ⊓ centralizer (U : Set G) = U.conjBy x⁻¹ ⊓ U := by
  have hn : x^2 ∈ normalizer (U : Set G) := mem_normalizer_iff_map_conj_eq.mpr hsq
  have hni : x⁻¹^2 ∈ normalizer (U : Set G) := by
    simpa only [inv_pow] using (normalizer (U : Set G)).inv_mem hn
  have hswap : (U.conjBy x⁻¹).conjBy x⁻¹ = U := by
    rw [conjBy_conjBy,←pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp hni
  have hh := congrArg (map (MulAut.conj x⁻¹).toMonoidHom) hfix
  rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective,
    map_inf _ _ _ (MulAut.conj x⁻¹).injective,map_centralizer_subgroup] at hh
  change U.conjBy x⁻¹ ⊓ centralizer ((U.conjBy x⁻¹).conjBy x⁻¹ : Set G) =
    U.conjBy x⁻¹ ⊓ (U.conjBy x⁻¹).conjBy x⁻¹ at hh
  rwa [hswap] at hh

theorem DoubleLinearSourceSetup.mixed_join_eq_core
    (c : DoubleLinearSourceSetup d M₀ n) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := elementaryAbelianMaxJ S
    let L₁ := d.block.map d.H.subtype
    let C := S ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule L₁
    let V₂ := (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom
    twoCore d.H ⊔ ((U₁ ⊔ V₂) ⊔ C) = (L₁ ⊔ R).pCoreIn 2 := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let L₁ := d.block.map d.H.subtype
  let U₁ := sourceModule L₁
  let U₂ := sourceModule c.second
  let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
  let C := S ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
  let Q := twoCore d.H
  let W := Q ⊔ ((U₁ ⊔ V₂) ⊔ C)
  have ht : ∃ t : M₀, (t:G) ∈ S ∧ L₁.conjBy (t:G)=c.second := by
    obtain ⟨t,ht,he⟩ := c.exchange
    exact ⟨⟨t,c.original.R_le_M ht⟩,ht,he⟩
  have hx : c.x ∈ normalizer (S : Set G) := c.original.R_normal c.x_mem
  have hb : ChapterB.baumann S = R := (c.core_span hi).1
  have hQR : Q ≤ R := le_sup_left.trans_eq (c.core_span hi).2.symm
  have hc := d.rank_one_two_block_core_source T hST M₀ c.second c.original.R_le_M hMT hi
    c.commutes c.permutes c.marked₁ c.marked₂ ht
  have hQ : Q = (U₁ ⊔ U₂) ⊔ C := by
    have hh := hc.2.1
    rw [(d.two_block_closures c.second c.permutes c.exchange).2,←c.join] at hh
    exact hh
  have hfull : S ⊓ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G)=Q := by
    have hh := d.two_block_core_centralizer c.second c.marked₁.short c.marked₂.short
      c.commutes c.permutes c.exchange
    rw [(d.two_block_closures c.second c.permutes c.exchange).2] at hh
    exact hh
  have hlocal : R ⊓ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G)=Q :=
    le_antisymm ((inf_le_inf (sSup_le (fun _ h => h.1)) le_rfl).trans_eq hfull)
      (le_inf hQR (hfull ▸ inf_le_right))
  have hf := c.marked₁.two_block_factorization c.marked₂ c.commutes M₀ S c.x c.x_mem hx
    hi c.permutes ht c.noncommuting
  have hspan : R = (V₁ ⊔ V₂) ⊔ Q := by
    have hh := hf.2.2.1
    change ChapterB.baumann S = (U₁ ⊔ U₂).map (MulAut.conj c.x⁻¹).toMonoidHom ⊔
      (ChapterB.baumann S ⊓ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G)) at hh
    rw [hb,hlocal,Subgroup.map_sup] at hh
    exact hh
  have hW : W = Q ⊔ V₂ := by
    dsimp only [W]
    rw [hQ]
    simp only [sup_assoc,sup_left_comm,sup_comm,sup_left_idem]
  have hWR : W ≤ R := by
    rw [hW,hspan]
    exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  have hgen : R = V₁ ⊔ W := by
    rw [hW,hspan]
    ac_rfl
  have hg := c.marked₁.four_module_geometry c.commutes c.marked₂.module_le M₀ S c.x c.x_mem
    hx hi c.permutes ht c.noncommuting
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp hg.2.2.2
  have hV₂ : V₂ ≤ centralizer (U₁ : Set G) :=
    (le_sup_right.trans (le_centralizer_iff.mp hcomm)).trans
      (centralizer_le (show U₁ ≤ U₁ ⊔ V₁ from le_sup_left))
  have hWC : W ≤ centralizer (U₁ : Set G) := by
    rw [hW]
    exact sup_le ((hfull ▸ inf_le_right).trans (centralizer_le (show U₁ ≤ U₁ ⊔ U₂ from le_sup_left))) hV₂
  have hsq : U₁.conjBy (c.x^2)=U₁ := hg.2.2.1 0
  have hfix := c.marked₁.commutator_eq_fixed hx c.noncommuting
  have hdual : V₁ ⊓ centralizer (U₁ : Set G)=V₁ ⊓ U₁ :=
    opposite_fixed U₁ c.x hsq (hfix.1.symm.trans hfix.2)
  have hUVQ : U₁ ≤ Q := hQ ▸ le_sup_left.trans le_sup_left
  have hnV : R ≤ normalizer (V₁ : Set G) := hb ▸ c.marked₁.conjugate_normalized hx
  have he : R ⊓ centralizer (U₁ : Set G)=W := by
    apply le_antisymm
    · rintro a ⟨haR,haC⟩
      have ham : a ∈ (V₁ : Set G)*(W : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left V₁ W (hWR.trans hnV),←hgen]
        exact haR
      obtain ⟨v,hv,w,hw,rfl⟩ := ham
      have hvC : v ∈ centralizer (U₁ : Set G) := by
        simpa only [mul_inv_cancel_right] using
          (centralizer (U₁ : Set G)).mul_mem haC ((centralizer (U₁ : Set G)).inv_mem (hWC hw))
      exact W.mul_mem (mem_sup_left (hUVQ ((hdual ▸ (show v ∈ V₁ ⊓ centralizer (U₁ : Set G) from ⟨hv,hvC⟩)).2))) hw
    · exact le_inf hWR hWC
  have hcore := c.marked₁.core
  change (L₁ ⊔ ChapterB.baumann S).pCoreIn 2 = ChapterB.baumann S ⊓ centralizer (U₁ : Set G) at hcore
  rw [hb,he] at hcore
  exact hcore.symm

/-- The larger four-point action is impossible in the original source:
its mixed normalizer would force the nonelementary mixed group to be elementary. -/
theorem DoubleLinearSourceSetup.thompson_normalizer_eq
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    (T : Subgroup G) ⊓ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G) = M₀ := by
  let := c.field₁_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let L₁ := d.block.map d.H.subtype
  let C := S ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
  let U₁ := sourceModule L₁
  let V₂ := (sourceModule c.second).map (MulAut.conj c.x⁻¹).toMonoidHom
  let Q := twoCore d.H
  let W := Q ⊔ ((U₁ ⊔ V₂) ⊔ C)
  have hb := (c.core_span hi).1
  obtain ⟨f,hfi,hfam,h0,h1,h2,h3⟩ := c.labelled_max_family hi
  have hfamS : Set.range f=elementaryAbelianMaxSubgroups S := hfam.trans (c.max_family_eq_source hi)
  have hpair : {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)}={f 0,f 1} := by
    rw [h0,h1]
    exact (c.core_pair T hST c.original.R_le_M hMT hi).2.2
  have hcontrol : (T : Subgroup G) ⊓ normalizer (f 0 : Set G)=S := by
    rw [h0]
    obtain ⟨P,hP⟩ := (lemma_2_3_9_1 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl).2.1
    exact (inf_eq_sylow_map P T.isPGroup' (hP.le.trans hST)).trans hP
  have he := FourFamilyAction.normalizer_eq_or_large_mixed (T : Subgroup G) M₀ S T.isPGroup'
    c.original.R_le_M hMT hi f hfi hfamS hpair hcontrol
  rcases he with he | hlarge
  · exact he
  exfalso
  have hcore : W=(L₁ ⊔ R).pCoreIn 2 := c.mixed_join_eq_core T hST hMT hi
  have hSN : S ≤ normalizer (R : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ S)
  have hBN : (S ⊓ normalizer (L₁ : Set G)) ≤ normalizer (W : Set G) := by
    rw [hcore]
    exact ((le_inf inf_le_right (inf_le_left.trans hSN)).trans
      (normalizer_inf_normalizer_le_normalizer_sup L₁ R)).trans
      (normalizer_le_normalizer_characteristic_image (L₁ ⊔ R) (pCore 2 (L₁ ⊔ R : Subgroup G)))
  have hLN : L₁ ≤ normalizer (W : Set G) := by
    rw [hcore]
    exact (le_sup_left.trans (L₁ ⊔ R).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (L₁ ⊔ R) (pCore 2 (L₁ ⊔ R : Subgroup G)))
  have hWS : W ≤ S := by
    have hq : f 0 ∈ elementaryAbelianMaxSubgroups S := hfamS ▸ ⟨0,rfl⟩
    have hp : f 2 ∈ elementaryAbelianMaxSubgroups S := hfamS ▸ ⟨2,rfl⟩
    rw [h0] at hq
    rw [h2] at hp
    exact sup_le hq.1 hp.1
  have hsmall := c.mixed_normalizer_card_lt hG T hM hTM hu hST c.original.R_le_M hMT hi W
    le_sup_left hWS hBN hLN (c.mixed_joins_not_elementary hi).1
  rw [h0,h2] at hlarge
  exact (not_le_of_gt hsmall) hlarge

/-- The independent source rank count now has only the Thompson equality
to supply: its normalizer is already the original index-two overgroup. -/
theorem DoubleLinearSourceSetup.sylow_eq_of_thompson_stable
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hJ : elementaryAbelianMaxJ M₀ =
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    M₀ = (T : Subgroup G) :=
  LinearDouble.sylow_eq_of_thompson_self_normalizer T M₀ _ hMT hJ.symm
    (c.thompson_normalizer_eq hG T hM hTM hu hST hMT hi)

end CFSG.Quasithin.Chapter2
