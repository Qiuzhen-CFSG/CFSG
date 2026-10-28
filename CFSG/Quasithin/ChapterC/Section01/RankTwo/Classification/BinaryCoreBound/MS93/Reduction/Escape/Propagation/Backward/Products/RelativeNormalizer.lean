module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Individual
/-!
# Relative-normalizer action on the backward span

The generating group on MS93 p.887 is `G_a ∩ N(Q_t)`, as defined on p.881.
Every automorphism of the actual edge kernel is realized in its holomorph
vertex stabilizer. Thus an element of the relative normalizer agrees on Q_t
with an element fixing t. The adjacent radius groups lie in Q_t, and this
realized action fixes Z_a. Covariance of B then preserves the literal reverse
condition `a ∈ movingNeighbors d`, including its noncontainment clause.
This proves normalization of W(t) directly, without requiring the original
normalizer element to fix the vertex t.

The endpoint commutator bound makes W(t)V_a normal in G_a. Inside that finite
local group, the normal closure of the escaping endpoint controls the actual
two-residual. Its idempotence sharpens the range to Vcirc_a. Transport through
G_a gives the residual bound for each individual V_d; generation by the
residual and the common edge kernel then proves individual product normality.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on printed p.881 and (4.3.7)(i), printed pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Realize the full edge-kernel normalizer action inside its holomorph
stabilizer, retaining pointwise agreement on the actual kernel. -/
theorem holomorph_realizes (t a : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t) (g : FreeAmalgam R)
    (hg : g ∈ normalizer (Q R t : Set (FreeAmalgam R))) :
    ∃ h ∈ stabilizer R t, ∀ x ∈ Q R t,
      (MulAut.conj h) x = (MulAut.conj g) x := by
  obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  swap
  · change true = false at ha
    cases ha
  let f := (MulAut.conj k⁻¹).toMonoidHom.comp (embedS R)
  have hf : Function.Injective f := (MulAut.conj k⁻¹).injective.comp (embedS_injective R)
  have hfr : f.range = Q R (hVertex R k) := by
    rw [MonoidHom.range_comp]
    have hq := Q_act R k (beta R)
    simpa only [beta, act_hVertex, one_mul, Q, neighborhoodKernel_h_base_eq_Sbar,
      Sbar] using hq.symm
  let e : R ≃* Q R (hVertex R k) :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hfr)
  let c := (Q R (hVertex R k)).normalizerMonoidHom ⟨g, hg⟩
  let A : MulAut R := e.trans (c.trans e.symm)
  let h₀ := embedH R (SemidirectProduct.inr A)
  refine ⟨(MulAut.conj k⁻¹) h₀, ?_, ?_⟩
  · rw [stabilizer_hVertex]
    exact mem_map_of_mem _ (show h₀ ∈ Hbar R from ⟨_, rfl⟩)
  · intro x hx
    obtain ⟨s, hs⟩ := e.surjective ⟨x, hx⟩
    have hsx : f s = x := congrArg Subtype.val hs
    rw [← hsx]
    have hc : f (A s) = (MulAut.conj g) (f s) := by
      change ((e (A s) : Q R (hVertex R k)) : FreeAmalgam R) = _
      simp only [A, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
    have hh : embedS R (A s) = h₀ * embedS R s * h₀⁻¹ := by
      have q := congrArg (embedH R) (SemidirectProduct.inl_aut A s)
      have hemb (r : R) : embedH R (SemidirectProduct.inl r) = embedS R r :=
        DFunLike.congr_fun (embedH_comp_inl R) r
      simpa only [MonoidHom.id_apply, map_mul, map_inv, hemb] using q
    change (MulAut.conj ((MulAut.conj k⁻¹) h₀)) (f s) = _
    rw [← hc]
    change (MulAut.conj ((MulAut.conj k⁻¹) h₀)) ((MulAut.conj k⁻¹) (embedS R s)) =
      (MulAut.conj k⁻¹) (embedS R (A s))
    rw [hh]
    simp only [map_mul, map_inv, MulAut.conj_apply]

omit [Finite M] in
/-- Agreement on the edge kernel transports every subgroup contained in it. -/
theorem map_conj_eq_of_agree {K T : Subgroup (FreeAmalgam R)}
    (hK : K ≤ T) {h g : FreeAmalgam R}
    (he : ∀ x ∈ T, (MulAut.conj h) x = (MulAut.conj g) x) :
    K.map (MulAut.conj h).toMonoidHom = K.map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor <;> rintro ⟨y, hy, rfl⟩
  · exact ⟨y, hy, (he y (hK hy)).symm⟩
  · exact ⟨y, hy, he y (hK hy)⟩

/-- The full relative normalizer preserves the reverse-moving span.
The holomorph realization fixes Z_a as a subgroup, so the transported
neighbor still satisfies the defining noncontainment in B. -/
theorem backwardSpan_relative_normalized (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R)) ≤
      normalizer (backwardSpan geometry a t : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨h, hht, he⟩ := holomorph_realizes t a ha hat g hg.2
  have hVQ (d : Vertex R) (hd : color R d = false) (hdt : Adjacent R d t) :
      V R d ≤ Q R t := (geometry.V_le_Q hb d hd).trans (Q_le_adjacent_h R ht hdt)
  have hZa : (Z R a).map (MulAut.conj h).toMonoidHom = Z R a :=
    (map_conj_eq_of_agree ((Z_le_VBall R a 2).trans (hVQ a ha hat)) he).trans
      (mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hg.1))
  have hfix : act R h⁻¹ t = t := (stabilizer R t).inv_mem hht
  have hmap : (backwardSpan geometry a t).map (MulAut.conj g).toMonoidHom ≤
      backwardSpan geometry a t := by
    rw [backwardSpan, Subgroup.map_iSup]
    apply iSup_le
    intro d
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hdt
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hmove
    have hdcol : color R d = false :=
      (color_eq_of_dist_even R d a (hmove.1.symm ▸ (by decide : Even 2))).trans ha
    rw [← map_conj_eq_of_agree (hVQ d hdcol hdt) he,
      ← inv_inv h, ← V_act]
    have het : Adjacent R (act R h⁻¹ d) t := by
      simpa only [hfix] using (adjacent_act_iff R h⁻¹ d t).mpr hdt
    have hn : ¬ Z R a ≤ B R (act R h⁻¹ d) (geometry.Z_normal _) := by
      rw [PairingControl.FirstPairing.B_act hb h⁻¹ d hdcol, inv_inv, ← hZa]
      exact fun hh => hmove.2 ((map_le_map_iff_of_injective (MulAut.conj h).injective).mp hh)
    apply V_le_backwardSpan het
    refine ⟨?_, hn⟩
    rw [SimpleGraph.dist_comm]
    apply neighbor_distance_two ha hat het
    intro hae
    apply hn
    rw [← hae]
    exact EdgeTransfer.Z_le_B hb a ha
  exact hmap (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- The source relative normalizer and endpoint generate the normal join. -/
theorem backwardSpan_join_normal_relativeNormalizer (p : Counterexample geometry)
    (hb : 4 < geometry.b R) (initial : InitialFacts p) (t : Vertex R)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔
      Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    backwardSpan geometry p.a t ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((backwardSpan geometry p.a t ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal := by
  have hb₂ : 2 < geometry.b R := by omega
  have hlocal : backwardSpan geometry p.a t ⊔ V R p.a ≤ stabilizer R p.a :=
    (sup_le (backwardSpan_le_Q p.color_a hb t)
      (geometry.V_le_Q hb₂ p.a p.color_a)).trans (fun _ hx => hx.1)
  refine ⟨hlocal, normal_subgroupOf_of_le_normalizer ?_⟩
  rw [← hgen]
  apply sup_le
  · exact (le_inf (backwardSpan_relative_normalized hb₂ p.color_a hat)
      (inf_le_left.trans (V_normalized p.a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · rw [sup_comm (backwardSpan geometry p.a t)]
    exact PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le _ _ _
      (p.end_Z_le_start_stabilizer.trans (V_normalized p.a))
      ((endpoint_commutator_le_radius p (by omega) initial _ hW).trans p.radius_le_start)

private theorem commutator_join_normal_le_relative {G : Type*} [Group G]
    (W N J : Subgroup G) [N.Normal] (hc : ⁅W, J⁆ ≤ N) : ⁅W ⊔ N, J⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hN : N.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' N).symm
  have hz : (⁅W ⊔ N, J⁆).map q = ⊥ := by
    rw [map_commutator, Subgroup.map_sup, hN, sup_bot_eq, ← map_commutator,
      Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hc
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- The residual estimate for the actual normal join at a selected edge. -/
theorem backwardSpan_join_residual_le_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔
      Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t ⊔ V R p.a, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let W := (backwardSpan geometry p.a t ⊔ V R p.a).subgroupOf S
  let V₀ := (V R p.a).subgroupOf S
  let J := (Z R p.a').subgroupOf S
  let π := initial.natural_section.projection
  obtain ⟨hWG, hnormal⟩ := backwardSpan_join_normal_relativeNormalizer p hb initial t hat hgen hW
  let : W.Normal := hnormal
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (V_normalized p.a)
  have hVG : V R p.a ≤ S := initial.natural_section.local_group
  have hJG : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  have hW₀G : backwardSpan geometry p.a t ≤ S := le_sup_left.trans hWG
  have hker : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hpW : IsPGroup 2 W :=
    ((Q_isPGroup R source.two_group source.core_le p.a p.color_a).to_le
      (sup_le (backwardSpan_le_Q p.color_a hb t)
        (geometry.V_le_Q (by omega) p.a p.color_a))).comap_subtype
  have hJ : ¬ J ≤ π.ker := by
    intro h
    apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    intro z hz
    have hz' := h (show (⟨z, hJG hz⟩ : S) ∈ J from hz)
    rw [initial.natural_section.module_section.projection_kernel] at hz'
    exact hz'
  have hc₀ : ⁅(backwardSpan geometry p.a t).subgroupOf S, J⁆ ≤ V₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hW₀G, map_subgroupOf_eq_of_le hJG]
    exact (endpoint_commutator_le_radius p (by omega) initial _ hW).trans p.radius_le_start
  have hc : ⁅W, J⁆ ≤ V₀ := by
    dsimp only [W]
    rw [subgroupOf_sup hW₀G hVG]
    exact commutator_join_normal_le_relative _ V₀ J hc₀
  have h := map_mono (f := S.subtype)
    (PairingControl.Geometry.LocalProducts.residual_commutator_bound π
      initial.natural_section.module_section.projection_surjective hker W V₀ J hpW hJ hc)
  dsimp only [W, V₀] at h
  simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
    map_subgroupOf_eq_of_le hVG, Vcirc, Ltilde, S] using h

/-- Restriction to W(t) retains the sharp residual range Vcirc_a. -/
theorem backwardSpan_residual_le_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔
      Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    ⁅backwardSpan geometry p.a t, Ltilde R p.a⁆ ≤ Vcirc R p.a :=
  (commutator_mono le_sup_left le_rfl).trans
    (backwardSpan_join_residual_le_relativeNormalizer source p hb initial t hat hgen hW)

/-- All three clauses for each individual product follow from a selected
edge with W(t) contained in the kernel two before the critical endpoint. -/
theorem products_of_selected_relativeNormalizer (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 4 < geometry.b R) (initial : InitialFacts p)
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔
      Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c)
    (d : Vertex R) (hd : (cosetGraph R).dist p.a d = 2)
    (hmove : p.a ∈ movingNeighbors geometry d) :
    V R d ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((V R d ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅V R d, Ltilde R p.a⁆ ≤ Vcirc R p.a := by
  have hres := individual_residual_le (by omega) p.color_a hat
    (backwardSpan_residual_le_relativeNormalizer source p hb initial t hat hgen hW) d hmove
  exact ⟨(product_le_Q p.color_a hb hd).trans (fun _ hx => hx.1),
    individual_product_normal source p.color_a hd hres, hres⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
