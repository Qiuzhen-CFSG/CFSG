module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure

/-!
# Collapse of the D span in MS93 (4.5.3)(i)

The fixed seed is the centralizer of the local residual in the full radius
V at the preceding vertex. Its right-conjugate span uses the literal
relative normalizer, not the edge stabilizer. The third printed containment
makes DZ normal in the whole local group. Its commutator with Q is then an
invariant subgroup of the natural eight-group, contained in an H of order
at most four, and hence trivial. The involutions in the seed therefore lie
in Z. The common-edge intersection finishes the hat-layer identity once
the preceding decomposition and span estimates are supplied.

The path applications discharge all geometric and generation premises on
the supplied path and retain the exact ordered setwise products. The
representation-theoretic decomposition and the three D containments remain
independent source obligations; this module does not assert their existence.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.5.3)(i), printed pp.897--898, especially the second paragraph
of p.898. The natural-subgroup argument uses the marked NaturalFactor API.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity
open PathCentrality NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The printed D₀ = C_{V_b}(Ltilde_b), with no hat on V. -/
noncomputable def fixedSeed (R : Subgroup M) (b : Vertex R) : Subgroup (FreeAmalgam R) :=
  V R b ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R))

/-- The printed D, using right conjugation by N_{G_a}(Q_t). -/
noncomputable def normalizerSpan (R : Subgroup M) (a b t : Vertex R) :
    Subgroup (FreeAmalgam R) := conjugatesIn (fixedSeed R b) (relativeNormalizer R a t)

/-- The identity conjugator includes the original seed in D. -/
theorem fixedSeed_le_span (a b t : Vertex R) : fixedSeed R b ≤ normalizerSpan R a b t := by
  intro x hx
  apply (le_iSup (fun g : relativeNormalizer R a t => rightConjugate (fixedSeed R b) g) 1)
  exact ⟨x, hx, by simp⟩

/-- Normality is relative to the actual source actor. -/
theorem span_normalized (a b t : Vertex R) :
    relativeNormalizer R a t ≤ normalizer (normalizerSpan R a b t) :=
  conjugatesIn_normalized _ _

private theorem span_le_of_normalized {A P K : Subgroup (FreeAmalgam R)}
    (hA : A ≤ K) (hn : P ≤ normalizer K) : conjugatesIn A P ≤ K := by
  apply iSup_le
  intro g
  rintro _ ⟨x, hx, rfl⟩
  exact le_normalizer_iff.mp hn g⁻¹ (P.inv_mem g.property) x (hA hx)

/-- The distance-two configuration places D in the central kernel. -/
theorem span_le_Q [Finite M]
    (earlier : Earlier R geometry) {a b t : Vertex R}
    (hb : color R b = false) (hba : (cosetGraph R).dist b a = 2) :
    normalizerSpan R a b t ≤ Q R a := by
  apply span_le_of_normalized
  · exact (show fixedSeed R b ≤ V R b from inf_le_left).trans
      (V_le_Q_of_dist_add_two_lt R hb (by rw [hba, earlier.distance]; decide))
  · exact (show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans
      (Q_normalized R a)

/-- Residual-fixed elements lie in the genuine quotient-fixed preimage. -/
theorem fixedSeed_le_B [Finite M] (common : CommonFacts R source geometry)
    {b : Vertex R} (hb : color R b = false) :
    fixedSeed R b ≤ B R b (geometry.Z_normal b) := by
  intro x hx
  apply (mem_B_iff R b (geometry.Z_normal b)
    ((V_le_Q R hb common.large_distance).trans (fun _ hy => hy.1)) x).mpr
  refine ⟨hx.1, ?_⟩
  intro l hl
  have hc := hx.2 l hl
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact (Z R b).one_mem

private theorem normalizes_commutator {G : Type*} [Group G] (S A B : Subgroup G)
    (hA : S ≤ normalizer A) (hB : S ≤ normalizer B) :
    S ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hg),
    mem_normalizer_iff_map_conj_eq.mp (hB hg)]

private theorem commutator_sup_central {G : Type*} [Group G] (A C Q : Subgroup G)
    (hA : A ≤ Q) (hC : C ≤ Q) (hc : ⁅C,Q⁆ = ⊥) : ⁅A ⊔ C,Q⁆ = ⁅A,Q⁆ := by
  let f : Bool → Subgroup G := fun b => if b then A else C
  have hf : (⨆ b, f b) = A ⊔ C := by simp [iSup_bool_eq, f]
  have h := commutator_iSup_of_le f Q (by intro b; cases b <;> assumption)
  rw [hf] at h
  simpa [iSup_bool_eq, f, hc] using h

private theorem natural_subgroup_dichotomy [Finite M]
    (common : CommonFacts R source geometry) {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R a)
    (hn : stabilizer R a ≤ normalizer K) : K = ⊥ ∨ K = U R a := by
  obtain ⟨model⟩ := localModel_nonempty source (LocalCommutator.moduleFacts common) a ha
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z R a).trans (Z_le_stabilizer R a)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor model.projection ⊤ ((U R a).subgroupOf S) ⊥ := {
    marking := MulEquiv.refl _
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized a g.property
    action := by
      intro g _ x y h
      exact congrArg Multiplicative.toAdd (model.action g
        ((subgroupOfEquivOfLe hUS) x) ((subgroupOfEquivOfLe hUS) y)
        (congrArg Subtype.val h)) }
  have hm : (⊤ : Subgroup S).map model.projection = ⊤ :=
    map_top_of_surjective _ model.surjective
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh

private theorem span_join_Z_normalized [Finite M]
    {a b t f : Vertex R} (hf : color R f = false)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hproduct : (normalizerSpan R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    stabilizer R a ≤ normalizer (normalizerSpan R a b t ⊔ Z R a : Subgroup (FreeAmalgam R)) := by
  let D := normalizerSpan R a b t
  let J := D ⊔ Z R a
  have hZG : Z R f ≤ stabilizer R a := le_sup_right.trans hgen.le
  rw [← hgen]
  apply sup_le
  · exact (le_inf (span_normalized a b t)
      ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans
        (Z_normalized R a))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    have hn := Z_normalized R a (hZG hg)
    have hmap : J.map (MulAut.conj g).toMonoidHom ≤ J := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨d, hd, rfl⟩
        obtain ⟨z, hz, q, hq, heq⟩ := hproduct hd
        have hqJ : q ∈ J := by
          have hh := J.mul_mem (J.inv_mem (mem_sup_right hz)) (mem_sup_left hd)
          rw [← heq] at hh
          simpa only [inv_mul_cancel_left] using hh
        have hqfix : g * q * g⁻¹ = q := by
          have hc := (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R f hf)) hg q hq
          rw [← hc]
          simp [mul_assoc]
        change g * d * g⁻¹ ∈ J
        rw [← heq]
        have he : g * (z * q) * g⁻¹ = (g * z * g⁻¹) * q := by
          calc
            _ = (g * z * g⁻¹) * (g * q * g⁻¹) := by group
            _ = _ := by rw [hqfix]
        rw [he]
        exact J.mul_mem (mem_sup_right (le_normalizer_iff.mp (Z_normalized R a)
          g (hZG hg) z hz)) hqJ
      · exact (mem_normalizer_iff_map_conj_eq.mp hn).le.trans le_sup_right
    exact hmap (mem_map_of_mem _ hx)

/-- The last paragraph of the D argument: the third containment and the
small commutator force the actual conjugate span into Z at the center. -/
theorem span_le_Z_of_product [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hsmall : ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b)
    (hproduct : (normalizerSpan R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    normalizerSpan R a b t ≤ Z R a := by
  let D := normalizerSpan R a b t
  have hDQ : D ≤ Q R a := span_le_Q earlier hb hmove.1
  have hZQ : Z R a ≤ Q R a := by rw [← common.X_eq_Z a ha]; exact omegaCenter_le _
  have hnorm : stabilizer R a ≤ normalizer (⁅D,Q R a⁆ : Subgroup (FreeAmalgam R)) := by
    have hn := normalizes_commutator (stabilizer R a) (D ⊔ Z R a) (Q R a)
      (span_join_Z_normalized hf hgen hproduct) (Q_normalized R a)
    rwa [commutator_sup_central D (Z R a) (Q R a) hDQ hZQ (Z_centralizes_Q R a ha)] at hn
  have hHU : H R b ≤ U R a := H_le_neighbor_U common earlier hb hmove
  have hzero : ⁅D,Q R a⁆ = ⊥ := by
    rcases natural_subgroup_dichotomy common ha _ (hsmall.trans hHU) hnorm with h | h
    · exact h
    · have hcard := H_card_le_four common earlier hb
      let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
      let : Finite (H R b) := Finite.of_injective (inclusion hHU) (inclusion_injective hHU)
      have hle : Nat.card (U R a) ≤ Nat.card (H R b) := Nat.card_le_card_of_injective _ (inclusion_injective (h ▸ hsmall))
      rw [common.natural.card_at a ha] at hle
      omega
  have hseed : fixedSeed R b ≤ Z R a := by
    rw [← common.X_eq_Z a ha]
    let := V_elementary_of_four_lt R hb (by rw [earlier.distance]; decide)
    intro x hx
    have hxD := fixedSeed_le_span a b t hx
    exact mem_omegaCenter_iff.mpr ⟨hDQ hxD,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V R b) x hx.1,
      commutator_eq_bot_iff_le_centralizer.mp hzero hxD⟩
  exact span_le_of_normalized hseed
    ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans (Z_normalized R a))


private theorem inf_eq_of_index_two {G : Type*} [Group G] {A B E : Subgroup G}
    (hEA : E ≤ A) (hEB : E ≤ B) (hi : E.relIndex A = 2) (hn : ¬ A ≤ B) :
    A ⊓ B = E := by
  have hEI : E ≤ A ⊓ B := le_inf hEA hEB
  have hiI := relIndex_mul_relIndex E (A ⊓ B) A hEI inf_le_left
  rw [hi] at hiI
  have hdiv : (A ⊓ B).relIndex A ∣ 2 :=
    ⟨E.relIndex (A ⊓ B), by rw [mul_comm]; exact hiI.symm⟩
  have htwo : (A ⊓ B).relIndex A = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdiv with h | h
    · exact (hn ((relIndex_eq_one.mp h).trans inf_le_right)).elim
    · exact h
  rw [htwo] at hiI
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hEI

/-- A moving neighbor meets the fixed preimage in precisely the common edge layer. -/
theorem moving_Z_inf_B [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b) :
    Z R a ⊓ B R b (geometry.Z_normal b) = Z R t :=
  inf_eq_of_index_two (Escape.EdgeTransfer.edge_Z_le a t ha hat)
    ((Escape.EdgeTransfer.edge_Z_le b t hb hbt).trans
      (Escape.EdgeTransfer.Z_le_B common.large_distance b hb))
    (earlier.edge_Z_index a t ha hat) hmove.2

/-- The closing source implication retains D₀, the actual relative actor and
its ordered product with the distant kernel. The splitting and D estimates
are explicit earlier steps, not a completed proof of (4.5.3)(i). -/
theorem hat_eq_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hsplit : hatV R b a ≤ Vcirc R b ⊔ fixedSeed R b)
    (hsmall : ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b)
    (hproduct : (normalizerSpan R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    hatV R b a = Vcirc R b ⊔ Z R b := by
  have hDZ := span_le_Z_of_product common earlier ha hb hf hmove hgen hsmall hproduct
  have hseed : fixedSeed R b ≤ Z R b := by
    have h := le_inf ((fixedSeed_le_span a b t).trans hDZ) (fixedSeed_le_B common hb)
    rw [moving_Z_inf_B common earlier ha hb hat hbt hmove] at h
    exact h.trans (Escape.EdgeTransfer.edge_Z_le b t hb hbt)
  apply le_antisymm (hsplit.trans (sup_le_sup_left hseed _))
  exact sup_le (moving_le_hatV source earlier hb hmove) (Z_le_hatV hb hmove.1)

/-- The exact supplied-path application at alpha-minus-two. Both (4.5.2)
and all geometric hypotheses are discharged; only the three indicated
steps of the D calculation remain explicit. -/
theorem preceding_hat_eq_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (hsplit : hatV R (p.walk.getVert 2) a ≤
      Vcirc R (p.walk.getVert 2) ⊔ fixedSeed R (p.walk.getVert 2))
    (hsmall : ⁅normalizerSpan R a (p.walk.getVert 2) (p.walk.getVert 3), Q R a⁆ ≤
      H R (p.walk.getVert 2))
    (hproduct : (normalizerSpan R a (p.walk.getVert 2) (p.walk.getVert 3) :
      Set (FreeAmalgam R)) ⊆ (Z R a : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert 12) : Set (FreeAmalgam R))) :
    hatV R (p.walk.getVert 2) a = Vcirc R (p.walk.getVert 2) ⊔ Z R (p.walk.getVert 2) := by
  have ha : color R a = false := by
    simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide)
  apply hat_eq_of_calculations common earlier ha
    (p.even_color (i := 2) (by decide) (by decide))
    (p.even_color (i := 12) (by decide) (by decide))
  · simpa only [show 3 + 1 = 4 by decide, p.center_eq] using
      adjacent_symm R (p.adjacent (i := 3) (by decide))
  · exact p.adjacent (i := 2) (by decide)
  · simpa only [show 2 + 2 = 4 by decide, p.center_eq] using
      (p.moving_neighbors source common earlier (i := 2) (by decide) (by decide) (by decide)).2
  · simpa only [p.center_eq] using forward_generation common earlier p
      (firstFactsOnPath source common earlier p) (i := 4) (by decide) (by decide) (by decide)
  · exact hsplit
  · exact hsmall
  · exact hproduct


/-- Shift the D calculation two positions along the same path to obtain
both central source conclusions, including the literal ordered product. -/
theorem center_hat_eq_and_product_of_calculations [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (hsplit : hatV R a (p.walk.getVert 6) ≤ Vcirc R a ⊔ fixedSeed R a)
    (hsmall : ⁅normalizerSpan R (p.walk.getVert 6) a (p.walk.getVert 5),
      Q R (p.walk.getVert 6)⁆ ≤ H R a)
    (hproduct : (normalizerSpan R (p.walk.getVert 6) a (p.walk.getVert 5) :
      Set (FreeAmalgam R)) ⊆ (Z R (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert 14) : Set (FreeAmalgam R))) :
    hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a ∧
      (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) =
        (Vcirc R a : Set (FreeAmalgam R)) * (Z R a : Set (FreeAmalgam R)) := by
  have ha : color R a = false := by
    simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide)
  have heq : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a := by
    apply hat_eq_of_calculations common earlier
      (p.even_color (i := 6) (by decide) (by decide)) ha
      (p.even_color (i := 14) (by decide) (by decide))
    · exact adjacent_symm R (p.adjacent (i := 5) (by decide))
    · simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
    · simpa only [p.center_eq] using
        (p.moving_neighbors source common earlier (i := 4) (by decide) (by decide) (by decide)).2
    · exact forward_generation common earlier p (firstFactsOnPath source common earlier p)
        (i := 6) (by decide) (by decide) (by decide)
    · exact hsplit
    · exact hsmall
    · exact hproduct
  exact ⟨heq, hatV_product_of_eq common ha heq⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity
