module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralSection
public import Theory.Representation.BinaryConjugationSection.ElementaryQuotient
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The actual seed module at the start of 10.7

The core normalizes both radius/core factors of the source seed. Each
opposite critical center sends the seed into its own radius factor modulo
commutators, so the full local actor normalizes the seed. The earlier
7.4 commutator bound makes V_beta act quadratically on the elementary
seed quotient by the literal D_alpha.

The two quotient factors are disjoint because they lie in the two cores
whose intersection is D_alpha. Their product is the whole seed quotient.
The original opposite conjugator makes their indices equal, giving the
square-order formula. Conjugation coordinates are constructed on the
actual quotient; no action through SL2 or equality of the seed with
Q_alpha is assumed. Those are later obligations of the same source proof.
Source: DGS, Groups and Graphs (1985), proof of 10.7, pp.158--159.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

private theorem seed_core_normalized (x : Vertex F) :
    stabilizer F x ≤ normalizer (Q F x : Set G) :=
  (stabilizer F x).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The source seed is invariant under the actual local actor. Normalization
by the core is immediate; each critical center carries the other radius
factor into the first, while preserving D. -/
theorem BTwoOppositeGeometry.seed_normalized
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {t v m w z : Vertex F}
    (d : BTwoOppositeGeometry F t v m w z)
    (hactor : d.actor ≤ stabilizer F v) :
    d.actor ≤ normalizer (centralSeed F v m t : Set G) := by
  let A := V F m 1 ⊓ Q F v
  let C := V F t 1 ⊓ Q F v
  let J := centralSeed F v m t
  have hJQ : J ≤ Q F v := sup_le (sup_le inf_le_right inf_le_right) d.separated
  have hAJ : A ≤ J := le_sup_left.trans le_sup_left
  have hCJ : C ≤ J := le_sup_right.trans le_sup_left
  have hDJ : D F m t ≤ J := le_sup_right
  have hQA : Q F v ≤ d.actor := d.actor_generators ▸ le_sup_right
  have hQm : Q F v ≤ stabilizer F m :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F d.middle).trans inf_le_right)
  have hQt : Q F v ≤ stabilizer F t :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F d.previous.symm).trans inf_le_right)
  have hnormA : Q F v ≤ normalizer (A : Set G) :=
    (le_inf (hQm.trans (graph_stabilizer_normalizes_V h m 1))
      (Q F v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hnormC : Q F v ≤ normalizer (C : Set G) :=
    (le_inf (hQt.trans (graph_stabilizer_normalizes_V h t 1))
      (Q F v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hnormD := d.normalized h hS hb
  have hnormJ : Q F v ≤ normalizer (J : Set G) :=
    (le_inf ((le_inf hnormA hnormC).trans (normalizer_inf_normalizer_le_normalizer_sup A C))
      (hQA.trans hnormD)).trans (normalizer_inf_normalizer_le_normalizer_sup (A ⊔ C) (D F m t))
  have hgen (T : Subgroup G) (ha : ⁅A,T⁆ ≤ J) (hc : ⁅C,T⁆ ≤ J)
      (hd : ⁅D F m t,T⁆ ≤ J) : ⁅J,T⁆ ≤ J :=
    commutator_sup_le_of_relative_normal (Q F v) (A ⊔ C) (D F m t) T J
      hnormJ (sup_le inf_le_right inf_le_right) d.separated
      (commutator_sup_le_of_relative_normal (Q F v) A C T J hnormJ
        inf_le_right inf_le_right ha hc) hd
  have hWactor : Z F w ≤ d.actor := d.actor_generators ▸ le_sup_left.trans le_sup_left
  have hZactor : Z F z ≤ d.actor := d.actor_generators ▸ le_sup_right.trans le_sup_left
  have hWV : Z F w ≤ V F m 1 :=
    le_iSup_of_le w (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl d.terminal)) le_rfl)
  have hZV : Z F z ≤ V F t 1 :=
    le_iSup_of_le z (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl d.opposite)) le_rfl)
  have hpair (T : Subgroup G) (hT : T ≤ d.actor) (x : Vertex F)
      (hTx : T ≤ V F x 1) (hx : Q F v ≤ stabilizer F x)
      (U : Subgroup G) (hU : U ≤ Q F v) :
      ⁅U,T⁆ ≤ V F x 1 ⊓ Q F v := by
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono hTx le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hU.trans (hx.trans (graph_stabilizer_normalizes_V h x 1))))
    · exact (commutator_mono hU le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hT.trans (hactor.trans (seed_core_normalized v))))
  rw [d.actor_generators]
  apply sup_le (sup_le ?_ ?_) hnormJ
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact hgen _ ((hpair _ hWactor m hWV hQm A inf_le_right).trans hAJ)
      ((hpair _ hWactor m hWV hQm C inf_le_right).trans hAJ)
      ((le_normalizer_iff_commutator_le_left.mp (hWactor.trans hnormD)).trans hDJ)
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact hgen _ ((hpair _ hZactor t hZV hQt A inf_le_right).trans hCJ)
      ((hpair _ hZactor t hZV hQt C inf_le_right).trans hCJ)
      ((le_normalizer_iff_commutator_le_left.mp (hZactor.trans hnormD)).trans hDJ)

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The complete radius-one subgroup, not just its critical center, acts
quadratically on the seed modulo the literal D. -/
theorem BTwoCenterActionData.seed_quadratic_commutator
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hDQ : D F m t ≤ Q F v) (hZD : Z F m ≤ D F m t)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m) :
    ⁅V F m 1,⁅V F m 1,centralSeed F v m t⁆⁆ ≤ D F m t := by
  have hV := graph_V_le_Q_of_short h hS m (i := 1) (by rw [hb]; decide)
  have hJQ : centralSeed F v m t ≤ Q F v :=
    sup_le (sup_le inf_le_right inf_le_right) hDQ
  have hQm : Q F v ≤ stabilizer F m :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F c.middle).trans inf_le_right)
  have hc : ⁅V F m 1,centralSeed F v m t⁆ ≤ Q F m :=
    (le_normalizer_iff_commutator_le_left.mp
      (hJQ.trans (hQm.trans (graph_stabilizer_normalizes_V h m 1)))).trans hV
  exact ((commutator_mono le_rfl hc).trans hcomm).trans hZD

/-- The source seed has its genuine conjugation representation, with a
quadratic radius-one actor. The numerator has not yet been identified
with the whole core; no action of SL2 on this quotient is assumed. -/
theorem BTwoCenterActionData.central_seed_representation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m) :
    ∃ hN : ((D F m t).subgroupOf (centralSeed F v m t)).Normal,
      letI := hN
      ∃ hE : IsElementaryAbelian 2 (centralSeed F v m t ⧸
        (D F m t).subgroupOf (centralSeed F v m t)),
      letI := hE
      ∃ ρ : Representation (ZMod 2) c.actor (Additive (centralSeed F v m t ⧸
        (D F m t).subgroupOf (centralSeed F v m t))),
        Nonempty (Representation.BinaryConjugationSection c.actor
          (centralSeed F v m t) (D F m t) ρ) ∧
        Representation.BinaryOffender.IsQuadratic ρ ((V F m 1).subgroupOf c.actor) := by
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hnD := hd ▸ d.normalized h hS hb
  have hnJ := hd ▸ d.seed_normalized h hS hb (hd.symm ▸ c.actor_le)
  have hJQ : centralSeed F v m t ≤ Q F v :=
    sup_le (sup_le inf_le_right inf_le_right) d.separated
  have hZm := center_le_of_central_neighbor h hB hSyl c.middle hcentral
  have hZD : Z F v ≤ D F m t := (d.decomposition h hS hb) ▸ le_sup_left
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hSyl hb hactor hcentral ht hne hcomm
  refine ⟨hN,hE,?_⟩
  let := hN
  let := hE
  obtain ⟨ρ,⟨e⟩⟩ := Representation.BinaryConjugationSection.exists_elementary_quotient_coordinates
    c.actor (centralSeed F v m t) (D F m t) (hJQ.trans c.core_le) hnJ le_sup_right hnD
  refine ⟨ρ,⟨e⟩,?_⟩
  have hq := Representation.BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    c.actor (centralSeed F v m t) (D F m t) (V F m 1) ρ (MonoidHom.id c.actor) e
    (c.seed_quadratic_commutator h hS hb d.separated (hZm.trans hZD) hcomm)
  simpa only [Subgroup.map_id] using hq

/-- The two radius factors have disjoint images in the literal seed quotient
and generate it. This is the direct-product step of 10.7(b), before V=Q. -/
theorem bTwo_seed_quotient_factors
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) (v m t : Vertex F)
    [((D F m t).subgroupOf (centralSeed F v m t)).Normal]
    [IsElementaryAbelian 2 (centralSeed F v m t ⧸
      (D F m t).subgroupOf (centralSeed F v m t))] :
    let J := centralSeed F v m t
    let q := QuotientGroup.mk' ((D F m t).subgroupOf J)
    let A := ((V F m 1 ⊓ Q F v).subgroupOf J).map q
    let C := ((V F t 1 ⊓ Q F v).subgroupOf J).map q
    Disjoint A C ∧ ∃ e : A × C ≃* (J ⧸ (D F m t).subgroupOf J),
      ∀ a c, e (a,c) = (a : J ⧸ (D F m t).subgroupOf J) * c := by
  let J := centralSeed F v m t
  let q := QuotientGroup.mk' ((D F m t).subgroupOf J)
  let A₀ := V F m 1 ⊓ Q F v
  let C₀ := V F t 1 ⊓ Q F v
  let A := (A₀.subgroupOf J).map q
  let C := (C₀.subgroupOf J).map q
  have hAJ : A₀ ≤ J := le_sup_left.trans le_sup_left
  have hCJ : C₀ ≤ J := le_sup_right.trans le_sup_left
  have hDJ : D F m t ≤ J := le_sup_right
  have hAm : A₀ ≤ Q F m := inf_le_left.trans
    (graph_V_le_Q_of_short h hS m (by rw [hb]; decide))
  have hCt : C₀ ≤ Q F t := inf_le_left.trans
    (graph_V_le_Q_of_short h hS t (by rw [hb]; decide))
  have hd : Disjoint A C := by
    apply disjoint_def.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨c,hc,he⟩
    have hac : a*c⁻¹ ∈ q.ker := by
      change q (a*c⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hacD : ((a*c⁻¹ : J) : G) ∈ D F m t := by
      rw [QuotientGroup.ker_mk'] at hac
      exact hac
    have hat : (a : G) ∈ Q F t := by
      have hh : (a : G) * (c : G)⁻¹ * (c : G) ∈ Q F t :=
        (Q F t).mul_mem hacD.2 (hCt hc)
      simpa only [inv_mul_cancel_right] using hh
    exact (QuotientGroup.eq_one_iff a).mpr ⟨hAm ha,hat⟩
  have hgen : A ⊔ C = ⊤ := by
    have hDmap : ((D F m t).subgroupOf J).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    have hh := congrArg (fun U : Subgroup G => (U.subgroupOf J).map q)
      (show (A₀ ⊔ C₀) ⊔ D F m t = J from rfl)
    rw [subgroupOf_sup (sup_le hAJ hCJ) hDJ,subgroupOf_sup hAJ hCJ,
      Subgroup.map_sup,Subgroup.map_sup,hDmap,sup_bot_eq,subgroupOf_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hc : A ≤ centralizer (C : Set (J ⧸ (D F m t).subgroupOf J)) := by
    intro a _ c _
    exact mul_comm c a
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A C hd hc
  exact ⟨hd,e.trans ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv),he⟩

/-- Conjugation by the retained opposite lift gives equal orders for the
two quotient factors. Thus the seed quotient has the square of the literal
radius/core index, without substituting an unproved field parameter. -/
theorem BTwoCenterActionData.central_seed_card_square
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m) :
    ∃ hN : ((D F m t).subgroupOf (centralSeed F v m t)).Normal,
      letI := hN
      Nat.card (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t)) =
        (D F m t).relIndex (V F m 1 ⊓ Q F v) ^ 2 := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hnD : (D F m t).map (MulAut.conj (g : G)).toMonoidHom = D F m t :=
    mem_normalizer_iff_map_conj_eq.mp ((hd ▸ d.normalized h hS hb) g.property)
  have hmap : (V F m 1 ⊓ Q F v).map (MulAut.conj (g : G)).toMonoidHom =
      V F t 1 ⊓ Q F v := by
    rw [map_inf _ _ _ (MulAut.conj (g : G)).injective,←V_translate,←Q_translate,hg,hgv]
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) (D F m t) (V F m 1 ⊓ Q F v)
    (MulAut.conj (g : G)).injective
  rw [hnD,hmap] at hi
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hSyl hb hactor hcentral ht hne hcomm
  refine ⟨hN,?_⟩
  let := hN
  let := hE
  let J := centralSeed F v m t
  let q := QuotientGroup.mk' ((D F m t).subgroupOf J)
  obtain ⟨_,e,_⟩ := bTwo_seed_quotient_factors h hS hb v m t
  have hA := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
    J (D F m t) (V F m 1 ⊓ Q F v) q (QuotientGroup.ker_mk' _)
    (le_sup_left.trans le_sup_left)
  have hC := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
    J (D F m t) (V F t 1 ⊓ Q F v) q (QuotientGroup.ker_mk' _)
    (le_sup_right.trans le_sup_left)
  change Nat.card (J ⧸ (D F m t).subgroupOf J) = _
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hA,hC,hi,pow_two]


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
