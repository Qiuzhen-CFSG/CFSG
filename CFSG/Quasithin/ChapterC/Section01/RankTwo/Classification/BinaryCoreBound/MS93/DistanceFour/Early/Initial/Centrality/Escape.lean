module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Offender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Extensions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer

/-!
# The final conjugate escape in MS93 (4.6.3)

For a noncentral radius-generator pair (delta, lambda) about alpha, assume
its index-four and intersection bounds and V_delta' = U_delta. The derived
equality transports to alpha. The critical commutator is a nontrivial
subgroup of U_alpha intersect U_delta, while the index-four bound puts this
intersection in the order-two group U_delta intersect Q_lambda. Consequently
U_alpha intersect U_delta has order two.

Apply (2.1)(vii) inside G_delta to Z_alpha Z_delta and this natural
intersection. Critical-path nonnormality handles the first subgroup, and
the actual natural action excludes normality of the second. Both are
normal in their common edge kernel. Conjugate generation is relative to
G_delta and uses the reversed critical pair.

For the single selected conjugator, write mu = alpha^g. The intersection
bound forces (mu, alpha) to be critical. Its nontrivial commutator lies in
the selected order-two intersection U_mu intersect U_delta, hence equals
it. But that commutator lies in Z_alpha and therefore centralizes Z_lambda,
contradicting the second escape clause.

The source uses Z_alpha intersect U_delta for the second subgroup. In this
binary proof its smaller natural intersection suffices, with its order and
all normality premises proved here. No selected witness, InitialFacts,
later centrality, or finiteness of the free amalgam is assumed. The parent
InitialFacts assembly must still supply the three explicit premises.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.3), printed pp.901--902, using (2.1)(vii) and (2.2)(v).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem small_natural_nonnormal
    (common : CommonFacts R source geometry) (d : Vertex R) (hd : color R d = false)
    (K : Subgroup (FreeAmalgam R)) (hKU : K ≤ U R d) (hK : Nat.card K = 2) :
    ¬ (K.subgroupOf (stabilizer R d)).Normal := by
  have hKG := hKU.trans ((U_le_Z d).trans (Z_le_stabilizer R d))
  intro hn
  let := finite_stabilizer R d
  let : (K.subgroupOf (stabilizer R d)).Normal := hn
  obtain ⟨frame⟩ := ModuleAlternatives.SourceCalculation.exists_frame d hd
  have hp : IsPGroup 2 (frame.projection source).ker := by
    rw [frame.projection_kernel source]
    exact (Q_isPGroup R source.two_group source.core_le d hd).comap_subtype
  have hz := Escape.Propagation.Backward.Moving.Symmetry.small_normal_centralizes_residual
    (frame.projection source) (frame.projection_surjective source) hp
    (K.subgroupOf (stabilizer R d)) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hKG).toEquiv, hK]
      decide)
  have hz' := congrArg (Subgroup.map (stabilizer R d).subtype) hz
  rw [map_commutator, map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] at hz'
  have hbot : K = ⊥ := le_bot_iff.mp (by
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) d hd]
    exact le_inf hKU (commutator_eq_bot_iff_le_centralizer.mp hz'))
  rw [hbot, card_bot] at hK
  omega

namespace NoncentralPair
variable {a d e : Vertex R}

private theorem natural_intersection_card (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (hindex : (Q R e).relIndex (Z R d) = 4)
    (hderived : ⁅V R d,V R d⁆ = U R d) :
    Nat.card (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) = 2 := by
  have hcrit := h.critical_pair common hb
  have hidx : (Q R e).relIndex (U R d) = 4 := by
    rw [← (naturalStructure common).critical_Z_index_eq_U geometry d h.color_d e hcrit]
    exact hindex
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Q R e ⊓ U R d) (U R d) bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hidx,
    common.natural.card_at d h.color_d] at hcard
  have hsmall : Nat.card (Q R e ⊓ U R d : Subgroup (FreeAmalgam R)) = 2 := by omega
  let := finite_stabilizer R d
  let : Finite (U R d) := Finite.of_injective
    (inclusion ((U_le_Z d).trans (Z_le_stabilizer R d))) (inclusion_injective _)
  let : Finite (Q R e ⊓ U R d : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  let : Finite (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  have haQ : Z R a ≤ Q R e := Z_le_Q_of_dist_lt R a
    (geometry.exists_critical a h.color_a) (by
      rw [geometry.distance_constant a h.color_a]
      change (cosetGraph R).dist a e < geometry.b R
      rw [SimpleGraph.dist_comm, h.dist_ea, hb]
      decide)
  have hupper : Nat.card (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) ≤ 2 :=
    (card_le_of_le (inf_le_inf_right (U R d) ((U_le_Z a).trans haQ))).trans_eq hsmall
  have hJa : ⁅Z R d,Z R e⁆ ≤ U R a := by
    rw [← radius_derived_eq_U_at_all d a h.color_d h.color_a hderived]
    exact commutator_mono
      (le_iSup_of_le d (le_iSup_of_le h.dist_da.le le_rfl))
      (le_iSup_of_le e (le_iSup_of_le h.dist_ea.le le_rfl))
  have hJd : ⁅Z R d,Z R e⁆ ≤ U R d := by
    rw [(naturalStructure common).critical_commutator_eq geometry d h.color_d e hcrit]
    exact le_normalizer_iff_commutator_le_left.mp
      (source.critical_U_mutually_normalize geometry d h.color_d e hcrit).2
  have hne : (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) ≠ ⊥ := by
    intro heq
    apply common.critical_noncommutation d h.color_d e hcrit
    exact le_bot_iff.mp (heq ▸ le_inf hJa hJd)
  have hlo := (U R a ⊓ U R d).one_lt_card_iff_ne_bot.mpr hne
  omega

private theorem simultaneous_natural_escape (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (hcard : Nat.card (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) = 2) :
    ∃ m, color R m = false ∧ (cosetGraph R).dist m d = 2 ∧
      Nat.card (U R m ⊓ U R d : Subgroup (FreeAmalgam R)) = 2 ∧
      ¬ Z R e ≤ normalizer (Z R m ⊔ Z R d : Subgroup (FreeAmalgam R)) ∧
      ¬ Z R e ≤ normalizer (U R m ⊓ U R d : Subgroup (FreeAmalgam R)) := by
  have hcrit := h.critical_pair common hb
  obtain ⟨t,hdt,hat⟩ := exists_common_neighbor_of_dist_two R d a h.dist_da
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hdt
    rw [h.color_d] at hn
    cases hh : color R t <;> simp_all
  have hTd : Q R t ≤ stabilizer R d := by rw [Q_h_eq_edge R ht hdt]; exact inf_le_left
  have hTa : Q R t ≤ stabilizer R a := by rw [Q_h_eq_edge R ht hat]; exact inf_le_left
  have hZt (c : Vertex R) (hc : color R c = false) (hct : Adjacent R c t) :
      Z R c ≤ Q R t :=
    (show Z R c ≤ Q R c by rw [← common.X_eq_Z c hc]; exact omegaCenter_le _).trans
      (Q_le_adjacent_h R ht hct)
  have hST : Z R a ⊔ Z R d ≤ Q R t := sup_le (hZt a h.color_a hat) (hZt d h.color_d hdt)
  have hKT : U R a ⊓ U R d ≤ Q R t := inf_le_left.trans ((U_le_Z a).trans (hZt a h.color_a hat))
  have hSN : Q R t ≤ normalizer (Z R a ⊔ Z R d : Subgroup (FreeAmalgam R)) :=
    (le_inf (hTa.trans (Z_normalized R a)) (hTd.trans (Z_normalized R d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hKN : Q R t ≤ normalizer (U R a ⊓ U R d : Subgroup (FreeAmalgam R)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_inf _ _ _ (MulAut.conj x).injective,
      mem_normalizer_iff_map_conj_eq.mp ((hTa.trans (U_normalized a)) hx),
      mem_normalizer_iff_map_conj_eq.mp ((hTd.trans (U_normalized d)) hx)]
  have hbpos : 0 < criticalDistance R d (geometry.exists_critical d h.color_d) := by
    rw [geometry.distance_constant d h.color_d]
    change 0 < geometry.b R
    omega
  have hpath : (cosetGraph R).dist a e + 2 = (cosetGraph R).dist d e := by
    rw [SimpleGraph.dist_comm (u := a) (v := e), h.dist_ea, hcrit.1,
      geometry.distance_constant d h.color_d]
    exact hb.symm
  have hnotS := (critical_nonnormal_reverse R geometry common.centralizer common.escape
    d h.color_d hbpos hcrit a h.dist_da hpath).2
  rw [common.X_eq_Z d h.color_d] at hnotS
  have hnotK := small_natural_nonnormal common d h.color_d _ inf_le_right hcard
  have heG : Z R e ≤ stabilizer R d :=
    (source.critical_Z_le_stabilizer geometry d h.color_d e hcrit).2
  have heout := (common.critical_reverse d h.color_d e h.color_e hcrit).2
  let N := NormalizerTransfer.conjugatesIn (Z R e) (stabilizer R d)
  have hNG : N ≤ stabilizer R d := NormalizerTransfer.conjugatesIn_le _ _ heG
  have heN : Z R e ≤ N := by
    intro x hx
    apply le_iSup (fun g : stabilizer R d => NormalizerTransfer.rightConjugate (Z R e) g) 1
    exact ⟨x,hx,by simp⟩
  have hLN : Ltilde R d ≤ N := NaturalStructure.Exclusion.residual_le_of_normal_not_le
    source d h.color_d N hNG
    (normal_subgroupOf_of_le_normalizer (NormalizerTransfer.conjugatesIn_normalized _ _))
    (fun hn => heout (heN.trans hn))
  have hgen : N ⊔ Q R t = stabilizer R d := by
    apply le_antisymm (sup_le hNG hTd)
    rw [← source.local_generation d h.color_d]
    exact sup_le (hLN.trans le_sup_left) ((Q_le_adjacent_h R ht hdt).trans le_sup_right)
  obtain ⟨g,hgd,hnS,hnK⟩ := source_2_1_vii R d e t h.color_d hdt
    (Z R a ⊔ Z R d) (U R a ⊓ U R d) hST hKT
    (normal_subgroupOf_of_le_normalizer hSN) (normal_subgroupOf_of_le_normalizer hKN)
    hnotS hnotK hgen
  have hfix : act R g d = d := hgd
  have hKmap : (U R a ⊓ U R d).map (MulAut.conj g⁻¹).toMonoidHom =
      U R (act R g a) ⊓ U R d := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, ← U_act, ← U_act, hfix]
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hfix] at hnS
  rw [hKmap] at hnK
  refine ⟨act R g a,by rw [action_preserves_color]; exact h.color_a,?_,?_,hnS,hnK⟩
  · rw [← hfix, dist_act, SimpleGraph.dist_comm]
    exact h.dist_da
  · rw [← hKmap, card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcard

/-- The final simultaneous-escape contradiction in the binary case of (4.6.3). -/
theorem false_of_index_intersection_derived (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (hindex : (Q R e).relIndex (Z R d) = 4)
    (hintersection : ⁅V R d ⊓ Q R a,Z R e⁆ ≤ Z R d)
    (hderived : ⁅V R d,V R d⁆ = U R d) : False := by
  have hcrit := h.critical_pair common hb
  have heG := (source.critical_Z_le_stabilizer geometry d h.color_d e hcrit).2
  obtain ⟨m,hm,hmd,hcard,hnS,hnK⟩ :=
    h.simultaneous_natural_escape common hb (h.natural_intersection_card common hb hindex hderived)
  have hmV : Z R m ≤ V R d := le_iSup_of_le m (le_iSup_of_le hmd.le le_rfl)
  have hout : ¬ Z R m ≤ Q R a := by
    intro hmQ
    apply hnS
    rw [sup_comm]
    exact Escape.PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le
      (Z R d) (Z R m) (Z R e)
      (heG.trans (Z_normalized R d))
      ((commutator_mono (le_inf hmV hmQ) le_rfl).trans hintersection)
  have hma : CriticalPair R m a (geometry.exists_critical m hm) := by
    refine ⟨le_antisymm ?_ (criticalDistance_le R m _ hout), hout⟩
    have htri := (cosetGraph_connected R).dist_triangle (u := m) (v := d) (w := a)
    rw [hmd,h.dist_da] at htri
    rw [geometry.distance_constant m hm]
    exact htri.trans_eq hb.symm
  have hnon := common.critical_noncommutation m hm a hma
  have hJU : ⁅Z R m,Z R a⁆ ≤ U R m := by
    rw [(naturalStructure common).critical_commutator_eq geometry m hm a hma]
    exact le_normalizer_iff_commutator_le_left.mp
      (source.critical_U_mutually_normalize geometry m hm a hma).2
  have hJD : ⁅Z R m,Z R a⁆ ≤ U R d := by
    rw [← hderived]
    exact commutator_mono hmV
      (le_iSup_of_le a (le_iSup_of_le (by rw [SimpleGraph.dist_comm]; exact h.dist_da.le) le_rfl))
  let : Finite (U R m ⊓ U R d : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite (⁅Z R m,Z R a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (le_inf hJU hJD)) (inclusion_injective _)
  have heq : ⁅Z R m,Z R a⁆ = U R m ⊓ U R d := by
    apply eq_of_le_of_card_ge (le_inf hJU hJD)
    have hlo := (⁅Z R m,Z R a⁆ : Subgroup (FreeAmalgam R)).one_lt_card_iff_ne_bot.mpr hnon
    omega
  have hJZ : ⁅Z R m,Z R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((source.critical_Z_le_stabilizer geometry m hm a hma).1.trans (Z_normalized R a))
  have heQ : Z R e ≤ Q R a := Z_le_Q_of_dist_lt R e
    (geometry.exists_critical e h.color_e) (by
      rw [geometry.distance_constant e h.color_e]
      change (cosetGraph R).dist e a < geometry.b R
      rw [h.dist_ea, hb]
      decide)
  apply hnK
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  rw [← heq]
  exact heQ.trans ((le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a h.color_a))).trans
    (centralizer_le hJZ))

end NoncentralPair
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
