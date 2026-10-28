module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.MovingActor

/-!
# The strict residual-section index in DGS 8.4

For W = V_beta^(3), put D = (W intersect Q_alpha') V_beta. Criticality
makes V_beta escape Q_alpha', so adjoining V_beta strictly decreases the
index relative to W intersect Q_alpha'. The first marked omega placement
bounds the latter index by the order of the terminal Sylow omega-center.
This proves the strict source bound with the original quotient map.

The radius-one subgroup and D are normal in W, as required to form the
literal residual sections. The argument works for every b > 3, including
b = 5, and uses no exponent assumption on W or its core intersection.
The second omega placement and the residual-action contradiction are
separate obligations.

Source: DGS, *Groups and Graphs* (1985), paragraph after 8.4(3), printed p.138.
`RadiusThreeIntersectionApplication` gives the reduced F1.11 consumer.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem strict_residual_index (W K E : Subgroup G) [Finite W]
    (hEW : E ≤ W) (hne : ¬ E ≤ K) :
    ((W ⊓ K) ⊔ E).relIndex W < K.relIndex W := by
  have hstrict : (W ⊓ K).subgroupOf W < ((W ⊓ K) ⊔ E).subgroupOf W := by
    refine lt_of_le_of_ne (subgroupOf_mono W le_sup_left) ?_
    intro he
    apply hne
    intro x hx
    have hxD : (⟨x,hEW hx⟩ : W) ∈ ((W ⊓ K) ⊔ E).subgroupOf W := (show E ≤ (W ⊓ K) ⊔ E from le_sup_right) hx
    rw [←he] at hxD
    exact hxD.2
  have hi := Subgroup.index_strictAnti hstrict
  change ((W ⊓ K) ⊔ E).relIndex W < (W ⊓ K).relIndex W at hi
  simpa only [inf_relIndex_left] using hi

private theorem radius_three_index_bound
    (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (R : Sylow 2 (d.localGroup a'))
    (hW : V (family P) beta 3 ≤ quotientSylowOmegaPreimage (d.localGroup a') R) :
    ((V (family P) beta 3 ⊓ Q (family P) a') ⊔ V (family P) beta 1).relIndex
        (V (family P) beta 3) <
      Nat.card (omegaCenterIn ((R : Subgroup (d.localGroup a')).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a'))))) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  let W := V F beta 3
  let q := QuotientGroup.mk' (pCore 2 L)
  have hWL : W ≤ L := hW.trans (map_subtype_le _)
  let : Finite W := Finite.of_injective (inclusion hWL) (inclusion_injective _)
  have he : ¬ V F beta 1 ≤ Q F a' := by
    intro hh
    exact hc.2 ((Z_neighbor_le_V F hab.symm).trans (hh.trans (source_Z_Q_U h a').2))
  have hi := strict_residual_index W (Q F a') (V F beta 1) (V_mono F beta (by decide)) he
  have hmap : (W.subgroupOf L).map q ≤ omegaCenterIn ((R : Subgroup L).map q) := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨z,hz,he⟩ := hW hy
    exact (Subtype.ext he : z = y) ▸ hz
  have hk : q.ker = (Q F a').subgroupOf L :=
    local_quotient_kernel F d a' (MulEquiv.refl _)
  have hcard := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
    L (Q F a') W q hk hWL
  apply hi.trans_le
  rw [←hcard]
  exact Nat.card_le_card_of_injective (inclusion hmap) (inclusion_injective _)


/-- The actual residual denominator in 8.4 has index strictly below the
marked terminal omega-center. Its normality is relative to W. -/
theorem source_radius_three_section_index (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer
        ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 3 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    let F := family P
    let W := V F beta 3
    ∃ (prev : Vertex F) (R : Sylow 2 (d.localGroup a')),
      (graph F).Adj a' prev ∧
      (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
      W ≤ Q F prev ∧
      (R : Subgroup (d.localGroup a')).map (d.localGroup a').subtype =
        (stabilizer F a' ⊓ stabilizer F prev).pCoreIn 2 ∧
      W ≤ quotientSylowOmegaPreimage (d.localGroup a') R ∧
      ((V F beta 1).subgroupOf W).Normal ∧
      (((W ⊓ Q F a') ⊔ V F beta 1).subgroupOf W).Normal ∧
      ((W ⊓ Q F a') ⊔ V F beta 1).relIndex W <
        Nat.card (omegaCenterIn ((R : Subgroup (d.localGroup a')).map
          (QuotientGroup.mk' (pCore 2 (d.localGroup a'))))) := by
  let := finite_endpoints h
  let F := family P
  let W := V F beta 3
  obtain ⟨prev,R,hprev,hdprev,hWprev,hR,hWO⟩ :=
    source_radius_three_omega h hB d hob models hc hab hd hb hcomm hne
  have hWL : W ≤ d.localGroup a' := hWO.trans (map_subtype_le _)
  have hWQ : W ≤ Q F beta := V_le_Q_of_dist_add_lt_b F h.generate
    (fun v => (source_Z_Q_U h v).1) beta beta 3
    (by simpa only [SimpleGraph.dist_self,zero_add] using hb) (d.kernel_sylow beta)
  have hWNQ : W ≤ normalizer (Q F a' : Set G) :=
    (hWL.trans (d.local_le a')).trans (stabilizer_normalizes_Q F a')
  have hWNA : W ≤ normalizer ((W ⊓ Q F a' : Subgroup G) : Set G) :=
    (le_inf W.le_normalizer hWNQ).trans inf_normalizer_le_normalizer_inf
  have hWNV : W ≤ normalizer (V F beta 1 : Set G) :=
    (hWQ.trans (Q_le_stabilizer F beta)).trans (stabilizer_normalizes_V F beta 1)
  have hVW : V F beta 1 ≤ W := V_mono F beta (by decide)
  refine ⟨prev,R,hprev,hdprev,hWprev,hR,hWO,
    (normal_subgroupOf_iff_le_normalizer hVW).mpr hWNV,
    (normal_subgroupOf_iff_le_normalizer (sup_le inf_le_left hVW)).mpr ?_,
    radius_three_index_bound h d hc hab R hWO⟩
  exact (le_inf hWNA hWNV).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
