module

public import Stellmacher.SectionNine.DistanceOneAction
public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionNine.CubicLocalAction
public import Theory.GroupTheory.NormalizedSupCard


/-!
# The extracted product equals the exact terminal conjugate closure

Assume the actual distance-one extraction, faithful initial conclusion,
distinguished Sylow order128, the terminal SL2(2) core quotient, and the final
intersection identity of source(8). Then the extracted product is exactly
Vstar, the terminal conjugate closure of Z_a intersect Q_d. Normality of the
extracted product is proved here and is not an extra hypothesis.

The cubic local action of the terminal quotient gives an edge stabilizer of
order twice the core order. It is a two-group containing the distinguished
Sylow, hence equals that Sylow; the core therefore has order64. The elementary
initial center has order16 and meets the core in the order8 extracted coatom,
so their join is the whole Sylow. The core normalizes both extracted factors,
while the extracted group E normalizes their product and contains Z_a.
Consequently the Sylow normalizes the product. The actual E-and-edge generation
identity then makes it normal in the terminal stabilizer.

Normality bounds the terminal conjugate closure by the product. Conversely,
the second factor is the conjugate of the first by the supplied extraction
actor in the terminal stabilizer, so the product lies in the closure.
Source: Stellmacher(9.1), Journal of Algebra190 (1997), p.48, immediately before
part(c). The separate faithful/core producers supply the explicit local inputs.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
universe u

public theorem distance_one_extracted_product_eq_vstar_of_terminal_quotient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G→*H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneActionData ctx) (hTcard : Nat.card T=128)
    (hterminal : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hintersection : z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)=
      z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a') :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)=
      conjugateClosure (z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a')
        (stabilizer ctx.Γ ctx.criticalPath.a') := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length=1 := hb
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let C := Za⊓stabilizer Γ next
  let D := z Γ next⊓stabilizer Γ cp.a
  let V := C⊔D
  let Q := q Γ cp.a'
  let terminal := stabilizer Γ cp.a'
  have hfirst : cp.firstStep=cp.a' := by
    calc
      cp.firstStep=cp.path ⟨1,by omega⟩ := cp.path_first.symm
      _=cp.path ⟨cp.length,Nat.lt_succ_self _⟩ := by congr 1; exact Fin.ext hb.symm
      _=cp.a' := cp.path_end
  have hadj := cp.firstStep_adj
  rw [hfirst] at hadj
  have hsylow := SevenSix.edge_sylow_data ctx.sectionSeven Γ cp
  rw [hfirst] at hsylow
  have hTedge : T≤stabilizer Γ cp.a⊓terminal := le_inf hsylow.1.1 hsylow.2.1
  have hedge := (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a' hterminal).edge_card cp.a
    (Γ.adjacent_symm hadj)
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (q Γ cp.a')
    rw [q,Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  obtain ⟨k,hk⟩ := hQp.exists_card_eq
  have hedgep : IsPGroup 2 (stabilizer Γ cp.a⊓terminal : Subgroup G) := by
    apply IsPGroup.of_card (n:=k+1)
    rw [inf_comm]
    change Nat.card (terminal⊓stabilizer Γ cp.a : Subgroup G)=_ at hedge ⊢
    rw [hedge,hk,pow_succ,mul_comm]
  obtain ⟨hTterm,P,hP⟩ := hsylow.2
  have hedgeT : stabilizer Γ cp.a⊓terminal=T := by
    have hPle : (P:Subgroup terminal)≤(stabilizer Γ cp.a⊓terminal).subgroupOf terminal := by
      intro p hp
      apply hTedge
      rw [← hP]
      exact Subgroup.mem_map_of_mem _ hp
    have hPeq := P.is_maximal' (hedgep.comap_subtype) hPle
    change (stabilizer Γ cp.a⊓terminal).subgroupOf terminal=(P:Subgroup terminal) at hPeq
    calc
      stabilizer Γ cp.a⊓terminal = ((stabilizer Γ cp.a⊓terminal).subgroupOf terminal).map terminal.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
      _ = T := by rw [hPeq,hP]
  have hQcard : Nat.card Q=64 := by
    change Nat.card (terminal⊓stabilizer Γ cp.a : Subgroup G)=2*Nat.card Q at hedge
    rw [inf_comm,hedgeT,hTcard] at hedge
    omega
  have hQfirst : Q≤stabilizer Γ cp.a := by
    have hback : cp.a∈neighborhood Γ cp.a' := by
      rw [neighborhood,Γ.neighbors_def]
      exact cp.endpoint_distance.trans hb
    exact ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _ hback default).2.2
  have hQnorm : terminal≤Subgroup.normalizer (Q:Set G) := SevenSix.stabilizer_le_normalizer_q Γ cp.a'
  have hQmap : Q.map (MulAut.conj data.x).toMonoidHom=Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm data.x_mem)
  have hQnext : Q≤stabilizer Γ next := by
    change Q≤stabilizer Γ (Γ.act data.x⁻¹ cp.a)
    rw [stabilizer_act,inv_inv,← hQmap]
    exact Subgroup.map_mono hQfirst
  have hQV : Q≤Subgroup.normalizer (V:Set G) := by
    have hQC : Q≤Subgroup.normalizer (C:Set G) :=
      (le_inf (hQfirst.trans (stabilizer_le_normalizer_z Γ _))
        (hQnext.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hQD : Q≤Subgroup.normalizer (D:Set G) :=
      (le_inf (hQnext.trans (stabilizer_le_normalizer_z Γ _))
        (hQfirst.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hQC hQD).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C D)
  have hEV : data.E≤Subgroup.normalizer (V:Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans data.product_action)
  have hZaE : Za≤data.E := by rw [data.generated]; exact le_sup_left
  have hZaV := hZaE.trans hEV
  have hQT : Q≤T := by
    change q Γ cp.a'≤T
    rw [← hfirst]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hZaT : Za≤T := by
    have hn : cp.a'∈neighborhood Γ cp.a := by
      rw [neighborhood,Γ.neighbors_def]
      exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
    exact (((lemma_seven_three ctx.sectionSeven Γ).center_core _ _ hn).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))).trans
      (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hZaQnorm : Za≤Subgroup.normalizer (Q:Set G) := (hZaT.trans hTterm).trans hQnorm
  have hCcard : Nat.card (Za⊓Q : Subgroup G)=8 := by
    have h := data.coatom_card
    rw [data.coatom_stabilizer,hintersection] at h
    have hZa : Nat.card Za=16 := hfaith.1
    change Nat.card Za=2*Nat.card (Za⊓Q : Subgroup G) at h
    omega
  have hgenT : Za⊔Q=T := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hZaT hQT)
    have h := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Q Za hZaQnorm
    have hZa : Nat.card Za=16 := hfaith.1
    rw [hQcard,hZa,inf_comm Q Za,hCcard,sup_comm Q Za] at h
    rw [hTcard]
    omega
  have hTV : T≤Subgroup.normalizer (V:Set G) := hgenT ▸ sup_le hZaV hQV
  have hterminalV : terminal≤Subgroup.normalizer (V:Set G) := by
    have he : data.E⊔(stabilizer Γ cp.a⊓terminal)=terminal := data.edge_generated
    rw [← he]
    apply sup_le hEV
    change stabilizer Γ cp.a⊓terminal≤Subgroup.normalizer (V:Set G)
    rw [hedgeT]
    exact hTV
  change V=conjugateClosure (Za⊓Q) terminal
  have hCV : Za⊓Q≤V := hintersection.symm ▸ (show C≤V from le_sup_left)
  apply le_antisymm
  · apply sup_le
    · intro c hc
      exact Subgroup.subset_closure ⟨1,⟨c,hintersection ▸ hc⟩,by simp⟩
    · have hD := (distance_one_factor_transport ctx hb data.toDistanceOneExtractionData).1
      change C.map (MulAut.conj data.x).toMonoidHom=D at hD
      rw [← hD]
      rintro d ⟨c,hc,rfl⟩
      exact Subgroup.subset_closure ⟨⟨data.x,data.x_mem⟩,⟨c,hintersection ▸ hc⟩,rfl⟩
  · apply (Subgroup.closure_le V).mpr
    rintro v ⟨a,c,rfl⟩
    exact Subgroup.le_normalizer_iff.mp hterminalV a a.property c (hCV c.property)
end Stellmacher.SectionNine
