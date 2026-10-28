module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition

/-!
# Faithfulness on the literal local-span head

Let H be the G_c-conjugate span of Z_a. If [H,Ltilde_c] lies in Z_c,
local generation gives H = Z_a Z_c. Consequently [Z_a,Q_c] = [H,Q_c]
is normal in G_c. The kernel Q_a centralizes this displacement, and escapes
Q_c when the displacement is not contained in D_c. Simplicity of the actual
SL₃(2) quotient then makes Ltilde_c centralize the displacement, a contradiction.

The supplied triple bound puts [Z_c[H,Q_c],Ltilde_c] in Z_c. Two-residual
commutator idempotence therefore preserves nontriviality in H/(Z_c[H,Q_c]).
The literal quotient-conjugation formula and simplicity prove faithfulness.
No comparison with the whole radius head or later natural section is used.

The final application discharges the faithfulness premise of the existing
recognition consumer. The marked configuration and displacement transfer
remain with their independent producers and the realization assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.6), printed pp.845--847, and its application in (4.4.1)(2), p.891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem normalizes_sup {G : Type*} [Group G] (S A C : Subgroup G)
    (hA : S ≤ normalizer A) (hC : S ≤ normalizer C) :
    S ≤ normalizer (A ⊔ C : Subgroup G) :=
  (le_inf hA hC).trans (normalizer_inf_normalizer_le_normalizer_sup A C)

private theorem normalizes_commutator {G : Type*} [Group G] (S A C : Subgroup G)
    (hA : S ≤ normalizer A) (hC : S ≤ normalizer C) :
    S ≤ normalizer (⁅A,C⁆ : Subgroup G) := by
  intro s hs
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hs),
    mem_normalizer_iff_map_conj_eq.mp (hC hs)]

private theorem span_eq_join_of_moving_le_Z (source : LocalSource L R)
    (a c : Vertex R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hfixed : ⁅localZSpan R a c, Ltilde R c⁆ ≤ Z R c) :
    localZSpan R a c = Z R a ⊔ Z R c := by
  have hZH := center_Z_le_span (R := R) hc hd
  have hWH : Z R a ⊔ Z R c ≤ localZSpan R a c :=
    sup_le (Z_le_localZSpan R a c) hZH
  have hQ : Q R c ≤ stabilizer R a := Q_le_stabilizer_of_dist_two R c a hc
    (by rwa [SimpleGraph.dist_comm])
  have hn : stabilizer R c ≤ normalizer (Z R a ⊔ Z R c : Subgroup (FreeAmalgam R)) := by
    rw [← source.local_generation c hc]
    exact sup_le
      (le_normalizer_iff_commutator_le_left.mpr
        (((commutator_mono hWH le_rfl).trans hfixed).trans le_sup_right))
      (normalizes_sup _ _ _ (hQ.trans (Z_normalized R a))
        ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (Z_normalized R c)))
  apply le_antisymm ?_ hWH
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  have hg := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R c).inv_mem g.property))
  exact (map_mono (show Z R a ≤ Z R a ⊔ Z R c from le_sup_left)).trans hg.le

private theorem residual_le_of_normal_escaping
    {G : Type*} [Group G] (π : G →* SL) (hπ : Function.Surjective π)
    (P N : Subgroup G) [N.Normal] (hker : π.ker = P) (hP : IsPGroup 2 P)
    (hout : ¬ N ≤ P) : pResidual 2 G ≤ N := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have ht : N.map π = ⊤ := by
    rcases (Normal.map (inferInstance : N.Normal) π hπ).eq_bot_or_eq_top with hz | ht
    · exact (hout (hker ▸ (map_eq_bot_iff N).mp hz)).elim
    · exact ht
  have hgen : N ⊔ P = ⊤ := by
    have hh := congrArg (Subgroup.comap π) ht
    simpa only [comap_map_eq, hker, comap_top] using hh
  exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N P hP hgen⟩

/-- A displacement escaping D_c forces nontrivial residual action on the
actual G_c-conjugate span modulo Z_c. This uses only the earlier local geometry. -/
theorem span_moving_not_le_Z (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ¬ ⁅localZSpan R a c, Ltilde R c⁆ ≤ Z R c := by
  intro hfixed
  let S := stabilizer R c
  let A := ⁅Z R a, Q R c⁆
  have hQcGa : Q R c ≤ stabilizer R a :=
    Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])
  have hQaS : Q R a ≤ S := Q_le_stabilizer_of_dist_two R a c ha hd
  have hAZa : A ≤ Z R a :=
    le_normalizer_iff_commutator_le_left.mp (hQcGa.trans (Z_normalized R a))
  have hAQ : A ≤ Q R c :=
    (commutator_mono (Z_le_localZSpan R a c) le_rfl).trans
      ((span_commutator_le_span a c).trans (localZSpan_le_Q R hc hd.le hb))
  have hAS : A ≤ S := hAQ.trans (fun _ hx => hx.1)
  let : Finite S := finite_stabilizer R c
  let : Finite (Q R c) := Finite.of_injective
    (inclusion (show Q R c ≤ S from fun _ hx => hx.1)) (inclusion_injective _)
  have hQaOut : ¬ Q R a ≤ Q R c := by
    intro hle
    have hEq : Q R a = Q R c := eq_of_le_of_card_ge hle
      (by rw [source.Q_card a ha, source.Q_card c hc])
    apply hn
    rw [← hEq, geometry.centralizes a ha]
    exact bot_le
  have hcomm : ⁅localZSpan R a c, Q R c⁆ = A := by
    have he := commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (span_eq_join_of_moving_le_Z source a c hc hd hfixed).symm)
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc))
      (((Z_le_localZSpan R a c).trans (localZSpan_le_Q R hc hd.le hb)).trans
        (Q R c).le_normalizer)
    rw [commutator_comm, ← he, commutator_comm]
  have hAn : S ≤ normalizer (A : Set (FreeAmalgam R)) := by
    rw [← hcomm]
    exact normalizes_commutator _ _ _ (localZSpan_normalized R a c) (Q_normalized R c)
  let A₀ := A.subgroupOf S
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hAn
  let C := centralizer (A₀ : Set S)
  have hQaC : (Q R a).subgroupOf S ≤ C := by
    intro q hq z hz
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
      (hAZa hz) q hq).symm
  have hCout : ¬ C ≤ localKernel c := by
    intro hC
    apply hQaOut
    intro q hq
    exact hC (hQaC (show (⟨q, hQaS hq⟩ : S) ∈ (Q R a).subgroupOf S from hq))
  have hLC : pResidual 2 S ≤ C := residual_le_of_normal_escaping
    (localProjection source c hc) (localProjection_surjective source c hc)
    (localKernel c) C (localProjection_kernel source c hc)
    (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype hCout
  apply hn
  refine le_inf hAQ ?_
  intro z hz l hl
  obtain ⟨lS, hlS, rfl⟩ := hl
  have he := hLC hlS (⟨z, hAS hz⟩ : S) hz
  exact (congrArg Subtype.val he).symm

private theorem span_local_moving_not_le_Z (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ¬ ⁅localSpan a c, pResidual 2 (stabilizer R c)⁆ ≤ Escape.Initial.Natural.Splitting.localZ c := by
  intro h
  apply span_moving_not_le_Z source geometry hb ha hc hd hn
  have hh := map_mono (f := (stabilizer R c).subtype) h
  rwa [map_commutator,
    map_subgroupOf_eq_of_le ((localZSpan_le_Q R hc hd.le hb).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R c)] at hh

private theorem span_commutator_le_radical_of_head_trivial (source : LocalSource L R)
    (geometry : Geometry R) (a c : Vertex R) (hc : color R c = false)
    (htriv : (spanHeadAction source geometry a c hc).ker = ⊤) :
    ⁅localSpan a c, (⊤ : Subgroup (stabilizer R c))⁆ ≤ spanRadical a c := by
  let := spanRadical_normal geometry a c
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g _ v hv
  have hg : spanHeadAction source geometry a c hc (localProjection source c hc g) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [htriv]
    trivial
  have he := spanHeadAction_apply source geometry a c hc g ⟨v, hv⟩
  rw [hg] at he
  let w : localSpan a c := ⟨g * v * g⁻¹,
    (inferInstance : (localSpan a c).Normal).conj_mem v hv g⟩
  have hh : w / ⟨v, hv⟩ ∈ (spanHeadProjection geometry a c).ker := by
    change spanHeadProjection geometry a c (w / ⟨v, hv⟩) = 1
    rw [map_div]
    change spanHeadProjection geometry a c
      ⟨g * v * g⁻¹, (inferInstance : (localSpan a c).Normal).conj_mem v hv g⟩ /
        spanHeadProjection geometry a c ⟨v, hv⟩ = 1
    rw [← he]
    exact div_self' _
  rw [spanHeadProjection_kernel] at hh
  change g * v * g⁻¹ / v ∈ spanRadical a c at hh
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh

omit [Finite M] in
private theorem span_radical_commutator_le_Z (geometry : Geometry R)
    (hb : 2 < geometry.b R) {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c) :
    ⁅spanRadical a c, pResidual 2 (stabilizer R c)⁆ ≤ Escape.Initial.Natural.Splitting.localZ c := by
  let := geometry.Z_normal c
  have hD : spanRadical a c ≤
      commutatorPreimage ⊤ (pResidual 2 (stabilizer R c)) (Escape.Initial.Natural.Splitting.localZ c) :=
    sup_le (le_commutatorPreimage le_top (commutator_le_left _ _))
      (le_commutatorPreimage le_top (span_local_triple geometry hb hc hd htriple))
  exact (commutator_mono hD le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

/-- Faithfulness of the actual local-span head. The triple bound preserves
the geometric nontriviality after killing the Q_c commutators. -/
theorem spanHeadAction_injective_of_triple (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c) :
    Function.Injective (spanHeadAction source geometry a c hc) := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply (spanHeadAction source geometry a c hc).ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker (spanHeadAction source geometry a c hc)).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exfalso
    apply span_local_moving_not_le_Z source geometry (by omega) ha hc hd hn
    let := finite_stabilizer R c
    let := localSpan_elementary geometry hb hc hd.le
    have hp : IsPGroup 2 (localSpan a c) := IsElementaryAbelian.isPGroup 2 _
    have hperfect := commutator_isPPerfect_idempotent
      (pResidual 2 (stabilizer R c)) (localSpan a c) (isPPerfect_pResidual 2)
      hp le_normalizer_of_normal
    rw [← hperfect]
    exact (commutator_mono ((commutator_mono le_rfl le_top).trans
      (span_commutator_le_radical_of_head_trivial source geometry a c hc hk)) le_rfl).trans
      (span_radical_commutator_le_Z geometry (by omega) hc hd.le htriple)

/-- The escaping displacement from the inside-B branch supplies nontriviality.
Neither its placement in Z_c D_c nor the marked quotient point is needed. -/
theorem spanHeadAction_injective_of_escaping (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c) :
    Function.Injective (spanHeadAction source geometry a c hc) :=
  spanHeadAction_injective_of_triple source geometry hb ha hc hd
    (fun h => hxD (h hx)) htriple

/-- Application to the literal recognition consumer, with faithfulness
discharged. The independent configuration and model-transfer producers remain
inputs of the realization assembly; this is not the full source (4.4.1). -/
theorem hasNaturalSection_of_displacement_and_transfer (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (d : EscapingConfiguration (spanHeadAction source geometry a c hc))
    (htransfer : actionDisplacement (spanHeadAction source geometry a c hc)
      (zpowers d.involution) ⊤ ≤
      actionDisplacement (spanHeadAction source geometry a c hc) (zpowers d.involution)
        (actionEscapingSpan (spanHeadAction source geometry a c hc)
          (markedPointStabilizer d.marking d.point) d.involution d.seed)) :
    HasNaturalSection R a c :=
  hasNaturalSection_of_escaping_transfer source geometry hb hc hd htriple
    (spanHeadAction_injective_of_escaping source geometry hb ha hc hd x hx hxD htriple)
    d htransfer

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
