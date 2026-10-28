module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Action

/-!
# Transport of the marked escaping span to the local head

The literal image in H/(Z_c[H,Q_c]) commutes with right conjugation.
Consequently the image of the K-span is invariant under the projected K
and its full orbit generates the head. If K is the preimage of a marked
point stabilizer, any nonidentity involution in the projected endpoint
has its escaping span contained in the image of the source escaping span.
The latter's commutator bound therefore gives the required small action.

This proves the transport part of MS93 (4.4.1)(2), printed p.891, for
application of (1.6), pp.845–847. Identifying K with the point stabilizer
and proving faithfulness are separate obligations.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem subgroupOf_iSup_of_le {G : Type*} [Group G] {S : Subgroup G}
    {ι : Sort*} (F : ι → Subgroup G) (hF : ∀ i, F i ≤ S) :
    (⨆ i, F i).subgroupOf S = ⨆ i, (F i).subgroupOf S := by
  apply Subgroup.map_injective S.subtype_injective
  rw [map_subgroupOf_eq_of_le (iSup_le hF), Subgroup.map_iSup]
  simp_rw [map_subgroupOf_eq_of_le (hF _)]

theorem spanHeadImage_mono (geometry : Geometry R) (a c : Vertex R)
    {W W' : Subgroup (FreeAmalgam R)} (h : W ≤ W') :
    spanHeadImage geometry a c W ≤ spanHeadImage geometry a c W' :=
  map_mono (subgroupOf_mono _ (subgroupOf_mono _ h))

theorem spanHeadImage_span (geometry : Geometry R) (a c : Vertex R) :
    spanHeadImage geometry a c (localZSpan R a c) = ⊤ := by
  change ((localSpan a c).subgroupOf (localSpan a c)).map _ = ⊤
  rw [subgroupOf_self, map_top_of_surjective _ (spanHeadProjection_surjective geometry a c)]

/-- Restricting to the head preserves joins of subgroups of H. -/
theorem spanHeadImage_iSup (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false) (hd : (cosetGraph R).dist a c ≤ 2)
    {ι : Sort*} (F : ι → Subgroup (FreeAmalgam R))
    (hF : ∀ i, F i ≤ localZSpan R a c) :
    spanHeadImage geometry a c (⨆ i, F i) = ⨆ i, spanHeadImage geometry a c (F i) := by
  have hS : ∀ i, F i ≤ stabilizer R c := fun i =>
    (hF i).trans ((localZSpan_le_Q R hc hd hb).trans (fun _ hx => hx.1))
  simp only [spanHeadImage, subgroupOf_iSup_of_le F hS,
    subgroupOf_iSup_of_le _ (fun i => show (F i).subgroupOf (stabilizer R c) ≤
      localSpan a c from fun _ hx => hF i hx), Subgroup.map_iSup]

variable [Finite M]

/-- The formula uses right conjugates on both sides. -/
theorem spanHeadImage_conjugate (source : LocalSource L R) (geometry : Geometry R)
    (a c : Vertex R) (hc : color R c = false)
    (W : Subgroup (FreeAmalgam R)) (g : stabilizer R c) :
    actionConjugate (spanHeadAction source geometry a c hc)
      (spanHeadImage geometry a c W) (localProjection source c hc g) =
    spanHeadImage geometry a c (NormalizerTransfer.rightConjugate W g) := by
  apply le_antisymm
  · rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    change spanHeadAction source geometry a c hc (localProjection source c hc g)⁻¹
      (spanHeadProjection geometry a c u) ∈ _
    rw [← map_inv, spanHeadAction_apply]
    refine ⟨⟨g⁻¹ * (u : stabilizer R c) * g⁻¹⁻¹,
      (inferInstance : (localSpan a c).Normal).conj_mem u u.property g⁻¹⟩, ?_, rfl⟩
    exact mem_map_of_mem (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom hu
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at he
    change (g : FreeAmalgam R)⁻¹ * v * (g : FreeAmalgam R) = (u : FreeAmalgam R) at he
    have hvS : v ∈ stabilizer R c := by
      have he' : v = (g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ := by
        rw [← he]
        simp [mul_assoc]
      rw [he']
      exact (stabilizer R c).mul_mem ((stabilizer R c).mul_mem g.property u.val.property)
        ((stabilizer R c).inv_mem g.property)
    let vS : stabilizer R c := ⟨v, hvS⟩
    have hvH : vS ∈ localSpan a c := by
      have he' : vS = g * (u : stabilizer R c) * g⁻¹ := by
        apply Subtype.ext
        change v = (g : FreeAmalgam R) * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹
        rw [← he]
        simp [mul_assoc]
      rw [he']
      exact (inferInstance : (localSpan a c).Normal).conj_mem u u.property g
    let vH : localSpan a c := ⟨vS, hvH⟩
    refine ⟨spanHeadProjection geometry a c vH, ⟨vH, hv, rfl⟩, ?_⟩
    change spanHeadAction source geometry a c hc (localProjection source c hc g)⁻¹
      (spanHeadProjection geometry a c vH) = spanHeadProjection geometry a c u
    rw [← map_inv, spanHeadAction_apply]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simpa only [coe_mul, coe_inv, inv_inv] using he

/-- The actual normalizer span is invariant after passing to the head. -/
theorem spanHead_normalizerSpan_invariant (source : LocalSource L R)
    (geometry : Geometry R) (a c : Vertex R) (hc : color R c = false)
    (x g : stabilizer R c) (hg : (g : FreeAmalgam R) ∈ pointNormalizer c x) :
    (spanHeadImage geometry a c (normalizerSpan a c x)).map
      (spanHeadAction source geometry a c hc (localProjection source c hc g)).toMonoidHom =
    spanHeadImage geometry a c (normalizerSpan a c x) := by
  have he := spanHeadImage_conjugate source geometry a c hc (normalizerSpan a c x) g⁻¹
  simp only [actionConjugate, map_inv, inv_inv] at he
  rw [he]
  congr 1
  simp only [NormalizerTransfer.rightConjugate, coe_inv, inv_inv]
  exact mem_normalizer_iff_map_conj_eq.mp (normalizerSpan_normalized a c x hg)

/-- Generation uses precisely the published normalizer-span generation identity. -/
theorem spanHead_normalizerSpan_generates (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) {a c : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c ≤ 2)
    (x : stabilizer R c) :
    actionOrbitSpan (spanHeadAction source geometry a c hc)
      (spanHeadImage geometry a c (normalizerSpan a c x)) = ⊤ := by
  have hF (g : stabilizer R c) :
      NormalizerTransfer.rightConjugate (normalizerSpan a c x) g ≤ localZSpan R a c := by
    rw [← normalizerSpan_conjugates_eq a c x]
    exact le_iSup_of_le g le_rfl
  have he := spanHeadImage_iSup geometry hb hc hd _ hF
  rw [show (⨆ g : stabilizer R c,
    NormalizerTransfer.rightConjugate (normalizerSpan a c x) g) = localZSpan R a c from
    normalizerSpan_conjugates_eq a c x, spanHeadImage_span] at he
  apply top_unique
  rw [he]
  apply iSup_le
  intro g
  rw [← spanHeadImage_conjugate source geometry a c hc]
  exact le_iSup_of_le (localProjection source c hc g) le_rfl

/-- Monotonicity permits restriction to one involution of the endpoint image. -/
theorem actionDisplacement_mono_both {E : Type*} [Group E] (ρ : SL →* MulAut E)
    {T T' : Subgroup SL} {W W' : Subgroup E} (hT : T ≤ T') (hW : W ≤ W') :
    actionDisplacement ρ T W ≤ actionDisplacement ρ T' W' := by
  apply Subgroup.closure_mono
  rintro _ ⟨t, ht, w, hw, rfl⟩
  exact ⟨t, hT ht, w, hW hw, rfl⟩

/-- The critical endpoint supplies a nonidentity involution in its actual image. -/
theorem exists_endpoint_involution (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : 2 < geometry.b R)
    {c e : Vertex R} (hc : color R c = false) (p : CriticalPath R geometry c e) :
    ∃ t : SL, t ≠ 1 ∧ t ^ 2 = 1 ∧
      t ∈ ((Z R e).subgroupOf (stabilizer R c)).map (localProjection source c hc) := by
  obtain ⟨z, hz, hn⟩ := Set.not_subset.mp (p.reverse common).critical.2
  let zS : stabilizer R c := ⟨z, p.endpoint_Z_le_start_stabilizer (by omega) hz⟩
  refine ⟨localProjection source c hc zS, ?_, ?_, mem_map_of_mem _ hz⟩
  · intro he
    have hker : zS ∈ (localProjection source c hc).ker := he
    rw [localProjection_kernel] at hker
    exact hn hker
  · let := geometry.Z_elementary (by omega) e p.end_color
    have hsq : zS ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
    rw [← map_pow, hsq, map_one]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
