module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Transvections.Frattini
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Transvections.Geometry

/-!
# The faithful temporary-core action and the offender rank adapter

`TemporaryData` retains the original local inputs, the unchanged Sylow group,
and the inherited marked elements and centralizer-span witness. From those
inputs we recover the temporary core using `Replacement.Core`, prove the
Frattini and residual-commutator steps, and act on the entire original lineV
inside the actual temporary normalizer. The faithful representation has
precisely its relative centralizer as kernel.

For explicit marked fixed-space geometry, `temporary_core_transvections`
proves faithfulness on the first space and identifies every nonzero displacement
range with C_E(τ). `temporary_core_fixedCodim` gives the doubling identity for
all subgroups of the core action image. The last theorem supplies both displayed
offender inequalities for B = A ∩ Q, deriving the needed kernel containment.

This is a conditional prerequisite: the replacement assembly supplies the
original local facts and the marked direct sum and center-line witnesses.
Neither a numerical rank identity nor a transvection conclusion is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
variable {G K : Type*} [Group G] [Group K]

/-- The subgroup commutator is the displacement in the actual conjugation representation. -/
theorem conjugation_displacement (U E Q : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (f : G →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (hc : ⁅U, Q⁆ ≤ E) :
    ∀ q ∈ Q.map f, ∀ x : Additive U,
      Representation.NormalElementaryQuotient.representation U f hf hker q x - x ∈
        Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U) := by
  rintro _ ⟨q, hq, rfl⟩ x
  change ((Representation.NormalElementaryQuotient.representation U f hf hker (f q) x - x).toMul : G) ∈ E
  change ((Representation.NormalElementaryQuotient.representation U f hf hker (f q) x).toMul : G) /
    (x.toMul : G) ∈ E
  rw [div_eq_mul_inv]
  rw [Representation.NormalElementaryQuotient.representation_apply]
  change ⁅q, (x.toMul : G)⁆ ∈ E
  rw [← commutatorElement_inv]
  exact E.inv_mem (hc (commutator_mem_commutator x.toMul.property hq))

/-- Pointwise centralization of E is pointwise fixation of its binary subspace. -/
theorem conjugation_fixes_line (U E Q : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (f : G →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (hc : Q ≤ centralizer (E : Set G)) :
    ∀ q ∈ Q.map f, ∀ x ∈ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U),
      Representation.NormalElementaryQuotient.representation U f hf hker q x = x := by
  rintro _ ⟨q, hq, rfl⟩ x hx
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [Representation.NormalElementaryQuotient.representation_apply,
    ← hc hq x.toMul hx, mul_inv_cancel_right]

/-- The center in the linear geometry is exactly the binary subspace of C_E(τ). -/
theorem first_center_eq_centralizer (U E : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (f : G →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (t : G) :
    Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U) ⊓
      firstSpace (Representation.NormalElementaryQuotient.representation U f hf hker) (f t) =
        Representation.NormalElementaryQuotient.subspace U
          ((E ⊓ centralizer ({t} : Set G)).subgroupOf U) := by
  ext x
  change ((x.toMul : G) ∈ E ∧ x ∈ firstSpace
    (Representation.NormalElementaryQuotient.representation U f hf hker) (f t)) ↔
    (x.toMul : G) ∈ E ∧ (x.toMul : G) ∈ centralizer ({t} : Set G)
  apply and_congr_right
  intro _
  rw [mem_firstSpace, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he := congrArg (fun v : Additive U => (v.toMul : G)) h
    rw [Representation.NormalElementaryQuotient.representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [Representation.NormalElementaryQuotient.representation_apply, ← h, mul_inv_cancel_right]

/-- Original local inputs and inherited marked geometry for the temporary group.
The action consequences and all numerical ranks are deliberately absent. -/
structure TemporaryData (Y T V E : Subgroup G) [IsMulCommutative V] where
  line_le : E ≤ V
  span_le_sylow : lineV V E ≤ lineT T E
  sylow : Sylow 2 (lineNormalizer E)
  sylow_eq : (sylow : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E
  residual_normalized : lineNormalizer E ≤ normalizer (lineY Y E : Set G)
  original_core_section : lineQ E ≤ Descent.sectionKernel V E
  residual_section_core : lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E
  local_core : (lineY Y E ⊔ lineT T E).pCoreIn 2 ≤ T ⊓ centralizer (E : Set G)
  local_commutator : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E
  residual_core_centralizes : (lineY Y E).pCoreIn 2 ≤ centralizer (V : Set G)
  seed_normalized : lineT T E ≤ normalizer (V : Set G)
  seed_elementary : IsElementaryAbelian 2
    (V.normalizerMonoidHom.comp (inclusion seed_normalized)).range
  tau : temporaryLineNormalizer T V E
  tau_mem : (tau : G) ∈ lineT T E
  conjugator : temporaryLineNormalizer T V E
  conjugator_mem : (conjugator : G) ∈ lineY Y E
  centralizer_tau_mod : ∀ c ∈ temporaryCentralizer T V E,
    ⁅c, (tau : G)⁆ ∈ temporaryCore T V E
  centralizer_span : lineV V E = conjugateSpanBy V (temporaryCentralizer T V E)

/-- The original span, viewed inside the literal temporary normalizer. -/
abbrev localSpan (T V E : Subgroup G) :=
  (lineV V E).subgroupOf (temporaryLineNormalizer T V E)

/-- The temporary core as a subgroup of its own local group. -/
noncomputable abbrev localCore (T V E : Subgroup G) :=
  (temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)

/-- The original residual restricted to the temporary normalizer. -/
noncomputable abbrev localResidual (Y T V E : Subgroup G) :=
  (lineY Y E).subgroupOf (temporaryLineNormalizer T V E)

/-- The marked line inside the temporary normalizer. -/
abbrev localLine (T V E : Subgroup G) :=
  E.subgroupOf (temporaryLineNormalizer T V E)

/-- The literal faithful conjugation representation of the temporary group. -/
noncomputable abbrev localRepresentation (T V E : Subgroup G)
    [(localSpan T V E).Normal] [IsElementaryAbelian 2 (localSpan T V E)]
    (f : temporaryLineNormalizer T V E →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (localSpan T V E : Set (temporaryLineNormalizer T V E))) :=
  Representation.NormalElementaryQuotient.representation (localSpan T V E) f hf hker

/-- The actual marked E-subspace in the original span. -/
noncomputable abbrev localLineSpace (T V E : Subgroup G)
    [IsElementaryAbelian 2 (localSpan T V E)] :=
  Representation.NormalElementaryQuotient.subspace (localSpan T V E)
    ((localLine T V E).subgroupOf (localSpan T V E))

variable [Finite G] (Y T V E : Subgroup G) [IsMulCommutative V]

omit [Finite G] in
/-- The local data place the original residual in the actual temporary normalizer. -/
theorem TemporaryData.residual_le (d : TemporaryData Y T V E) : lineY Y E ≤ (temporaryLineNormalizer T V E) :=
  lineY_le_temporary Y T V E d.line_le d.sylow d.sylow_eq d.residual_normalized
    d.original_core_section d.residual_section_core

/-- The original local relations recover the temporary core, without identifying it with lineQ. -/
theorem TemporaryData.core_eq (d : TemporaryData Y T V E) :
    temporaryCore T V E = lineQuotientCentralizer T V E :=
  temporaryCore_eq_quotientCentralizer Y T V E d.line_le
    ((le_conjugateSpanBy V (lineNormalizer E)).trans d.span_le_sylow)
    d.sylow d.sylow_eq d.residual_normalized d.original_core_section
    d.residual_section_core d.local_core d.local_commutator

/-- The same local core bound shows that the temporary core fixes E. -/
theorem TemporaryData.core_centralizes_line (d : TemporaryData Y T V E) :
    temporaryCore T V E ≤ centralizer (E : Set G) := by
  have hQT := temporaryCore_le_lineT T V E d.line_le d.sylow d.sylow_eq
  have hQ := (normal_subgroupOf_iff_le_normalizer (temporaryCore_le T V E)).mp
    (temporaryCore_normal T V E)
  exact ((le_pCoreIn_of_normalizes (temporaryCore_isPGroup T V E)
    (hQT.trans le_sup_right)
    ((sup_le (d.residual_le Y T V E) (lineT_le_temporary T V E d.line_le)).trans hQ)).trans
      d.local_core).trans inf_le_right

omit [Finite G] in
/-- Restriction to H retains the entire original span, not an intersection with a smaller group. -/
theorem TemporaryData.span_map_eq (d : TemporaryData Y T V E) :
    (localSpan T V E).map (temporaryLineNormalizer T V E).subtype = lineV V E :=
  map_subgroupOf_eq_of_le
    (d.span_le_sylow.trans (lineT_le_temporary T V E d.line_le))

omit [Finite G] in
/-- Normality of the original conjugate span is relative to the temporary group. -/
theorem TemporaryData.span_normal (d : TemporaryData Y T V E) :
    (localSpan T V E).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (d.span_le_sylow.trans (lineT_le_temporary T V E d.line_le))).mpr
  exact inf_le_left.trans (le_normalizer_conjugateSpanBy V (lineNormalizer E))

omit [Finite G] in
/-- The inherited elementary structure is transported on the same group. -/
theorem TemporaryData.span_elementary [IsElementaryAbelian 2 (lineV V E)]
    (d : TemporaryData Y T V E) : IsElementaryAbelian 2 (localSpan T V E) :=
  IsElementaryAbelian.subgroupOf
    (d.span_le_sylow.trans (lineT_le_temporary T V E d.line_le))

variable [(localSpan T V E).Normal] [IsElementaryAbelian 2 (localSpan T V E)]
variable (f : (temporaryLineNormalizer T V E) →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer ((localSpan T V E) : Set (temporaryLineNormalizer T V E)))

/-- The raw source inputs give all qualitative core-action properties used by the linear proof. -/
theorem temporary_core_action (d : TemporaryData Y T V E) :
    IsElementaryAbelian 2 ((localCore T V E).map f) ∧
    (∀ q ∈ (localCore T V E).map f, Commute (f d.tau) q) ∧
    (∀ q ∈ (localCore T V E).map f, Commute (f d.conjugator) q) ∧
    (∀ q ∈ (localCore T V E).map f, ∀ x, (localRepresentation T V E f hf hker) q x - x ∈ (localLineSpace T V E)) ∧
    (∀ q ∈ (localCore T V E).map f, ∀ x ∈ (localLineSpace T V E), (localRepresentation T V E f hf hker) q x = x) := by
  let P := (zpowers (d.tau : G) ⊔ temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)
  have hphi : frattini (P.map f) = ⊥ :=
    temporary_frattini_image_eq_bot T V E d.line_le d.sylow d.sylow_eq
      d.tau d.tau_mem d.seed_normalized d.seed_elementary
      d.centralizer_tau_mod d.centralizer_span f hker
  have hp : IsPGroup 2 (lineT T E) := d.sylow_eq ▸ d.sylow.isPGroup'.map (lineNormalizer E).subtype
  have hPS : zpowers (d.tau : G) ⊔ temporaryCore T V E ≤ lineT T E :=
    sup_le (zpowers_le.mpr d.tau_mem) (temporaryCore_le_lineT T V E d.line_le d.sylow d.sylow_eq)
  have hpP : IsPGroup 2 P := (hp.to_le hPS).comap_subtype
  let _ : Finite (P.map f) := Set.Finite.to_subtype ((Set.toFinite (P : Set (temporaryLineNormalizer T V E))).image f)
  let _ : Fact (IsPGroup 2 (P.map f)) := ⟨hpP.map f⟩
  let _ : IsElementaryAbelian 2 (P.map f) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hQP : (localCore T V E).map f ≤ P.map f := map_mono (comap_mono le_sup_right)
  have hel : IsElementaryAbelian 2 ((localCore T V E).map f) := IsElementaryAbelian.of_le hQP
  have ht : ∀ q ∈ (localCore T V E).map f, Commute (f d.tau) q := by
    intro q hq
    exact setLike_mul_comm
      (mem_map_of_mem f (show d.tau ∈ P from mem_sup_left (mem_zpowers _))) (hQP hq)
  have hc := temporary_commutator_centralizes_lineV Y T V E d.line_le d.sylow d.sylow_eq
    (d.residual_le Y T V E) (inf_le_left.trans d.residual_normalized) d.residual_core_centralizes
  have hc' : ⁅localResidual Y T V E, localCore T V E⁆ ≤
      centralizer (localSpan T V E : Set (temporaryLineNormalizer T V E)) := by
    apply commutator_le.mpr
    intro y hy q hq u hu
    exact Subtype.ext (hc (commutator_mem_commutator hy hq) u hu)
  have himage := image_commutes (localResidual Y T V E) (localCore T V E) (localSpan T V E) f hker hc'
  have hy : ∀ q ∈ (localCore T V E).map f, Commute (f d.conjugator) q := by
    intro q hq
    exact (himage (mem_map_of_mem f d.conjugator_mem) q hq).symm
  have hsec : ⁅(localSpan T V E), (localCore T V E)⁆ ≤ (localLine T V E) := by
    apply commutator_le.mpr
    intro u hu q hq
    have hq' : (q : G) ∈ lineQuotientCentralizer T V E := d.core_eq Y T V E ▸ hq
    exact ((mem_lineQuotientCentralizer_iff T V E
      (d.span_le_sylow.trans inf_le_right) q).mp hq').2 u hu
  have hfix : (localCore T V E) ≤ centralizer ((localLine T V E) : Set (temporaryLineNormalizer T V E)) := by
    intro q hq e he
    exact Subtype.ext (d.core_centralizes_line Y T V E hq e he)
  exact ⟨hel, ht, hy, conjugation_displacement (localSpan T V E) (localLine T V E) (localCore T V E) f hf hker hsec,
    conjugation_fixes_line (localSpan T V E) (localLine T V E) (localCore T V E) f hf hker hfix⟩

/-- The exact source doubling identity for every subgroup of the faithful temporary-core image. -/
theorem temporary_core_fixedCodim (d : TemporaryData Y T V E)
    (geom : FixedGeometry (localRepresentation T V E f hf hker) (f d.tau) (f d.conjugator) (localLineSpace T V E))
    (W : Subgroup K) (hW : W ≤ (localCore T V E).map f) :
    fixedCodim (localRepresentation T V E f hf hker) W = 2 * rank W := by
  let _ : Finite K := Finite.of_surjective f hf
  obtain ⟨hel, ht, hy, hd, he⟩ := temporary_core_action Y T V E f hf hker d
  let _ : IsElementaryAbelian 2 ((localCore T V E).map f) := hel
  exact core_fixedCodim_eq_twice_rank (localRepresentation T V E f hf hker)
    ((localCore T V E).map f) (f d.tau) (f d.conjugator) (localLineSpace T V E)
    ht hy (Representation.NormalElementaryQuotient.representation_injective (localSpan T V E) f hf hker)
    geom hd he W hW

/-- The core acts faithfully on C_U(τ), and every nonidentity actor has exactly the center C_E(τ). -/
theorem temporary_core_transvections (d : TemporaryData Y T V E)
    (geom : FixedGeometry (localRepresentation T V E f hf hker) (f d.tau)
      (f d.conjugator) (localLineSpace T V E)) :
    ∃ ht : ∀ q ∈ (localCore T V E).map f, Commute (f d.tau) q,
      Function.Injective (firstRepresentation (localRepresentation T V E f hf hker)
        ((localCore T V E).map f) (f d.tau) ht) ∧
      ∀ q : (localCore T V E).map f, q ≠ 1 →
        LinearMap.range (firstRepresentation (localRepresentation T V E f hf hker)
          ((localCore T V E).map f) (f d.tau) ht q - LinearMap.id) =
            (localLineSpace T V E).comap
              (firstSpace (localRepresentation T V E f hf hker) (f d.tau)).subtype := by
  obtain ⟨_, ht, hy, hd, _⟩ := temporary_core_action Y T V E f hf hker d
  have hfaith := Representation.NormalElementaryQuotient.representation_injective
    (localSpan T V E) f hf hker
  refine ⟨ht, firstRepresentation_injective _ _ _ _ _ ht hy hfaith geom, ?_⟩
  intro q hq
  apply Submodule.eq_of_le_of_finrank_eq (first_displacement_range_le _ _ _ _ ht hd q)
  exact (first_displacement_finrank _ _ _ _ _ ht hy hfaith geom hd q hq).trans
    (first_center_finrank _ _ _ _ geom).symm

omit [(localSpan T V E).Normal] [IsElementaryAbelian 2 (localSpan T V E)] in
include hker in
/-- The source D = C_A(U) lies in the temporary core for every A inside the unchanged Sylow. -/
theorem temporary_action_kernel_le_core (d : TemporaryData Y T V E)
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ≤ (lineT T E).subgroupOf (temporaryLineNormalizer T V E)) :
    A ⊓ f.ker ≤ localCore T V E := by
  intro x hx
  change (x : G) ∈ temporaryCore T V E
  rw [d.core_eq Y T V E]
  apply (mem_lineQuotientCentralizer_iff T V E
    (d.span_le_sylow.trans inf_le_right) x).mpr
  refine ⟨hA hx.1, fun u hu => ?_⟩
  have huH : u ∈ temporaryLineNormalizer T V E :=
    (d.span_le_sylow.trans (lineT_le_temporary T V E d.line_le)) hu
  have hxC : x ∈ centralizer (localSpan T V E : Set (temporaryLineNormalizer T V E)) :=
    hker ▸ hx.2
  have he := congrArg Subtype.val (hxC ⟨u, huH⟩ hu)
  rw [commutatorElement_eq_one_iff_mul_comm.mpr he]
  exact E.one_mem

/-- The doubling identity in the source's relative quotient-rank convention. -/
theorem temporary_core_quotientRank (d : TemporaryData Y T V E)
    (geom : FixedGeometry (localRepresentation T V E f hf hker) (f d.tau)
      (f d.conjugator) (localLineSpace T V E))
    (B : Subgroup (temporaryLineNormalizer T V E)) (hB : B ≤ localCore T V E) :
    quotientRank (localSpan T V E) ((localSpan T V E) ⊓ centralizer (B : Set (temporaryLineNormalizer T V E))) =
      2 * rank (B.map f) := by
  rw [quotientRank_eq_fixedCodim (localSpan T V E) f hf hker B]
  exact temporary_core_fixedCodim Y T V E f hf hker d geom _ (map_mono hB)

/-- Both displayed offender inequalities, with B = A ∩ Q and no extra rank premise. -/
theorem temporary_displayed_rank_inequalities [(localCore T V E).Normal]
    (d : TemporaryData Y T V E)
    (geom : FixedGeometry (localRepresentation T V E f hf hker) (f d.tau)
      (f d.conjugator) (localLineSpace T V E))
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ∈ elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf (temporaryLineNormalizer T V E))) :
    let U := localSpan T V E
    let Q := localCore T V E
    let N := quotientRank (U ⊓ centralizer
      ((A ⊓ Q : Subgroup (temporaryLineNormalizer T V E)) : Set (temporaryLineNormalizer T V E)))
      (U ⊓ centralizer (A : Set (temporaryLineNormalizer T V E)))
    rank ((A ⊓ Q).map f) + N ≤ rank (A.map (QuotientGroup.mk' Q)) ∧
      quotientRank U (U ⊓ centralizer (A : Set (temporaryLineNormalizer T V E))) + N ≤
        2 * rank (A.map (QuotientGroup.mk' Q)) := by
  exact displayed_rank_inequalities
    ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)) (localSpan T V E) A
    (localCore T V E) (comap_mono d.span_le_sylow) hA f hker
    (temporary_action_kernel_le_core Y T V E f hker d A hA.1)
    (temporary_core_quotientRank Y T V E f hf hker d geom (A ⊓ localCore T V E) inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
