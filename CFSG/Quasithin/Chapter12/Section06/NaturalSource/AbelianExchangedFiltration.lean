module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedQuotient
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedTensor
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.NonTensor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Recognition
public import Theory.Representation.BinaryOffender.ConjugatePairFixedSpace
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.Representation.BinaryConjugationSection.MixedCommutator
public import Theory.Representation.BinaryConjugationSection.QuotientSection

/-!
# The original exchanged non-tensor filtration

Recognize the faithful irreducible maximal quotient of U_H/V₁. If both
component fixed spaces vanish, intrinsic cubic recognition supplies tensor
coordinates. The FF alternative excludes that quotient; in the central
alternative the coordinates lift to the whole module, contradicting the
original edge-core-fixed four-space. Thus the quotient has crossed supports.

Mixed movement in its kernel would have an irreducible head moved by both
components. That head is tensor and costs strictly more than one actor rank;
the faithful maximal quotient costs at least one. The same original quadratic
actor has a two-rank bound, so the kernel has no mixed movement. Pulling back
the literal subspace constructs the actual normal subgroup I of H with
[U_H,K,Kᵗ] ≤ I and [I,K,Kᵗ] ≤ V₁. The final application discharges these two
premises of the existing nonsingular-vector contradiction.

The earlier geometry, point marking and selection of a cubic in K intersect L
still need their original-source discharge. This does not assert 12.6.33 or
the universal natural reduction.
Source: Aschbacher--Smith 12.6.33, pp.837--838; F.9.18 and D.3.9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
open ModuleAlternatives ModuleAlternatives.F918Sections ModuleAlternatives.F918Sections.NoStrong
open ModuleAlternatives.SourceRecognition
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
/-- The original quadratic budget prevents a second tensor section below
an irreducible faithful head. Thus the two components have no mixed movement
on the kernel. The same elementary actor is used in both layers. -/
private theorem exchanged_mixed_kernel_eq_bot
    {J U : Type*} {F : Type} [Group J] [Finite J] [Field F] [Finite F] [CharP F 2]
    (b : ExchangedActor KnownSimple.IsKnownSimple J F 2)
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U)
    (hA : ∀ g : J, b.component.conjBy g = b.component ∨ b.component.conjBy g = b.second)
    (hB : ∀ g : J, b.second.conjBy g = b.component ∨ b.second.conjBy g = b.second)
    (W : Subrepresentation ρ) (hfaith : Function.Injective W.quotientRepresentation)
    (A : Subgroup J) (hEA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    subspaceCommutator W.toRepresentation
      (subspaceCommutator W.toRepresentation ⊤ b.component) b.second = ⊥ := by
  let δ := W.toRepresentation
  let X := subspaceCommutator δ (subspaceCommutator δ ⊤ b.component) b.second
  have hc : b.component ≤ centralizer (b.second : Set J) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (b.component_isComponent.commutator_eq_bot_of_ne b.second_isComponent b.distinct.symm)
  have hcomm : ∀ x ∈ b.component, ∀ y ∈ b.second, Commute x y :=
    fun x hx y hy => (hc hx y hy).symm
  have hp : ∀ g : J,
      (b.component.map (MulAut.conj g).toMonoidHom = b.component ∧
        b.second.map (MulAut.conj g).toMonoidHom = b.second) ∨
      (b.component.map (MulAut.conj g).toMonoidHom = b.second ∧
        b.second.map (MulAut.conj g).toMonoidHom = b.component) := by
    intro g
    have hinj := Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rcases hA g with ha | ha <;> rcases hB g with hb | hb
    · exact (b.distinct (hinj (hb.trans ha.symm))).elim
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
    · exact (b.distinct (hinj (hb.trans ha.symm))).elim
  let : IsQuasisimple b.component := b.component_isComponent.2
  let : IsQuasisimple b.second := b.second_isComponent.2
  have hinv := mixed_commutator_invariant_of_permuted δ b.component b.second hcomm hp
  by_contra hn
  let Y : Subrepresentation δ := ⟨X,fun g v hv => (hinv (mem_top g) v).2 hv⟩
  let : Nontrivial Y.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  let : IsCoatomic (Subrepresentation Y.toRepresentation) :=
    SimpleHeadQuotient.subrepresentation_coatomic Y.toRepresentation
  obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation Y.toRepresentation)
  let : N.quotientRepresentation.IsIrreducible :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let σ := N.quotientRepresentation
  let : Nontrivial (Y.toSubmodule ⧸ N.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨hmA,hmB⟩ := mixed_commutator_generated δ b.component b.second hcomm
  have hfullA : subspaceCommutator σ ⊤ b.component = ⊤ :=
    quotient_moved_eq_top_of_full δ Y N b.component hmA
  have hfullB : subspaceCommutator σ ⊤ b.second = ⊤ :=
    quotient_moved_eq_top_of_full δ Y N b.second hmB
  have hσ : Function.Injective σ := b.faithful_of_noncentral σ (by
    intro hk
    have hz : subspaceCommutator σ ⊤ b.component = ⊥ :=
      (subspaceCommutator_eq_bot_iff _ _ _).mpr
        (fun v _ g => hk g (b.component_le g.property) v)
    exact (top_ne_bot : (⊤ : Submodule (ZMod 2) _) ≠ ⊥) (hfullA.symm.trans hz))
  have hfix : fixedSpace σ b.component = ⊥ ∧ fixedSpace σ b.second = ⊥ := by
    rcases cross_fixed_or_component_fixed_eq_bot σ _ _ hA hB hc with hx | hz
    · have he : subspaceCommutator σ ⊤ b.second = ⊥ :=
        (subspaceCommutator_eq_bot_iff _ _ _).mpr (hfullA ▸ hx.1)
      exact (top_ne_bot (hfullB.symm.trans he)).elim
    · exact hz
  have hqY := quadratic_subrepresentation δ Y (quadratic_subrepresentation ρ W hq)
  have hqN := quadratic_of_equivariant_surjection Y.toRepresentation σ
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hqY
  have hcostW := fixedCodim_subrepresentation_le ρ W A
  have hcostY := fixedCodim_subrepresentation_le δ Y A
  have hcostN := fixedCodim_quotient_add_subrepresentation_le Y.toRepresentation N A
  change fixedCodim Y.toRepresentation A ≤ fixedCodim W.toRepresentation A at hcostY
  have hboundN : fixedCodim σ A ≤ 2 * rank A := by
    change fixedCodim N.quotientRepresentation A ≤ 2 * rank A
    omega
  have horth := exchanged_cubic_orthogonal b σ hσ hfix.1 hfix.2
    ((cubicRatio_le_nat_iff _ 2).mpr ⟨A,hEA,isCubic_of_isQuadratic hqN,hboundN⟩)
  let : b.orbit.Normal := b.orbit_normal
  have hstrict := rank_lt_fixedCodim_of_nonFF_image σ hEA (fun x _ hx => by
    apply hσ
    apply LinearMap.ext
    intro v
    simpa only [map_one,Module.End.one_apply] using hx v) (orthogonal_image_not_ff σ b.orbit horth)
  let : Finite (U ⧸ W.toSubmodule) := Finite.of_surjective W.toSubmodule.mkQ
    W.toSubmodule.mkQ_surjective
  have hnot := exchanged_not_strong b W.quotientRepresentation hfaith
  have hcostQ : rank A ≤ fixedCodim W.quotientRepresentation A := by
    exact le_of_not_gt (fun hh => hnot ⟨A,hEA,hh⟩)
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  change rank A < fixedCodim N.quotientRepresentation A at hstrict
  omega

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


variable [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

local instance filtration_source_span_elementary (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    IsElementaryAbelian 2 (Chapter13.Section08.Source.UH J E.V₅) :=
  inferInstanceAs (IsElementaryAbelian 2 (E.UH J))
local instance filtration_source_span_normal (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    (E.V₁.subgroupOf (Chapter13.Section08.Source.UH J E.V₅)).Normal :=
  inferInstanceAs ((E.V₁.subgroupOf (E.UH J)).Normal)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Both layers have crossed supports: intrinsic tensor recognition and
the original displacement budget construct the entire linear filtration. -/
theorem SourceHypothesis.original_abelian_exchanged_linear_filtration
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ t : G, t ∈ T ∧ t ∉ normalizer (K : Set G) ∧
      ∃ W : Subrepresentation a.representation, W ≠ ⊤ ∧
        W.quotientRepresentation.IsIrreducible ∧
        Function.Injective W.quotientRepresentation ∧
        (sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁).map
          W.toSubmodule.mkQ ≠ ⊥ ∧
        subspaceCommutator W.quotientRepresentation ⊤ (actorImage H K) ≤
          fixedSpace W.quotientRepresentation (actorImage H (K.conjBy t)) ∧
        subspaceCommutator W.quotientRepresentation ⊤ (actorImage H (K.conjBy t)) ≤
          fixedSpace W.quotientRepresentation (actorImage H K) ∧
        subspaceCommutator W.toRepresentation
          (subspaceCommutator W.toRepresentation ⊤ (actorImage H K))
          (actorImage H (K.conjBy t)) = ⊥ ∧
        ((IsFFModule (imageRepresentation W.toRepresentation) ∧
          IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
         W.toSubmodule ≤ fixedSpace a.representation
            (actorImage H (conjugateSpanBy K (T : Subgroup G)))) := by
  obtain ⟨W,hW,hirr,hfaith,hcubic,hseed,halt⟩ := S.original_abelian_exchanged_faithful_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
  let := hirr
  obtain ⟨t,ht,hTH,htn,F,hF,hfin,hchar,b,ha,hb,ho,_,_⟩ :=
    S.original_abelian_exchanged_actor D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hm
  obtain ⟨hA,hB⟩ := S.original_abelian_exchanged_pair_conjugates
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn ht htn
  have hcomm : actorImage H K ≤ centralizer (actorImage H (K.conjBy t) : Set (H ⧸ pCore 2 H)) := by
    rw [←ha,←hb]
    exact commutator_eq_bot_iff_le_centralizer.mp
      (b.component_isComponent.commutator_eq_bot_of_ne b.second_isComponent b.distinct.symm)
  rcases cross_fixed_or_component_fixed_eq_bot W.quotientRepresentation _ _ hA hB hcomm with hx | hf
  · obtain ⟨_,hU,c,B,_,_,hEA,hquad,hcod,_,_⟩ :=
      S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
    have heq := a.representation_eq c
    rw [←heq] at hquad hcod
    have hlower := exchanged_mixed_kernel_eq_bot b a.representation
      (by simpa only [ha,hb] using hA) (by simpa only [ha,hb] using hB)
      W hfaith (B.map (QuotientGroup.mk' (pCore 2 H))) hEA hquad hcod
    rw [ha,hb] at hlower
    exact ⟨t,ht,htn,W,hW,hirr,hfaith,hseed,hx.1,hx.2,hlower,halt⟩
  · have horth : HasOrthogonalFourOrbit W.quotientRepresentation b.orbit :=
      exchanged_cubic_orthogonal b W.quotientRepresentation hfaith (ha.symm ▸ hf.1)
        (hb.symm ▸ hf.2) hcubic
    exfalso
    rcases halt with hff | hcentral
    · let : b.orbit.Normal := b.orbit_normal
      exact orthogonal_image_not_ff W.quotientRepresentation b.orbit horth hff.2
    · have hfull := S.original_abelian_exchanged_movement
        D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
      rw [ho] at horth
      obtain ⟨_,f,e,he⟩ := orthogonal_quotient_is_whole a.representation _ W hcentral hfull horth
      let f' := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
      let e' := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
      apply S.original_abelian_exchanged_tensor_impossible
        D hZ z hz hTV hTz hbound hTI hns hH a hKH hK hgen hn hm f' e'
      intro k u
      change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
        (e (a.representation k.val u)) = _
      rw [he]
      have hf' : f k = ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv (f' k) :=
        (ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.apply_symm_apply _).symm
      rw [hf']
      exact ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates_projective_equivariant
        (f' k) (e u)

omit [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)] in
include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original non-tensor filtration, on actual subgroups of H. Both
component embeddings and the original Sylow exchanger are retained. -/
theorem SourceHypothesis.original_abelian_exchanged_group_filtration
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ t : G, t ∈ T ∧ t ∉ normalizer (K : Set G) ∧
      ∃ I : Subgroup H,
        (D.fullSetup hZ T z).V₁.subgroupOf H ≤ I ∧
        I ≤ ((D.fullSetup hZ T z).UH H).subgroupOf H ∧ I.Normal ∧
        ⁅⁅((D.fullSetup hZ T z).UH H).subgroupOf H,K.subgroupOf H⁆,
          (K.conjBy t).subgroupOf H⁆ ≤ I ∧
        ⁅⁅I,K.subgroupOf H⁆,(K.conjBy t).subgroupOf H⁆ ≤
          (D.fullSetup hZ T z).V₁.subgroupOf H := by
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor
    D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  obtain ⟨t,ht,htn,W,hW,hirr,hfaith,hseed,hupper,_,hlower,_⟩ :=
    S.original_abelian_exchanged_linear_filtration
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let c : BinaryConjugationSection H (E.UH H) E.V₁ (a.representation.comp q) := {
    section_le := a.le_local
    kernel_le := a.kernel_le
    normalized := a.normalizes
    coordinates := (MulEquiv.multiplicativeAdditive _).symm.toMonoidHom.comp
      (QuotientGroup.mk' (E.V₁.subgroupOf (E.UH H)))
    onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
    kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
    equivariant := fun g u => (a.conjugation g u).symm }
  let W' : Subrepresentation (a.representation.comp q) := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule g v hv := W.apply_mem_toSubmodule (q g) hv }
  let I := c.invariantPreimage W'
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hBH : K.conjBy t ≤ H := (conjugate_isCComponent H K hKH hK (hTH ht)).1
  have hI : I ≤ E.UH H := c.invariantPreimage_le W'
  have hu : ⁅⁅E.UH H,K⁆,K.conjBy t⁆ ≤ I := by
    apply (c.quotientSection W').mixed_commutator_le_kernel K (K.conjBy t) hKH hBH
    change subspaceCommutator (W.quotientRepresentation.comp q) ⊤ (K.subgroupOf H) ≤
      fixedSpace (W.quotientRepresentation.comp q) ((K.conjBy t).subgroupOf H)
    rw [subspaceCommutator_comp_map,fixedSpace_comp_map]
    exact hupper
  have hl : ⁅⁅I,K⁆,K.conjBy t⁆ ≤ E.V₁ := by
    apply (c.invariantSection W').mixed_commutator_le_kernel K (K.conjBy t) hKH hBH
    change subspaceCommutator (W.toRepresentation.comp q) ⊤ (K.subgroupOf H) ≤
      fixedSpace (W.toRepresentation.comp q) ((K.conjBy t).subgroupOf H)
    rw [subspaceCommutator_comp_map,fixedSpace_comp_map]
    exact (subspaceCommutator_eq_bot_iff _ _ _).mp hlower
  refine ⟨t,ht,htn,I.subgroupOf H,
    comap_mono (c.kernel_le_invariantPreimage W'),comap_mono hI,
    c.invariantPreimage_normal W',?_,?_⟩
  · apply (map_le_iff_le_comap).mp
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le a.le_local,
      map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hBH]
    exact hu
  · apply (map_le_iff_le_comap).mp
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le (hI.trans a.le_local),
      map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hBH]
    exact hl

omit [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)] in
include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Apply the constructed filtration to the original nonsingular-vector
contradiction. Only the point coordinates and an actual cubic in K intersect L
remain for the original-source selection; no filtration or tensor coordinates
are assumed. -/
theorem SourceHypothesis.original_abelian_exchanged_impossible_of_marked_cubic
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    (hout : ¬ K ≤ M L)
    (r : Equiv.Perm (Fin 8))
    (hmark : D.coordinates (Submodule.Quotient.mk (Additive.ofMul z)) =
      BinaryPermutation.naturalRepresentation (Fin 8) r
        BinaryPermutation.TerminalOrthogonal.CubicMovement.point)
    (x : K) (hxL : (x : G) ∈ L) (hx3 : x ^ 3 = 1) (hxn : x ≠ 1) : False := by
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor
    D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  obtain ⟨t,ht,htn,I,_,_,_,hupper,hlower⟩ :=
    S.original_abelian_exchanged_group_filtration
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨hBH,hB⟩ := conjugate_isCComponent H K hKH hK (h.T_le_H ht)
  have hq : IsQuasisimple (actorImage H K) :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  let : IsQuasisimple (Chapter13.Section08.Source.starImage H K) := hq
  have hqB : IsQuasisimple (actorImage H (K.conjBy t)) :=
    IsQuasisimple.of_mulEquiv (starConjugateEquiv H K hKH (h.T_le_H ht))
  have hne : K ≠ K.conjBy t := fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc := (star_isComponent H K hK hq).commutator_eq_bot_of_ne
    (star_isComponent H _ hB hqB) (starImages_ne H K _ hKH hBH hK hB hne)
  change ⁅(K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)),
    ((K.conjBy t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))⁆ = ⊥ at hc
  rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hc
  let xH : H := ⟨x,hKH x.property⟩
  apply S.original_nonTensor_wreath_impossible_of_cubic D hZ z h
    (show IsMulCommutative ((D.fullSetup hZ T z).UH H) from inferInstance)
    r hmark hns (K.subgroupOf H) ((K.conjBy t).subgroupOf H) I hK hc hupper hlower
    (by simpa only [map_subgroupOf_eq_of_le hKH] using hout) t ht
    (by rw [map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hBH]; rfl)
    xH x.property hxL (Subtype.ext (congrArg (fun w : K => (w : G)) hx3))
  intro he
  exact hxn (Subtype.ext (congrArg (fun w : H => (w : G)) he))

end CFSG.Quasithin.Chapter12.Section06
