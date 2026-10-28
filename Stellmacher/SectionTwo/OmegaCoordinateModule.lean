module
public import Stellmacher.CentralizerQuotientAction
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.SectionOne.OneSevenSylowFixedCoordinate
public import Theory.GroupAction.NormalizingActor

/-!
# Ambient omega coordinate of a normal one-seven factor

Let V be a normal elementary abelian two-subgroup with Ω₁(Z(B)) ≤ V ≤ B.
For the action induced by the exact quotient by C_G(V), suppose a Sylow
two-subgroup of E maps onto the image of B and D is a normal one-seven
factor of E. If K has image D B and its two-residual has image D', then
[Ω₁(Z(B)), O²(K)] = [V, O²(K)] has order four, is normalized by the
preimage of E, and K has fixed index two on Ω₁(Z(B)).

The Sylow fixed space of V maps precisely to Ω₁(Z(B)): its elements are
central involutions of B, and the containment hypotheses give the reverse
inclusion. The one-seven fixed-coordinate theorem then supplies the
derived commutator module and fixed index. Quotient-action transport
identifies these with the ambient commutator and centralizer, while
normality of D gives invariance under E. All restrictions use the exact
centralizer quotient action occurring in the hypothesis.

This is the selected natural-module calculation used in Stellmacher (6.3),
including its opening application of (2.2) and the later fixed-index bound,
journal p. 31; source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionTwo
universe u

private theorem fixedPoints_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (N : Subgroup G) (A : Subgroup N) :
    FixedPoints.subgroup (A.map N.subtype) V = FixedPoints.subgroup A V := by
  ext v
  rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hv a
    exact hv ⟨((a : N) : G), Subgroup.mem_map_of_mem N.subtype a.property⟩
  · intro hv a
    obtain ⟨x, hx, hxa⟩ := a.property
    have h := hv ⟨x, hx⟩
    change (x : G) • v = v at h
    change (a : G) • v = v
    rw [← hxa]
    exact h

private theorem commutatorSubgroup_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (N : Subgroup G) (A : Subgroup N) (W : Subgroup V) :
    commutatorSubgroup (A.map N.subtype) V W = commutatorSubgroup A V W := by
  unfold commutatorSubgroup
  congr 1
  ext v
  constructor
  · rintro ⟨a, w, hw, rfl⟩
    obtain ⟨x, hx, heq⟩ := a.property
    refine ⟨⟨x, hx⟩, w, hw, ?_⟩
    change w⁻¹ * (a : G) • w = w⁻¹ * (x : G) • w
    change (x : G) = (a : G) at heq
    rw [heq]
  · rintro ⟨a, w, hw, rfl⟩
    exact ⟨⟨((a : N) : G), Subgroup.mem_map_of_mem N.subtype a.property⟩, w, hw, rfl⟩

public theorem omega_coordinate_module
    {G : Type u} [Group G] [Finite G]
    (V B : Subgroup G) (hVn : V.Normal) [IsElementaryAbelian 2 V]
    (hVB : V ≤ B) (hAV : omegaOneCenterAmbient B ≤ V)
    {X : Type u} [Group X] [Finite X] (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set G))
    (E : Subgroup X) (T : Sylow 2 E) (hT : (T : Subgroup E).map E.subtype = B.map q)
    (D : Subgroup E) [D.Normal] (K : Subgroup G)
    (hK : K.map q = D.map E.subtype ⊔ B.map q)
    (hR : (twoResidualAmbient K).map q = ((commutator D).map D.subtype).map E.subtype) :
    letI := centralizerQuotientAction V hVn q hq hker
    SectionOne.IsOneSevenFactor (V := V) D →
      ⁅omegaOneCenterAmbient B, twoResidualAmbient K⁆ = ⁅V, twoResidualAmbient K⁆ ∧
      Nat.card (⁅V, twoResidualAmbient K⁆ : Subgroup G) = 4 ∧
      E.comap q ≤ Subgroup.normalizer ((⁅V, twoResidualAmbient K⁆ : Subgroup G) : Set G) ∧
      (omegaOneCenterAmbient B ⊓ Subgroup.centralizer (K : Set G)).relIndex
        (omegaOneCenterAmbient B) = 2 := by
  let _ := centralizerQuotientAction V hVn q hq hker
  intro hD
  let A := FixedPoints.subgroup T V
  let M := commutatorAction D V
  let F := (commutator D).map D.subtype
  have hAmap : A.map V.subtype = omegaOneCenterAmbient B := by
    rw [show A = FixedPoints.subgroup T V from rfl,
      ← fixedPoints_map_subtype E (T : Subgroup E), hT,
      centralizerQuotientAction_fixedPoints_image_map V hVn q hq hker]
    apply le_antisymm
    · intro v hv
      apply (mem_omegaOneCenterAmbient_iff B v).mpr
      refine ⟨hVB hv.1, elemPow_eq_one_of_isElementaryAbelian v hv.1, ?_⟩
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp hv.2 b hb)
    · intro a ha
      refine ⟨hAV ha, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun b hb =>
        ((mem_omegaOneCenterAmbient_iff B a).mp ha).2.2 b hb)
  obtain ⟨_hline, hindex, hcommA⟩ := SectionOne.oneSevenFactor_sylow_fixed_coordinate T D hD
  change commutatorSubgroup F V A = M at hcommA
  have htransport (W : Subgroup V) :
      (commutatorSubgroup F V W).map V.subtype = ⁅W.map V.subtype, twoResidualAmbient K⁆ := by
    rw [← commutatorSubgroup_map_subtype E F W, ← hR]
    exact centralizerQuotientAction_commutatorSubgroup_image_map V hVn q hq hker _ W
  have hMV : M.map V.subtype = ⁅V, twoResidualAmbient K⁆ := by
    change (commutatorAction D V).map V.subtype = _
    rw [SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    change (commutatorSubgroup F V ⊤).map V.subtype = _
    rw [htransport, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hMA : M.map V.subtype = ⁅omegaOneCenterAmbient B, twoResidualAmbient K⁆ := by
    rw [← hcommA, htransport A, hAmap]
  have hnorm : E.comap q ≤ Subgroup.normalizer (M.map V.subtype : Set G) := by
    have hinv := commutatorAction_isInvariant_of_normalizing_actor
      (V := V) (⊤ : Subgroup E) D (Subgroup.le_normalizer_of_normal)
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg v hv
    obtain ⟨w, hw, rfl⟩ := hv
    let e : E := ⟨q g, hg⟩
    have hw' : e • w ∈ M := (hinv.invariant ⟨e, trivial⟩ w).mp hw
    refine ⟨e • w, hw', ?_⟩
    change ((q g • w : V) : G) = g * (w : G) * g⁻¹
    exact centralizerQuotientAction_smul_coe V hVn q hq hker g w
  have hfixmap : (A ⊓ FixedPoints.subgroup D V).map V.subtype =
      omegaOneCenterAmbient B ⊓ Subgroup.centralizer (K : Set G) := by
    have heq : A ⊓ FixedPoints.subgroup D V = FixedPoints.subgroup (K.map q) V := by
      ext v
      constructor
      · rintro ⟨hvA, hvD⟩
        have hBF : B.map q ≤ fixingSubgroup X ({v} : Set V) := by
          rw [← hT]
          rintro _ ⟨t, ht, rfl⟩
          rw [mem_fixingSubgroup_iff]
          intro w hw
          have hwv : w = v := Set.mem_singleton_iff.mp hw
          subst w
          exact (FixedPoints.mem_subgroup (M := T) (a := v)).mp hvA ⟨t, ht⟩
        have hDF : D.map E.subtype ≤ fixingSubgroup X ({v} : Set V) := by
          rintro _ ⟨d, hd, rfl⟩
          rw [mem_fixingSubgroup_iff]
          intro w hw
          have hwv : w = v := Set.mem_singleton_iff.mp hw
          subst w
          exact (FixedPoints.mem_subgroup (M := D) (a := v)).mp hvD ⟨d, hd⟩
        have hKF : K.map q ≤ fixingSubgroup X ({v} : Set V) := by
          rw [hK]
          exact sup_le hDF hBF
        rw [FixedPoints.mem_subgroup]
        intro k
        exact (mem_fixingSubgroup_iff (M := X)).mp (hKF k.property) v (Set.mem_singleton v)
      · intro hv
        rw [FixedPoints.mem_subgroup] at hv
        constructor
        · change v ∈ FixedPoints.subgroup T V
          rw [FixedPoints.mem_subgroup]
          intro t
          apply hv
            ⟨(t : E), (hK ▸ (show B.map q ≤ D.map E.subtype ⊔ B.map q from le_sup_right))
              (hT ▸ Subgroup.mem_map_of_mem E.subtype t.property)⟩
        · change v ∈ FixedPoints.subgroup D V
          rw [FixedPoints.mem_subgroup]
          intro d
          exact hv ⟨(d : E), (hK ▸ (show D.map E.subtype ≤ D.map E.subtype ⊔ B.map q from le_sup_left))
            (Subgroup.mem_map_of_mem E.subtype d.property)⟩
    have hsub : FixedPoints.subgroup (K.map q) V ≤ A := heq ▸ inf_le_left
    have hsubmap : V ⊓ Subgroup.centralizer (K : Set G) ≤ omegaOneCenterAmbient B := by
      rw [← centralizerQuotientAction_fixedPoints_image_map V hVn q hq hker K, ← hAmap]
      exact Subgroup.map_mono hsub
    rw [heq, centralizerQuotientAction_fixedPoints_image_map V hVn q hq hker]
    exact le_antisymm (le_inf hsubmap inf_le_right) (inf_le_inf_right _ hAV)
  refine ⟨hMA.symm.trans hMV, ?_, ?_, ?_⟩
  · rw [← hMV, Subgroup.card_map_of_injective V.subtype_injective]
    exact hD.2.2.1
  · rwa [hMV] at hnorm
  · rw [← hfixmap, ← hAmap,
      Subgroup.relIndex_map_map_of_injective _ _ V.subtype_injective]
    exact hindex

end Stellmacher.SectionTwo

