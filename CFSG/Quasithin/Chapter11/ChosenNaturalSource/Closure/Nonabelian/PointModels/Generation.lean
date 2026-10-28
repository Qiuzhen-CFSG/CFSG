module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointLifting

/-!
# From distinct model lines to the original quotient point generation

An original subgroup avoiding all L-conjugates of V₁ contains vectors on two
distinct field lines: transitivity places its first nonzero vector on a
conjugate of V₁, and avoidance supplies a second vector outside that line.
The original point residuals map onto the line residuals in the same marked
model. Thus generation by the two model line residuals gives generation in
the literal L/O₂(L), and the existing perfect-kernel lifting theorem supplies
actual generation in L.

LinePairGeneration is the remaining model obligation, separately for full SL₃
and Sp₄ over the nonbinary field. The source intersection application is
conditional on that calculation; it does not claim to establish 11.5.3.
Source: Aschbacher--Smith, 11.5.3(1--2), printed p.779.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : CFSG.Quasithin.ChapterB.QuasisimpleSource.BinaryField}

private theorem span_preimage_le_conjugate (c : Coordinates D F)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (U : Submodule F.Carrier c.Space) (z : V)
    (hz : (c.projection z).toAdd ∈ U) (l : L) :
    c.preimage (Submodule.span F.Carrier
      {c.modelAction (c.quotientMap l) (c.projection z).toAdd}) ≤
      (c.preimage U).map (MulAut.conj l.val : G →* G) := by
  intro v hv
  have hvV := D.centralQuotientPreimage_le _ hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((c.mem_preimage _ ⟨v, hvV⟩).mp hv)
  obtain ⟨x, hx⟩ := c.projection_surjective
    (Multiplicative.ofAdd (a • (c.projection z).toAdd))
  have hxU : x.val ∈ c.preimage U := (c.mem_preimage U x).mpr (by
    change (c.projection x).toAdd ∈ U
    rw [hx]
    exact U.smul_mem a hz)
  refine ⟨x.val, hxU, ?_⟩
  have he : V.normalizerMonoidHom (inclusion D.normalizes l) x = ⟨v, hvV⟩ := by
    apply projection_injective c hfixed
    apply Multiplicative.toAdd.injective
    rw [c.projection_component_conjugation, hx]
    change c.modelAction (c.quotientMap l) (a • (c.projection z).toAdd) = _
    rw [map_smul]
    exact ha
  exact congrArg Subtype.val he

open CFSG.Quasithin.ChapterB.QuasisimpleSource
/-- Residuals of two distinct field-line stabilizers generate the full model. -/
def LinePairGeneration (F : BinaryField) {H W : Type*} [Group H]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] (ρ : Representation F.Carrier H W) : Prop :=
  ∀ U₁ U₂ : Submodule F.Carrier W,
    Module.finrank F.Carrier U₁ = 1 → Module.finrank F.Carrier U₂ = 1 → U₁ ≠ U₂ →
    residualIn (BinaryOffender.subspaceStabilizer (restrictScalars (k := ZMod 2) ρ)
      (U₁.restrictScalars (ZMod 2))) ⊔
    residualIn (BinaryOffender.subspaceStabilizer (restrictScalars (k := ZMod 2) ρ)
      (U₂.restrictScalars (ZMod 2))) = ⊤

/-- Transport two-line generation to the actual original point-residual images. -/
theorem quotientPointGeneration_of_linePair
    {E : Geometry D} (F₀ : MarkedFlag E)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hgen : LinePairGeneration E.input.field F₀.action.coordinates.modelAction) :
    QuotientPointGeneration L V E.V₁ := by
  let c := F₀.action.coordinates
  let U₀ := F₀.flag.space 0
  have hline : E.V₁ = c.preimage U₀ := by
    change D.centralQuotientPreimage E.point = _
    rw [F₀.point_eq]
    rfl
  let z : V := ⟨E.z, E.V₁_le hz⟩
  have hzU : (c.projection z).toAdd ∈ U₀ :=
    (c.mem_preimage U₀ z).mp (hline ▸ hz)
  have hnonzero (v : V) (hv : v.val ≠ 1) : (c.projection v).toAdd ≠ 0 := by
    intro he
    apply hv
    exact congrArg Subtype.val (projection_injective c hfixed
      (he.trans (map_one c.projection).symm))
  intro A hAV havoid
  have hA : A ≠ ⊥ := by
    intro he
    exact havoid 1 L.one_mem (he ▸ bot_le)
  obtain ⟨u, hu, hu1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  let u' : V := ⟨u, hAV hu⟩
  let U := Submodule.span E.input.field.Carrier {(c.projection u').toAdd}
  obtain ⟨l, hl, hlu⟩ := htrans E.z z.property hz1 u u'.property hu1
  have hlu' : V.normalizerMonoidHom (inclusion D.normalizes ⟨l, hl⟩) z = u' :=
    Subtype.ext hlu
  have hUavoid : ¬ A ≤ c.preimage U := by
    intro h
    apply havoid l hl
    have hconj := span_preimage_le_conjugate c hfixed U₀ z hzU ⟨l, hl⟩
    rw [← c.projection_component_conjugation, hlu'] at hconj
    rw [hline]
    exact h.trans hconj
  obtain ⟨v, hv, hvU⟩ := SetLike.not_le_iff_exists.mp hUavoid
  let v' : V := ⟨v, hAV hv⟩
  have hv1 : v ≠ 1 := by
    intro he
    exact hvU (he ▸ (c.preimage U).one_mem)
  let W := Submodule.span E.input.field.Carrier {(c.projection v').toAdd}
  have hU : Module.finrank E.input.field.Carrier U = 1 :=
    finrank_span_singleton (hnonzero u' hu1)
  have hW : Module.finrank E.input.field.Carrier W = 1 :=
    finrank_span_singleton (hnonzero v' hv1)
  have hUW : U ≠ W := by
    intro he
    apply hvU
    apply (c.mem_preimage U v').mpr
    rw [he]
    exact Submodule.mem_span_singleton_self _
  have hmodel := hgen U W hU hW hUW
  change residualIn (c.modelStabilizer U) ⊔ residualIn (c.modelStabilizer W) = ⊤ at hmodel
  have hres (t : G) (ht : t ∈ A) (ht1 : t ≠ 1)
      (P : Submodule E.input.field.Carrier c.Space)
      (hP : Module.finrank E.input.field.Carrier P = 1)
      (htP : (c.projection ⟨t, hAV ht⟩).toAdd ∈ P) :
      residualIn (c.modelStabilizer P) ≤
        ((pointResidualJoin L A).subgroupOf L).map c.quotientMap := by
    rw [← model_residual_image c P,
      ← pointResidual_eq_localResidual c P hP hfixed ⟨t, hAV ht⟩ htP
        (fun he => ht1 (congrArg Subtype.val he))]
    apply map_mono
    exact comap_mono (le_iSup (fun u : {u : G // u ∈ A ∧ u ≠ 1} =>
      pointResidual L u.val) ⟨t, ht, ht1⟩)
  have htop : ((pointResidualJoin L A).subgroupOf L).map c.quotientMap = ⊤ := by
    apply top_unique
    rw [← hmodel]
    exact sup_le
      (hres u hu hu1 U hU (Submodule.mem_span_singleton_self _))
      (hres v hv hv1 W hW (Submodule.mem_span_singleton_self _))
  have he := congrArg (Subgroup.comap c.groupEquiv.toMonoidHom) htop
  simpa only [Coordinates.quotientMap, ← map_map,
    comap_map_eq_self_of_injective (f := c.groupEquiv.toMonoidHom)
      c.groupEquiv.injective, comap_top] using he

/-- The actual intersection and rank consumer. Only the two-line model
calculation and the named preceding source conclusions remain explicit. -/
theorem intersection_and_rank_of_linePair
    {E : Geometry D} (F₀ : MarkedFlag E)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : E.Kz = E.K)
    (hgen : LinePairGeneration E.input.field F₀.action.coordinates.modelAction)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hKL : E.K = E.L₁) :
    (∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        E.V₁.map (MulAut.conj l : G →* G)) ∧
      (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ ChapterE.globalR V :=
  intersection_and_rank_of_quotient D E F₀ hfixed hz hz1 htrans
    (pointResidual_eq F₀ hfixed hz hz1) hK
    (quotientPointGeneration_of_linePair F₀ hfixed hz hz1 htrans hgen) hTI hKL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
