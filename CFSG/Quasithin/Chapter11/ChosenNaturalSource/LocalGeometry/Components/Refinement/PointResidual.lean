module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.PointFixer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked

/-!
# The point-fixer lift and the PSL₂(25) exclusion

In each of the three marked natural models, a group element fixing the first
field line pointwise belongs to the solvable residual of its stabilizer.
A single conjugating element aligns the flag, and the established residual
projection lifts that model element to the literal ambient L₁. The formula on
representatives then makes the original Sylow automorphism of L₁/O₂(L₁) inner.
This contradicts the outer witness supplied by a PSL₂(25) containing component.

All transports use the original point preimage, retaining C_V(L), and the
original two-core quotient maps. No exhaustive embedding list is assumed
for this individual exclusion.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem embedded_residual_map {A : Type*} [Group A] [Finite A]
    (e : A ≃* A) (H : Subgroup A) :
    (solvableResidual (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype =
      ((solvableResidual H).map H.subtype).map e.toMonoidHom := by
  have hc : (H.map e.toMonoidHom).comap e.toMonoidHom = H := by
    rw [comap_map_eq,e.toMonoidHom.ker_eq_bot e.injective,sup_bot_eq]
  have hh := map_solvableResidual_comap e.toMonoidHom e.surjective (H.map e.toMonoidHom)
  rw [hc] at hh
  exact hh.symm

private theorem conjugate_fixes {F A W : Type*} [Field F] [Group A]
    [AddCommGroup W] [Module F W] (ρ : Representation F A W)
    (P : Submodule F W) (b g : A)
    (h : ∀ v ∈ P.map (ρ b), ρ g v = v) (v : W) (hv : v ∈ P) :
    ρ (b⁻¹*g*b) v = v := by
  have hh := congrArg (ρ b⁻¹) (h (ρ b v) ⟨v,hv,rfl⟩)
  simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
    Module.End.one_apply,mul_assoc] using hh

private theorem g2_point_fixer {F : Type*} [Field F] [Finite F] [CharP F 2]
    (g : Atlas.G2.Model F)
    (h : ∀ v ∈ Atlas.G2.Natural.OrthogonalCover.SylowFlag.N1 F,
      Atlas.G2.Natural.action F g v = v) :
    g ∈ Atlas.G2.LieParabolicSetup.local₂ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover.SylowFlag
    Atlas.G2.LieParabolicSetup in
  have hn : g ∈ parabolic₂ := by
    rw [← G2.ResidualIncidence.point_stabilizer F]
    change ∀ v, Natural.action F g v ∈ N1 F ↔ v ∈ N1 F
    intro v
    constructor
    · intro hv
      have he := h _ hv
      exact ((Natural.action F).apply_bijective g).injective he ▸ hv
    · intro hv
      rw [h v hv]
      exact hv
  open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover.SylowFlag
    Atlas.SplitOctonion Atlas.G2.LieParabolicSetup in
  obtain ⟨b,hb⟩ := mem_pointStabilizer_iff g |>.mp
    ((parabolic_eq_pointStabilizer (F := F)).le hn)
  open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover.SylowFlag
    Atlas.SplitOctonion Atlas.G2.LieParabolicSetup in
  have he : traceZeroAction F g (pointVector F) = (b : F) • pointVector F := by
    apply Subtype.ext
    have hp : (pointVector F).val = (basisVector 0 : Carrier F) := by
      ext i
      fin_cases i <;> simp [pointVector,Atlas.G2.Natural.OrthogonalCover.planeLift,basisVector]
    change g.val (pointVector F).val = (b : F) • (pointVector F).val
    rw [hp]
    exact hb
  open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover.SylowFlag
    Atlas.SplitOctonion Atlas.G2.LieParabolicSetup in
  have hb1 : (b : F) = 1 := by
    apply smul_left_injective F (point_class_ne_zero F)
    have hh := h (mk F (pointVector F)) (by rw [N1_eq_span]; exact Submodule.mem_span_singleton_self _)
    rw [action_mk,he,map_smul] at hh
    simpa using hh
  rw [Atlas.G2.LieParabolicSetup.local₂_eq_fixingFirstVector]
  change g.val (Atlas.SplitOctonion.basisVector 0) = _
  simpa only [Units.smul_def,hb1,one_smul] using hb

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

set_option backward.isDefEq.respectTransparency false in
/-- A natural model element fixing the marked point has a representative in L₁. -/
theorem point_model_fixer_lifts_to_residual (g : c.ModelGroup)
    (hfix : ∀ v ∈ f.space 0, c.modelAction g v = v) :
    ∃ l : f.Li 0, c.quotientMap ⟨l,(localResidual_le _ l.property).1⟩ = g := by
  cases c with
  | sl3 m =>
    change Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier at g
    have hs := SL3.flag_unique D S m 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    let b := SL3.alignment D S m
    have hg : b⁻¹*g*b ∈ Matrix.PSL3.LinearThree.pointLocalSL S.field.Carrier := by
      change specialLinearNatural 3 (b⁻¹*g*b) (![1,0,0] : Fin 3 → S.field.Carrier) = _
      apply conjugate_fixes (specialLinearNatural 3) (SL3.Model.point (F := S.field.Carrier)) b g
      · rw [hs] at hfix
        exact hfix
      · exact ⟨rfl,rfl⟩
    obtain ⟨l,hl,he⟩ := (SL3.PlaneAction.local_image D S m 0).ge hg
    refine ⟨⟨l,?_⟩,?_⟩
    · change l.val ∈ localResidual L ((Coordinates.sl3 m).preimage (f.space 0))
      rw [hs]
      exact hl
    · apply (MulAut.conj b⁻¹).injective
      change (MulAut.conj b⁻¹) ((Coordinates.sl3 m).quotientMap l) = b⁻¹*g*b at he
      simpa only [MulAut.conj_apply,inv_inv] using he
  | sp4 m =>
    change Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier at g
    have hs := Sp4.flag_unique m S 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    let b := Sp4.alignment m
    have hg : b⁻¹*g*b ∈ Theory.SpecificGroups.SymplecticFour.pointLocal := by
      rw [Theory.SpecificGroups.SymplecticFour.mem_pointLocal_iff_fixed]
      apply conjugate_fixes (symplecticNatural 2)
        (Theory.SpecificGroups.SymplecticFour.point S.field.Carrier) b g
      · rw [hs] at hfix
        change ∀ v ∈ (Theory.SpecificGroups.SymplecticFour.point S.field.Carrier).map
          (symplecticNatural 2 b), symplecticNatural 2 g v = v at hfix
        exact hfix
      · exact Submodule.mem_span_singleton_self _
    have hm : g ∈ (solvableResidual ((Coordinates.sp4 m).modelStabilizer (f.space 0))).map
        ((Coordinates.sp4 m).modelStabilizer (f.space 0)).subtype := by
      have hstab : (Coordinates.sp4 m).modelStabilizer (f.space 0) =
          (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := S.field.Carrier)).map
            (MulAut.conj b).toMonoidHom := by
        rw [hs]
        exact Sp4.modelStabilizer_space m 0
      rw [hstab,embedded_residual_map]
      change g ∈ ((solvableResidual
        (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := S.field.Carrier))).map
          (Theory.SpecificGroups.SymplecticFour.pointParabolic.subtype)).map
            (MulAut.conj b).toMonoidHom
      rw [mem_map_equiv,
        Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq
          S.field.card_eq S.nonbinary]
      simpa only [MulAut.conj_symm_apply] using hg
    obtain ⟨y,hy,hyval⟩ := hm
    obtain ⟨l,hl⟩ := (Coordinates.sp4 m).residualProjection_surjective (f.space 0) ⟨y,hy⟩
    refine ⟨l,?_⟩
    rw [← Coordinates.residualProjection_coe,hl]
    exact hyval
  | g2 m =>
    change Atlas.G2.Model S.field.Carrier at g
    have hs := G2.flag_unique S m 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    let b := (G2.ResidualIncidence.alignment S m).val
    have hg : b⁻¹*g*b ∈ Atlas.G2.LieParabolicSetup.local₂ := by
      apply g2_point_fixer
      apply conjugate_fixes (Atlas.G2.Natural.action S.field.Carrier)
        (Atlas.G2.Natural.OrthogonalCover.SylowFlag.N1 S.field.Carrier) b g
      rw [hs,G2.ResidualIncidence.flag_space_eq S m 0] at hfix
      change ∀ v ∈ (Atlas.G2.Natural.OrthogonalCover.SylowFlag.N1 S.field.Carrier).map
        (Atlas.G2.Natural.action S.field.Carrier b),
          Atlas.G2.Natural.action S.field.Carrier g v = v at hfix
      exact hfix
    obtain ⟨l,hl⟩ := G2.ResidualIncidence.localProjection_surjective S m 0 ⟨b⁻¹*g*b,hg⟩
    refine ⟨⟨l,?_⟩,?_⟩
    · change l.val ∈ localResidual L ((Coordinates.g2 m).preimage (f.space 0))
      rw [hs]
      exact l.property
    · apply (MulAut.conj b⁻¹).injective
      simpa only [MulAut.conj_apply,inv_inv] using
        (G2.ResidualIncidence.localProjection_coe S m 0 l).symm.trans
          (congrArg Subtype.val hl)

set_option backward.isDefEq.respectTransparency false in
/-- A Sylow element centralizing the full V₁ acts innerly on L₁/O₂(L₁). -/
theorem point_centralizing_sylow_inner_on_first (t : T)
    (ht : (t : G) ∈ centralizer (f.Vi 0 : Set G)) :
    Closure.coreQuotientAction (f.Li 0) ⟨t,f.sylow_normalizes_Li 0 t.property⟩ ∈
      MulAut.innerSubgroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := by
  obtain ⟨g,_,hg,ha⟩ := point_centralizing_sylow_model_operator D S f t ht
  obtain ⟨l,hl⟩ := point_model_fixer_lifts_to_residual D S f g hg
  refine ⟨QuotientGroup.mk' (pCore 2 (f.Li 0)) l,?_⟩
  ext x : 1
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (f.Li 0)) x
  rw [MulAut.conj_apply,← map_inv,← map_mul,← map_mul,Closure.coreQuotientAction_apply_mk]
  apply (c.residualCoreQuotientEquiv (f.space 0)).injective
  change QuotientGroup.mk' _ (c.residualProjection (f.space 0) (l*b*l⁻¹)) =
    QuotientGroup.mk' _ (c.residualProjection (f.space 0)
      ((f.Li 0).normalizerMonoidHom ⟨t,f.sylow_normalizes_Li 0 t.property⟩ b))
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [Coordinates.residualProjection_coe,Coordinates.residualProjection_coe]
  change c.quotientMap (⟨l,(localResidual_le _ l.property).1⟩ *
    ⟨b,(localResidual_le _ b.property).1⟩ * ⟨l,(localResidual_le _ l.property).1⟩⁻¹) =
      c.quotientMap (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t)
        ⟨b,(localResidual_le _ b.property).1⟩)
  rw [map_mul,map_mul,map_inv,hl]
  exact (ha ⟨b,(localResidual_le _ b.property).1⟩).symm

/-- The PSL₂(25) branch of the first-normalizer embedding list is impossible. -/
theorem first_component_not_twentyFive
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 := by
  intro hk
  obtain ⟨t,ht,_,htfix,hout⟩ :=
    first_twentyFive_outer_centralizes_point D S f hm hfour hfix hK hLK hk
  exact hout (point_centralizing_sylow_inner_on_first D S f ⟨t,ht⟩ htfix)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
