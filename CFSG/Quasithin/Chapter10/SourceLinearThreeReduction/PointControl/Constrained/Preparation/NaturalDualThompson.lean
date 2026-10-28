module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDual
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.Representation.BinaryConjugationSection.ThompsonCentralization

/-!
# Original Thompson fixedness for the natural–dual row

The actual half-Sylow normalizes the marked moved factor. Its faithful
coordinate action has no FF offenders, so maximum elementary subgroups
fix that original factor. Thompson heredity identifies their join with
J(T), and T-conjugation gives fixation of both original moved factors,
hence of D.fullModule. This removes the quietness premise from preparation
and from the faithful FF-action consumer on the literal reduced orbit.

Recognition of the natural–dual marking, the other original source rows,
and containing-model recognition remain with the final assembly owner
qt-d-10-nona5-point-constrained.
Source: Aschbacher–Smith 10.1.2(1) and10.2.9, printed pp.742 and751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

set_option backward.isDefEq.respectTransparency false in
/-- The marked original natural–dual row forces J(T) to fix the full module. -/
theorem Context.thompson_centralizes_fullModule_of_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let P := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hPW : P ≤ normalizer (W : Set G) := inf_le_right
  have hPL : P ≤ normalizer (L : Set G) := inf_le_left
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hWT : W ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)).trans
      (D.fullModule_le_sylow (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal))
  have hWS : W ≤ S := le_inf hWT ((source_full_moved_le_component D).trans L.le_normalizer)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨η,hη⟩ := s.exists_original_quotient_action hPW (by rw [normalizer_eq_top]; exact le_top)
  let a : P →* MulAut BinaryLinearThree.Group :=
    (MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPL)))
  have ha (p : P) (l : L) : a p (q l) = q (L.normalizerMonoidHom (inclusion hPL p) l) := by
    change e (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion hPL p)) (e.symm (e (QuotientGroup.mk' _ l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hηa : ∀ p g x, η p (BinaryLinearThree.NaturalDual.action g x) =
      BinaryLinearThree.NaturalDual.action (a p g) (η p x) := by
    intro p g x
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨w,rfl⟩ := s.onto (Multiplicative.ofAdd x)
    change η p (BinaryLinearThree.NaturalDual.action (q l) (s.coordinates w).toAdd) =
      BinaryLinearThree.NaturalDual.action (a p (q l)) (η p (s.coordinates w).toAdd)
    have hs (k : L) (z : W) :
        (s.coordinates ⟨k*z*(k:G)⁻¹,
          (mem_normalizer_iff.mp (s.normalized k.property) z).mp z.property⟩).toAdd =
        BinaryLinearThree.NaturalDual.action (q k) (s.coordinates z).toAdd := s.equivariant k z
    rw [←hs,hη,ha,hη,←hs]
    apply congrArg (fun z : W => (s.coordinates z).toAdd)
    apply Subtype.ext
    change (p : G)*((l : G)*w*(l : G)⁻¹)*(p : G)⁻¹ =
      ((p : G)*l*(p : G)⁻¹)*((p : G)*w*(p : G)⁻¹)*((p : G)*l*(p : G)⁻¹)⁻¹
    group
  have hJS : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (le_inf (sSup_le fun _ hA => hA.1) D.thompson_normalizes_component) inf_le_left
  have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
    rw [←hJS]
    exact s.thompson_centralizes_of_nonFF_extension hPW hWS (le_inf inf_le_right hSW)
      η hη (BinaryLinearThree.NaturalDual.not_isFFModule_image_of_covariance η a hηa)
  have hconj (u : G) (hu : u ∈ (T : Subgroup G)) :
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer ((W.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) := by
    have h := map_mono (f := (MulAut.conj u).toMonoidHom) hJC
    rw [Theory.GroupTheory.map_centralizer_equiv] at h
    have hn : u ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
      normalizer_le_normalizer_elementaryAbelianMaxJ _ ((T : Subgroup G).le_normalizer hu)
    have he : (elementaryAbelianMaxJ (T : Subgroup G)).map
        (MulAut.conj u).toMonoidHom = elementaryAbelianMaxJ (T : Subgroup G) :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [he] at h
    exact h
  obtain ⟨u,hu,_,_,hfull,_⟩ := source_nonnormal_fullModule_pair D
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem))
  rw [hfull]
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp hJC) (le_centralizer_iff.mp (hconj u hu))

/-- Preparation now follows from the original marking alone. -/
theorem Context.prepared_of_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Prepared D v I :=
  c.prepared_of_quiet_naturalDual e s (c.thompson_centralizes_fullModule_of_naturalDual e s)

/-- The original reduced orbit carries the actual faithful FF action. -/
theorem Context.actionFacts_of_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ActionFacts c := c.actionFacts (c.prepared_of_naturalDual e s)
end CFSG.Quasithin.Chapter10.PointControl.Constrained
