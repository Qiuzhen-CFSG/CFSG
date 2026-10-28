module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Quiet
public import Theory.Representation.PSL3Two.NaturalDualFixedGeneration
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# Literal orbit preparation for the natural–dual row

The point two-group acts on the given six-dimensional conjugation coordinates
and normalizes the original binary-three action. Its fixed vectors generate
the natural–dual pair, so their L-orbit is the whole moved subgroup and is
contained in the literal I-orbit VI. This controls the ambient centralizer.
When J(T) fixes the full module, Thompson equality and movement complete
preparation and give the actual faithful FF action.

This proves the geometric step for row 10.1.1(5) in Aschbacher–Smith 10.2.9,
printed p.751. Row recognition and full-module fixedness remain with the
final assembly owner qt-d-10-nona5-point-constrained.
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
private theorem naturalDual_moved_fixed_span (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (P : Subgroup G) (hPL : P ≤ normalizer (L : Set G))
    (hPW : P ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) (hP : IsPGroup 2 P) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  let W := ⁅D.fullModule,L⁆
  let A := conjugateSpanBy (W ⊓ centralizer (P : Set G)) L
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hi : Function.Injective s.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [s.kernel_eq,bot_subgroupOf])
  have hPA : P ≤ normalizer (A : Set G) := normalizes_conjugateSpanBy _ _ _
    ((le_inf hPW (P.le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf) hPL
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
  have hK : s.imageSpace A = ⊤ := by
    apply BinaryLinearThree.NaturalDual.fixed_generates η hP a hηa
    · intro g x hx
      obtain ⟨l,rfl⟩ := hq g
      obtain ⟨w,hw,rfl⟩ := (s.mem_imageSpace_iff A x).mp hx
      exact (s.mem_imageSpace_iff A _).mpr
        ⟨⟨l*w*(l : G)⁻¹,(mem_normalizer_iff.mp (s.normalized l.property) w).mp w.property⟩,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _ l.property) w).mp hw,
          s.equivariant l w⟩
    · intro p x hx
      obtain ⟨w,hw,rfl⟩ := (s.mem_imageSpace_iff A x).mp hx
      rw [hη]
      exact (s.mem_imageSpace_iff A _).mpr
        ⟨_,(mem_normalizer_iff.mp (hPA p.property) w).mp hw,rfl⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := s.onto (Multiplicative.ofAdd x)
      apply (s.mem_imageSpace_iff A _).mpr
      refine ⟨w,le_conjugateSpanBy _ _ ⟨w.property,?_⟩,rfl⟩
      intro p hp
      have he := hx ⟨p,hp⟩
      change η ⟨p,hp⟩ (s.coordinates w).toAdd = (s.coordinates w).toAdd at he
      rw [hη] at he
      have hh := congrArg Subtype.val (hi (Multiplicative.toAdd.injective he))
      exact mul_inv_eq_iff_eq_mul.mp hh
  apply le_antisymm (conjugateSpanBy_le inf_le_left s.normalized)
  intro w hw
  obtain ⟨z,hz,hzw⟩ := (s.mem_imageSpace_iff A (s.coordinates ⟨w,hw⟩).toAdd).mp
    (hK ▸ Submodule.mem_top)
  have he := congrArg Subtype.val (hi (Multiplicative.toAdd.injective hzw))
  change (z : G) = w at he
  change (z : G) ∈ A at hz
  change w ∈ A
  exact he ▸ hz

/-- The marked natural–dual row generates the whole original moved factor. -/
theorem Context.moved_le_of_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  have hPW : pointSylow T v ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T))
      c.escaping.sylow_normalizes).trans (source_moved_normalizer_local_containment D)
  rw [←naturalDual_moved_fixed_span D e s (pointSylow T v)
    c.escaping.sylow_normalizes hPW (T.isPGroup'.to_le inf_le_left)]
  exact conjugateSpanBy_mono le_rfl c.escaping.strict.le

/-- The natural–dual orbit controls its actual ambient centralizer. -/
theorem Context.centralizer_le_of_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal :=
  c.centralizer_le_of_moved_le (c.moved_le_of_naturalDual e s)

/-- The quiet natural–dual row now supplies complete preparation. The
source-row recognition and quietness remain with this task's final
assembly, qt-d-10-nona5-point-constrained. -/
theorem Context.prepared_of_quiet_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    Prepared D v I := c.prepared_of_centralizer_of_thompson_eq
      (c.centralizer_le_of_naturalDual e s) (c.thompson_eq_of_fullModule_centralized hJ)

/-- Consumer: the literal reduced orbit carries the faithful FF action. -/
theorem Context.actionFacts_of_quiet_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    ActionFacts c := c.actionFacts (c.prepared_of_quiet_naturalDual e s hJ)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
