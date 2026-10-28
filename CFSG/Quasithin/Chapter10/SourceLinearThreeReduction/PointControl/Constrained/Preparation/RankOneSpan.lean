module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.FixedVector
public import Theory.GroupTheory.Commutator.CentralQuotientSaturation

/-!
# The whole moved span in a rank-one natural cover

A two-subgroup normalizing the original component and full module fixes a
vector with nonzero natural coordinates, by the central-cover fixed-vector
theorem. SL₂ transitivity makes its component orbit surject onto the natural
quotient. Since the kernel is central and the original subgroup is fully
moved, central-quotient saturation recovers the whole subgroup [V,L]. This
works with a positive fixed kernel and does not require a splitting.

At the literal point Sylow this gives [V,L] ≤ VI. The original Baumann orbit
and point saturation then give preparation and the actual FF action. The
containing-action applications are in Models.RankOne; final row recognition
remains with qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith 10.2.9, printed p.751, using I.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

set_option backward.isDefEq.respectTransparency false in
/-- The fixed seed generates the original moved subgroup, including its fixed kernel. -/
theorem rankOne_moved_fixed_span
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (P : Subgroup G) (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G))
    (hP : IsPGroup 2 P) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) L = ⁅D.fullModule,L⁆ := by
  obtain ⟨w,hw,hwne⟩ := MovingHall.source_natural_moved_noncentral_fixed_vector D n hn hF e s P hPM hPL hP
  let W := ⁅D.fullModule,L⁆
  let A := conjugateSpanBy (W ⊓ centralizer (P : Set G)) L
  have hAW : A ≤ W := conjugateSpanBy_le inf_le_left s.normalized
  have hA : L ≤ normalizer (A : Set G) := le_normalizer_conjugateSpanBy _ _
  apply eq_of_central_quotient_surjective L W A hAW hA
    (source_full_moved_eq_commutator D) s.coordinates
  · rw [s.kernel_eq]
    exact comap_mono (show sourceMovedFixed D ≤ centralizer (L : Set G) from inf_le_right)
  · intro v
    by_cases hv : v = 1
    · exact ⟨1,by simp [hv]⟩
    have hwn : (s.coordinates w).toAdd ≠ 0 := hwne
    have hvn : v.toAdd ≠ 0 := hv
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (s.coordinates w).toAdd v.toAdd hwn hvn
    obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    let a : A := ⟨l*w*(l:G)⁻¹,
      (mem_normalizer_iff.mp (hA l.property) w).mp
        (le_conjugateSpanBy _ _ ⟨w.property,hw⟩)⟩
    refine ⟨a,Multiplicative.toAdd.injective ?_⟩
    have he := s.equivariant l w
    change (s.coordinates (inclusion hAW a)).toAdd =
      SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)) (s.coordinates w).toAdd at he
    change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
    rw [hl] at he
    exact he.trans hg

variable {D} {t v : G} {I : Subgroup G}

/-- The actual point orbit contains the full moved subgroup of every rank-one cover. -/
theorem Context.moved_le_of_rankOne_cover (c : Context D t v I)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  rw [←rankOne_moved_fixed_span D n hn hF e s (pointSylow T v)
    (inf_le_left.trans (le_normalizer_componentOrbit L T)) c.escaping.sylow_normalizes
    (T.isPGroup'.to_le inf_le_left)]
  exact conjugateSpanBy_mono le_rfl c.escaping.strict.le

/-- The marked rank-one cover supplies all original preparation conclusions. -/
theorem Context.prepared_of_rankOne_cover (c : Context D t v I)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Prepared D v I := by
  apply c.prepared_of_centralizer_of_thompson_eq
    (c.centralizer_le_of_moved_le (c.moved_le_of_rankOne_cover n hn hF e s))
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from pow_lt_pow_right₀ (by decide) hn)
  obtain ⟨m,hm,hfix⟩ := Selection.RankOne.partner_baumann_conjugate_fixed D e s hlarge
    c.escaping.t_mem c.escaping.v_mem
  apply source_point_thompson_eq_of_conjugate_fixed D
    (c.escaping.sylow.restrict
      (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right) inf_le_right)
  exact ⟨m,hm,(map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann _)).trans hfix⟩

/-- Preparation gives the literal faithful FF action, without a fixed-kernel premise. -/
theorem Context.actionFacts_of_rankOne_cover (c : Context D t v I)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ActionFacts c := c.actionFacts (c.prepared_of_rankOne_cover n hn hF e s)

omit [Field F] [Finite F] [CharP F 2] in
/-- The original source-row marking also gives full moved-span inclusion. -/
theorem Context.moved_le_of_rankOneNatural (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) : ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  obtain ⟨n,hn,e,⟨s⟩⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  exact c.moved_le_of_rankOne_cover n hn (GaloisField.card 2 n (by omega)) e s

end CFSG.Quasithin.Chapter10.PointControl.Constrained
