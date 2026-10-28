module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.Quotient
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.SquareRoots
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.MarkedAction

/-!
# Assembly of the marked involution-centralizer core calculation

The outside-core orbit at z supplies the conjugacy z ∼ uz for either allowed
choice of u. Transport carries the original hypotheses to b = uz, with the
intrinsic generalized Fitting subgroup retained. The square-root assertion
from 4.6 places the literal quaternion intersection P ∩ L in Q_b. The marked
commutator calculation then places r outside Q_b, and the two-subgroup image
in the S₃ quotient proves rz ∈ Q_b.

The final assembly discharges the outside-core orbit, square-root assertion,
and marked commutator calculation using their source producers. It supplies
CoreData from the original local hypotheses and the explicit marked geometry,
independently of the ambient normalizer involution v.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 2.3, 2.7, the observation in 4.6, and 4.10, pp.40–42.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- Forget only the second involution and order conclusions of SourceGeometry. -/
@[expose] def selected (a : SourceGeometry h) : SelectedFusionData h where
  g := a.g
  fused_mem := a.fused_mem
  fused_ne := a.fused_ne
  intersection_elementary := a.intersection_elementary
  intersection_card := a.intersection_card
  intersection_ne_fusion := a.intersection_ne_fusion
  u := a.u
  u_order := a.u_order
  u_centralizes := a.u_centralizes
  u_conjugate_core := a.u_conjugate_core
  u_not_core := a.u_not_core
  u_fused := a.u_fused
  u_inverts_X := a.u_inverts_X

/-- The existing local orbit contract supplies fusion of the literal b. -/
theorem b_fused_of_orbits (s : SymmetricSixData h a) (o : Census.OrbitData z a.u) :
    IsConj z (s.u * z) := by
  have hzsq : z * z = 1 := by
    simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  have hbQ : s.u * z ∉ coreInG z := by
    intro hb
    rcases s.u_choice with he | he
    · have hh := (coreInG z).mul_mem hb h.involution_mem_coreInG
      apply a.u_not_core
      simpa only [he, mul_assoc, hzsq, mul_one] using hh
    · apply a.u_not_core
      simpa only [he, mul_assoc, hzsq, mul_one] using hb
  have hbH : s.u * z ∈ Centralizer z := mem_centralizer_singleton_iff.mpr
    (s.u_commutes_z.mul_left (Commute.refl z)).eq
  obtain ⟨c, hc⟩ := o.outside_transitive (s.u * z) hbH hbQ s.uz_order
  exact a.u_fused.trans (isConj_iff.mpr ⟨c, hc⟩)

/-- The source square-root assertion contains the whole marked quaternion eight. -/
theorem quaternion_le_core_of_squareRootClosed (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (hb : Hypotheses (s.u * z)) (hsq : SquareRootClosed (s.u * z)) :
    m.P ⊓ m.L ≤ coreInG (s.u * z) := by
  let b := s.u * z
  have hbP : b ∈ m.P := by
    apply map_subtype_le (center m.P)
    rw [m.center_P]
    exact mem_zpowers b
  have hbR : b ∈ m.P ⊓ m.L := ⟨hbP, m.b_mem_K.1⟩
  obtain ⟨e⟩ := m.quaternion
  let w : (m.P ⊓ m.L : Subgroup G) := ⟨b, hbR⟩
  have hw : e w ≠ 1 := fun he => s.uz_ne_one
    (congrArg Subtype.val (e.injective (he.trans e.map_one.symm)))
  have hw2 : e w ^ 2 = 1 := by
    rw [← map_pow]
    have he : w ^ 2 = 1 := Subtype.ext s.uz_sq
    rw [he, map_one]
  have htable : ∀ w : QuaternionGroup 2, w ≠ 1 → w ^ 2 = 1 →
      ∀ x : QuaternionGroup 2, x = 1 ∨ x = w ∨ x ^ 2 = w := by decide
  intro x hx
  let y : (m.P ⊓ m.L : Subgroup G) := ⟨x, hx⟩
  rcases htable (e w) hw hw2 (e y) with he | he | he
  · have hxy : x = 1 := congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
    exact hxy ▸ (coreInG b).one_mem
  · have hxy : x = b := congrArg Subtype.val (e.injective he)
    exact hxy ▸ hb.involution_mem_coreInG
  · apply hsq
    exact congrArg Subtype.val (e.injective ((map_pow e y 2).trans he))

/-- Conditional assembly with the original marked r and the intrinsic core.
The orbit input is owned by qt-i46-census-orbit-profile. The square-root and
marked-action producers discharge the other two explicit premises. -/
theorem nonempty_coreData_of_local_calculations (s : SymmetricSixData h a)
    (m : M10NormalizerGeometry s) (o : Census.OrbitData z a.u)
    (hsq : SquareRootClosed z)
    (hmoved : ∃ x ∈ m.P ⊓ m.L, ⁅m.r, x⁆ ∉ zpowers (s.u * z)) :
    Nonempty (CoreData s m) := by
  have hf := b_fused_of_orbits s o
  obtain ⟨g, hg⟩ := isConj_iff.mp hf
  let e : G ≃* G := MulAut.conj g
  have he : e z = s.u * z := hg
  let hb : Hypotheses (s.u * z) := he ▸ transport h e
  have hsqb : SquareRootClosed (s.u * z) := he ▸ squareRootClosed_transport hsq e
  have hRQ := quaternion_le_core_of_squareRootClosed s m hb hsqb
  exact ⟨⟨hf, hb, rz_mem_core m hb (z_not_core m hb hRQ)
    (r_not_core m hb hRQ hmoved)⟩⟩

/-- The source Q_b calculation for the original marked r: b is conjugate to z,
the original hypotheses transport to its intrinsic centralizer core, and
rz belongs to that core. All three local calculation premises are discharged. -/
theorem nonempty_coreData (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (a : SourceGeometry h) (s : SymmetricSixData h a)
    (n : SymmetricNormalizerData s) (m : M10NormalizerGeometry s) :
    Nonempty (CoreData s m) := by
  exact nonempty_coreData_of_local_calculations s m
    (Census.orbitData_of_quaternion_normal h hn d (selected a))
    (squareRootClosed_of_sourceGeometry h hn a)
    (exists_noncentral_commutator s n m)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore

end
