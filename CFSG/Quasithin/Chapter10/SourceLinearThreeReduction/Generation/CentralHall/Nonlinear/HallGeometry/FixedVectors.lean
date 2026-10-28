module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Basic
public import Theory.Representation.BinaryConjugationSection.DiagonalFixed
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.Representation.BinaryConjugationSection.FixedKernel
public import Theory.Representation.SL2.BinarySmallFixed
public import Theory.Representation.Suzuki.FixedVectors
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl

/-!
# The central Hall actor on stabilizer-fixed moved vectors

Write W=[V,L] and S=N_T(L). The nonnormal component pair gives [T:S]=2.
Its crossed-centralization geometry makes W and its exchanged factor commute.
For w in W centralizing S, the diagonal w w^t lies in Omega-one of Z(T).
The literal Hall subgroup preserves both factors and centralizes this diagonal,
so it fixes the coordinates of w modulo their common central kernel.

For the Hermitian and Suzuki rows, their global fixed spaces vanish and their
whole-module coordinates have trivial kernel. Thus the Hall subgroup fixes the
original stabilizer-fixed vectors, with the prescribed quotient actions.
These are inputs to the remaining semilinear Hall calculation; they do not
assert triviality of the entire Hall action or eliminate its field factor.

Source: Aschbacher--Smith, 10.1.1--2 and 10.2.3, printed pp.741--742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
include D c

omit D c [Finite G] in
private theorem normalizes_second_of_pair (M U : Subgroup G) (t : G)
    (ht : t ∈ M)
    (hpair : ∀ m ∈ M, U.conjBy m = U ∨ U.conjBy m = U.conjBy t)
    {b : G} (hb : b ∈ M) (hbU : b ∈ normalizer (U : Set G)) :
    b ∈ normalizer (U.conjBy t : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (U.conjBy t).conjBy b = U.conjBy t
  have he := hpair (b*t) (M.mul_mem hb ht)
  rw [conjBy_mul] at he
  rcases he with he | he
  · have hfix : U.conjBy b = U := mem_normalizer_iff_map_conj_eq.mp hbU
    have heq : U.conjBy t = U := map_injective (MulAut.conj b).injective
      (he.trans hfix.symm)
    exact he.trans heq.symm
  · exact he

theorem hall_normalizes_partner {t : G} (ht : t ∈ (T : Subgroup G))
    (htn : t ∉ normalizer (L : Set G)) :
    B.map H.subtype ≤ normalizer
      ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Set G) := by
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hmaps (s : G) (hs : s ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj s).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hs)
  have hpair : ∀ s ∈ D.maximalLocal,
      (⁅D.fullModule,L⁆).conjBy s = ⁅D.fullModule,L⁆ ∨
        (⁅D.fullModule,L⁆).conjBy s = (⁅D.fullModule,L⁆).conjBy t := by
    intro s hs
    change (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom = _ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom = _
    rw [map_commutator,hmaps s hs]
    rcases source_nonnormal_maximal_pair D c.nonnormal ht htn s hs with he | he
    · exact Or.inl (by rw [he])
    · right
      change _ = (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
      rw [map_commutator,hmaps t (hTM ht),he]
  intro b hb
  exact normalizes_second_of_pair D.maximalLocal ⁅D.fullModule,L⁆ t (hTM ht)
    hpair (map_le_iff_le_comap.mpr c.hall_le hb) (hall_normalizes_moved D c hb)

theorem moved_le_stabilizer (geometry : ModuleGeometry D) :
    ⁅D.fullModule,L⁆ ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
  replace hWV := hWV.trans (le_of_eq geometry.full_eq_local)
  exact le_inf (hWV.trans D.module_le_sylow)
    (hWV.trans (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D c.nonnormal)))

theorem moved_fixed_mem_omegaCenter (geometry : ModuleGeometry D)
    {w : G} (hw : w ∈ ⁅D.fullModule,L⁆)
    (hfixed : w ∈ centralizer
      ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) :
    w ∈ omegaOneCenterAmbient ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  have hwV : w ∈ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule) hw
    rwa [geometry.full_eq_local] at hh
  let := D.module_elementary
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨moved_le_stabilizer D c geometry hw,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) w hwV,hfixed⟩

/-- On the actual moved module, the Hall group fixes the coordinates of the
vectors fixed by the Sylow stabilizer of the component. The retained kernel
need only contain the common fixed subgroup of the component. -/
theorem hall_fixed_coordinates
    (geometry : ModuleGeometry D)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Z : Subgroup G} {ρ : Representation (ZMod 2) L V}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ Z ρ)
    (hkernel : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≤ Z)
    (w : (⁅D.fullModule,L⁆ : Subgroup G))
    (hw : (w : G) ∈ centralizer
      ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G))
    (b : B) :
    d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
      (mem_normalizer_iff.mp (hall_normalizes_moved D c
        (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩ = d.coordinates w := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : S.relIndex (T : Subgroup G) = 2 := by
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal
  have htS : t ∉ S := fun h => htn h.2
  have hWV : ⁅D.fullModule,L⁆ ≤ D.moduleSubgroup := by
    have hh := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact hh.trans (le_of_eq geometry.full_eq_local)
  have hwV := hWV w.property
  have htwV : t*(w : G)*t⁻¹ ∈ D.moduleSubgroup :=
    (mem_normalizer_iff.mp (D.sylow_normalizes_module ht) w).mp hwV
  let := D.module_elementary
  have hc : Commute (w : G) (t*(w : G)*t⁻¹) :=
    congrArg Subtype.val (mul_comm (⟨w,hwV⟩ : D.moduleSubgroup) ⟨_,htwV⟩)
  have hHZ : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact c.central)
  exact d.coordinates_conj_eq_of_centralizes_diagonal inf_le_left hi t ht htS
    (le_inf inf_le_left (inf_le_right.trans (geometry.crossed t ht htn)) |>.trans hkernel)
    w (moved_fixed_mem_omegaCenter D c geometry w.property hw) hc b
    (hall_normalizes_moved D c (mem_map_of_mem H.subtype b.property))
    (hall_normalizes_partner D c ht htn (mem_map_of_mem H.subtype b.property))
    (hHZ b.val.property)

section Natural
local instance naturalFixedBinaryAlgebra (r : ℕ) : Algebra (ZMod 2) (GaloisField 2 r) :=
  ZMod.algebra _ 2

/-- Application to the literal natural section of 10.1.1(1), including its
possibly nontrivial central kernel. -/
theorem natural_hall_fixed_coordinates
    (geometry : ModuleGeometry D) (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
    (d : NaturalSection D r e)
    (w : (⁅D.fullModule,L⁆ : Subgroup G))
    (hw : (w : G) ∈ centralizer
      ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) (b : B) :
    d.coordinates ⟨(b : G)*w*(b : G)⁻¹,
      (mem_normalizer_iff.mp (hall_normalizes_moved D c
        (mem_map_of_mem H.subtype b.property)) w).mp w.property⟩ = d.coordinates w :=
  hall_fixed_coordinates D c geometry d le_rfl w hw b
end Natural

/-- If the model has no global fixed vectors and the coordinates have trivial
kernel, the diagonal argument fixes the actual moved vectors pointwise. -/
theorem hall_centralizes_moved_fixed_of_no_fixed
    (geometry : ModuleGeometry D)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) L V}
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥ ρ)
    (hzero : ∀ v, (∀ l, ρ l v = v) → v = 0) :
    B.map H.subtype ≤ centralizer
      ((⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) : Subgroup G) : Set G) := by
  have hkernel := d.centralizer_le_kernel_of_fixed_eq_zero hzero
  have hi : Function.Injective d.coordinates :=
    (MonoidHom.ker_eq_bot_iff d.coordinates).mp (by
      rw [d.kernel_eq,bot_subgroupOf])
  rintro b ⟨b,hb,rfl⟩ w hw
  let w' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨w,hw.1⟩
  have he := hall_fixed_coordinates D c geometry d hkernel w' hw.2 (⟨b,hb⟩ : B)
  have hc : (b : G)*w*(b : G)⁻¹ = w := congrArg Subtype.val (hi he)
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

local instance movedFixedBinaryAlgebra (n : ℕ) : Algebra (ZMod 2)
    (Representation.OrthogonalFourMinus.FiniteModel.fixedField n) := ZMod.algebra _ 2
local instance movedFixedHermitianBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2)
    (Representation.OrthogonalFourMinus.FiniteModel.Space n) :=
  Module.compHom _ (algebraMap (ZMod 2)
    (Representation.OrthogonalFourMinus.FiniteModel.fixedField n))

/-- The orthogonal row fixes the actual Sylow-stabilizer-fixed moved vectors;
there is no additional action, quotient or kernel hypothesis. -/
theorem orthogonal_hall_centralizes_moved_fixed
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    B.map H.subtype ≤ centralizer
      ((⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) : Subgroup G) : Set G) := by
  apply hall_centralizes_moved_fixed_of_no_fixed D c geometry d
  intro v hv
  apply SL2.BinarySmall.hermitian_fixed_eq_zero n v
  intro g
  obtain ⟨q,hq⟩ := e.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hh := hv l
  change (SL2.BinarySmall.hermitian n) (e (QuotientGroup.mk' (pCore 2 L) l)) v = v at hh
  rwa [hl,hq] at hh

/-- The Suzuki row fixes the actual Sylow-stabilizer-fixed moved vectors,
using the literal four-dimensional matrix model. -/
theorem suzuki_hall_centralizes_moved_fixed
    (geometry : ModuleGeometry D) (m : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SuzukiNatural.natural m).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    B.map H.subtype ≤ centralizer
      ((⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) : Subgroup G) : Set G) := by
  apply hall_centralizes_moved_fixed_of_no_fixed D c geometry d
  intro v hv
  apply SuzukiNatural.natural_fixed_eq_zero m v
  intro g
  obtain ⟨q,hq⟩ := e.surjective g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hh := hv l
  change (SuzukiNatural.natural m) (e (QuotientGroup.mk' (pCore 2 L) l)) v = v at hh
  rwa [hl,hq] at hh

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
