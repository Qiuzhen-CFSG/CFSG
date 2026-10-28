module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.OddActor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.FixedLayer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Source

/-!
# The whole rank-one fixed layer in odd field degree

The odd-degree normalizer theorem fixes the original moved kernel under
T₁ = N_T(L). Since T₁ is normal in T, the same literal subgroup fixes
its conjugate kernel under the specified exchanger. Crossed centralization
identifies the entire L₀-fixed layer with the join of these two kernels.
Thus T₁ fixes that whole layer, with no assumption that the kernels vanish
or that the moved factors have trivial intersection.

Source: Aschbacher--Smith, 10.1.1(1) and the rank-one branch of10.2.9,
printed pp.741 and750. This proves the odd-degree branch of the additional
fixed-layer interface used by the point-Sylow consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance oddFixedBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance oddFixedMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- An odd-degree natural field makes the half-Sylow fix both moved kernels. -/
theorem half_sylow_centralizes_moved_kernels_of_odd_degree
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (Representation.SL2.BinarySmall.natural.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      centralizer (↑(sourceMovedFixed D ⊔
        (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hSK : S ≤ centralizer (sourceMovedFixed D : Set G) :=
    two_subgroup_centralizes_kernel_of_odd_degree D e c hn hcard S
      (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
    (fun h => htn (h ht))
  have hnorm : ((normalizer (L : Set G)).subgroupOf (T : Subgroup G)).Normal :=
    normal_of_index_eq_two hi
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hs hx.1)
        ((T : Subgroup G).inv_mem hs),
        hnorm.conj_mem (⟨x,hx.1⟩ : T) hx.2 (⟨s,hs⟩ : T)⟩
    · intro hx
      have hxT : x ∈ (T : Subgroup G) := by
        have hh := (T : Subgroup G).mul_mem
          ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hs) hx.1) hs
        simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
      have hh := hnorm.conj_mem (⟨s*x*s⁻¹,hx.1⟩ : T) hx.2 (⟨s,hs⟩ : T)⁻¹
      refine ⟨hxT,?_⟩
      change x ∈ normalizer (L : Set G)
      simpa only [Subgroup.mem_subgroupOf,Subgroup.coe_mul,Subgroup.coe_inv,
        inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  have hSK' := map_mono (f := (MulAut.conj t).toMonoidHom) hSK
  have hmap : S.map (MulAut.conj t).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  rw [hmap,Theory.GroupTheory.map_centralizer_equiv] at hSK'
  apply le_centralizer_iff.mp
  exact sup_le (le_centralizer_iff.mpr hSK) (le_centralizer_iff.mpr hSK')

/-- The literal fixed-layer obligation holds over every odd-degree natural field. -/
theorem fixed_layer_centralizes_half_sylow_of_odd_degree
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (Representation.SL2.BinarySmall.natural.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  rw [BinaryThree.fixed_layer_eq_moved_kernels D ht htn hcross]
  exact le_centralizer_iff.mpr
    (half_sylow_centralizes_moved_kernels_of_odd_degree D e c hn hcard ht htn)

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
