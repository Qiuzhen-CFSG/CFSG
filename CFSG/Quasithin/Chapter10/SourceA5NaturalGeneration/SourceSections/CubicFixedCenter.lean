module
public import Theory.Representation.BinaryConjugationSection.CubicActor
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedCoordinates
public import CFSG.Quasithin.Chapter10.SourceA5ActionKernel
/-!
# Original natural cubic fixed centers

Every cubic element in the original orbit acts nontrivially on its module:
the actual action kernel is a two-group. The paired natural coordinates then
force one cubic coordinate, giving the same omega-center fixed subgroup as
the whole orbit. Comparing this with the H-star cubic fixed subgroup removes
both fixed centers by original maximal-overgroup uniqueness.

Source: Aschbacher–Smith, 10.2.3(4), p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))

include e hn in
theorem source_original_cubic_not_centralizes_local_module
    (b : localOrbit T L) (hb : orderOf b=3) :
    (b:G) ∉ centralizer (D.moduleSubgroup : Set G) := by
  intro hc
  let X := localJoin T L
  let U := D.moduleSubgroup.subgroupOf X
  let C := centralizer (U : Set X)
  let bx : X := inclusion (show localOrbit T L ≤ X from le_sup_left) b
  have hbc : bx ∈ C := by
    intro a ha
    apply Subtype.ext
    exact hc a ha
  let bc : C := ⟨bx,hbc⟩
  have ho : orderOf bc=3 := by
    rw [show orderOf bc = orderOf bx from Subgroup.orderOf_mk _ _]
    exact (orderOf_injective (inclusion (show localOrbit T L ≤ X from le_sup_left))
      (inclusion_injective _) b).trans hb
  have hne : bc≠1 := by
    intro he
    simp [he] at ho
  have hd := (source_a5_local_module_kernel_isTwoGroup D e hn).dvd_orderOf hne
  rw [ho] at hd
  norm_num at hd

variable {F : Type*} [Field F] [CharP F 2]
local instance originalCubicFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4)
    (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

include D e hn hH hZH hF f n
theorem source_original_cubic_fixed_of_hstar_natural_four
    (b : localOrbit T L) (hb : orderOf b=3) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
  obtain ⟨K,q₁,q₂,c,hfix⟩ :=
    source_original_paired_cubic_fixed_of_hstar_natural_four D e hn hH hZH hF f n
  let := D.module_elementary
  exact hfix b (c.paired_cubic_image_of_noncentral q₁ q₂ inf_le_right b hb
    (source_original_cubic_not_centralizes_local_module D e hn b hb))

theorem source_hstar_natural_four_fixed_centers_eq_bot_of_cubic
    (b : localOrbit T L) (hb : orderOf b=3)
    (hHZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ :=
  source_hstar_fixed_centers_eq_bot_of_eq D hH (hHZ.trans
    (source_original_cubic_fixed_of_hstar_natural_four D e hn hH hZH hF f n b hb))
end CFSG.Quasithin.Chapter10
