module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.Centralizers
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.CentralCovers
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The actual binary PSL₃ Sylow-overgroup bound in B.1.13

Unipotent overgroup placement puts each proper Sylow overgroup in an
actual point or line parabolic. Its root plane lies in the supplied Sylow
and is self-centralizing, so the overgroup has characteristic two. The
existing central-cover argument retains the original center and applies
the bound to the literal intersection L∩(K∨T) in B.1.13.

Source: Aschbacher–Smith B.1.13, printed p.74, used by C.1.27, p.133.
Neither solvability nor containment of the whole Borel is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
variable (F : Type*) [Field F] [Finite F]

private theorem standard_overgroup_core [CharP F 2]
    (X : Subgroup PSL(3,F)) (hU : unipotent F ≤ X) (hX : X ≠ ⊤) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  have hp : ∃ point : Bool, X ≤ parabolic F point := by
    rcases UnipotentOvergroups.overgroup_unipotent F X hU hX with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨point, hp⟩ := hp
  apply centralizer_pCore_le_of_normalized 2 (rootPlane F point) X
    (rootPlane_two F point)
  · exact (map_mono (f := projection F) (rootPlaneSL_le_unipotent F point)).trans hU
  · rwa [normalizer_rootPlane]
  · exact MainConverse.LinearThreeGeometry.centralizer_rootPlane_le F point

/-- Every proper overgroup of the supplied Sylow has characteristic two,
over every positive binary field, including F₂. -/
theorem linearThree_sylow_overgroup_core {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F)) (X : Subgroup PSL(3,F))
    (hSX : (S : Subgroup PSL(3,F)) ≤ X) (hX : X ≠ ⊤) :
    generalizedFitting X = pCore 2 X := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) S (unipotentSylow F hn hF)
  let e := MulAut.conj g
  have hS : (S : Subgroup PSL(3,F)).map e.toMonoidHom = unipotent F := by
    change ((g • S : Sylow 2 PSL(3,F)) : Subgroup PSL(3,F)) = _
    rw [hg]
    rfl
  have hUY : unipotent F ≤ X.map e.toMonoidHom := by
    rw [← hS]
    exact map_mono hSX
  have hY : X.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hX
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he, map_top_of_surjective _ e.surjective]
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap X)).mpr
    (standard_overgroup_core F _ hUY hY)

/-- The full B.1.13 model bound, with the center term available for lifting. -/
theorem linearThree_properSylowFittingBound {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) :
    ChapterB.ComponentRecognition.SylowOvergroups.ProperSylowFittingBound PSL(3,F) := by
  intro S X hSX hX
  rw [linearThree_sylow_overgroup_core F hn hF S X hSX hX]
  exact le_sup_left

/-- Literal B.1.13 consumer on a perfect central cover and the original
relative-subnormal subgroup K. No center is discarded. -/
theorem eq_component_of_linearThree_centralQuotient
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L) (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : L ⧸ center L ≃* PSL(3,F)) : K = L :=
  ChapterB.ComponentRecognition.SylowOvergroups.eq_component_of_centralQuotient_bound
    K L T hL hLK hkind hK hKL e (linearThree_properSylowFittingBound F hn hF)

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
