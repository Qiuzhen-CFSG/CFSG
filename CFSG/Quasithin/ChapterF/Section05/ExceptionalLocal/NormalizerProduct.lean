module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PlaneStabilizer
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupAction.SixteenOddComplements.Recognition
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PCoreProduct
/-!
# The original plane normalizer is S₄ × S₄

The source two-core A₂ is elementary of order16 and self-centralizing.
The proved quotient is S₃×S₃, and the original endpoint transvection has
eight fixed elements on A₂. The normal-nine splitting and two invariant
plane argument therefore identify the actual H=N_G(A₂) with S₄×S₄.

The core calculation retains A₂ as a subgroup of H and maps it onto the
product of the literal Klein-four cores. No choice of vertex-intersection
coordinates or extension of an endpoint automorphism is assumed.

Source: Aschbacher--Smith F.5.4(4) and F.5.7, printed pp.301–303.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

private theorem source_plane_normalizer_transvection_fixed :
    let A' := (A c i true).subgroupOf (H c i)
    letI : A'.Normal := normal_subgroupOf_of_le_normalizer (show H c i ≤ normalizer (A c i true : Set G) from le_rfl)
    ∃ g : H c i, Nat.card (MulAut.conjNormal (H:=A') g).fixedSubgroup=8 := by
  let A' := (A c i true).subgroupOf (H c i)
  have hAN : A c i true ≤ H c i := le_normalizer
  let : A'.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨g,hgN,hg⟩ := source_normalizer_transvection c i z h true
  let gN : H c i := ⟨g,hgN⟩
  let eA : A' ≃* A c i true := subgroupOfEquivOfLe hAN
  let F := (centralizer ({g} : Set G)).subgroupOf (A c i true)
  have hF : Nat.card F=8 := by
    have hh := F.card_mul_index
    rw [hg,source_A_card c i h.embedding_injective true] at hh
    omega
  let eF : (MulAut.conjNormal (H:=A') gN).fixedSubgroup ≃* F :=
    { toFun := fun x => ⟨eA x,by
        have hh := (MulAut.mem_fixedSubgroup _ _).mp x.property
        have hv := congrArg (fun y:A' => ((y:H c i):G)) hh
        change g*(eA x:G)*g⁻¹=(eA x:G) at hv
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv).symm⟩
      invFun := fun x => ⟨eA.symm x,by
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        apply Subtype.ext
        apply Subtype.ext
        have hh := mem_centralizer_singleton_iff.mp x.property
        change g*(x.val:G)*g⁻¹=(x.val:G)
        exact mul_inv_eq_iff_eq_mul.mpr hh.symm⟩
      left_inv := fun x => Subtype.ext (eA.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (eA.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (eA.map_mul x y) }
  exact ⟨gN,(Nat.card_congr eF.toEquiv).trans hF⟩

/-- The actual plane normalizer is the symmetric-four product. All quotient,
faithfulness and transvection inputs come from the original source hypotheses. -/
theorem source_H_iso : Nonempty (H c i ≃* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) := by
  let A' := (A c i true).subgroupOf (H c i)
  have hAN : A c i true ≤ H c i := le_normalizer
  let : A'.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 (A c i true) := source_A_elementary c i h.embedding_injective true
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAN
  have hA : Nat.card A' = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans
      (source_A_card c i h.embedding_injective true)
  have hC : centralizer (A' : Set (H c i)) ≤ A' := by
    intro x hx
    apply (source_A_self_centralizer c i z h true).le
    intro a ha
    exact congrArg Subtype.val (hx ⟨a,hAN ha⟩ ha)
  obtain ⟨e⟩ := source_normalizer_plane_quotient c i z h
  change (H c i ⧸ A') ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) at e
  obtain ⟨g,hg⟩ := source_plane_normalizer_transvection_fixed c i z h
  exact SixteenOddComplements.symmetric_four_product_of_symmetric_three_pair_quotient A' hA hC e g hg

/-- Chosen coordinates on the literal source normalizer. -/
noncomputable def sourceHEquiv : H c i ≃* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) :=
  Classical.choice (source_H_iso c i z h)

theorem source_H_card : Nat.card (H c i)=576 := by
  rw [Nat.card_congr (sourceHEquiv c i z h).toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
  decide

/-- A₂ is exactly the two-core of the full local group. -/
theorem source_H_twoCore : pCore 2 (H c i) = (A c i true).subgroupOf (H c i) := by
  let A' := (A c i true).subgroupOf (H c i)
  have hAN : A c i true ≤ H c i := le_normalizer
  let : A'.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 (A c i true) := source_A_elementary c i h.embedding_injective true
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAN
  obtain ⟨e⟩ := source_normalizer_plane_quotient c i z h
  change (H c i ⧸ A') ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) at e
  have hcore : pCore 2 (H c i ⧸ A')=⊥ := by
    apply map_injective (f:=e.toMonoidHom) e.injective
    rw [Subgroup.map_bot,pCore_map_iso 2 e]
    exact SymmetricThreeProduct.twoCore_eq_bot
  have hh := (QuotientGroup.mk' A').comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective A') (show IsPGroup 2 (QuotientGroup.mk' A').ker by
      rw [QuotientGroup.ker_mk']; exact IsElementaryAbelian.isPGroup 2 A')
  rw [hcore] at hh
  change (QuotientGroup.mk' A').ker = pCore 2 (H c i) at hh
  rw [QuotientGroup.ker_mk'] at hh
  exact hh.symm

/-- Every local comparison retains A₂ as the two literal Klein-four factors. -/
theorem source_H_core_map (e : H c i ≃* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :
    ((A c i true).subgroupOf (H c i)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core.prod
        Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
  rw [←source_H_twoCore c i z h,pCore_map_iso,pCore_prod,
    ←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

