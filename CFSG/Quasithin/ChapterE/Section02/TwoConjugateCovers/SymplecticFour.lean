module
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate
public import Theory.GroupTheory.CentralExtensionGeneratedP
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.GroupTheory.CentralPChiefFactors
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual nonbinary symplectic core quotient in E.2.10(7)

The projection X/P → X/J has central kernel. For the specified Sp₄ model
over a characteristic-two field of size at least four, the derived cover
has trivial kernel by the actual multiplier theorem. The abelianization
is a two-group because the original two elementary subgroups generate X.
Thus J/P is a two-group and J=O₂(X). The final equivalence retains the
original X/J marking on the literal two-core quotient of X/Z.

Source: Aschbacher–Smith E.2.10(7), printed p.223.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem J_eq_twoCore_of_symplectic_four (h : Hypotheses T V M g)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Sp F) : J M = pCore 2 X := by
  let := h.core_geometry.1
  let := h.elementary
  let q := QuotientGroup.mk' (P V M g)
  let e := ξ
  have hPJ : P V M g ≤ J M := h.P_le_twoCore.trans h.twoCore_le_J
  let f : (X ⧸ P V M g) →* Sp F := QuotientGroup.lift (P V M g)
    (e.toMonoidHom.comp (QuotientGroup.mk' (J M))) (by
      intro x hx
      change e (QuotientGroup.mk' (J M) x) = 1
      exact e.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff x).mpr (hPJ hx)))
  have hfac (x : X) : f (q x) = e (QuotientGroup.mk' (J M) x) := rfl
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y,rfl⟩ := e.surjective z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (J M) y
    exact ⟨q x,rfl⟩
  have hk : f.ker = (J M).map q := by
    apply comap_injective (QuotientGroup.mk'_surjective (P V M g))
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hPJ]
    ext x
    change f (q x) = 1 ↔ x ∈ J M
    rw [hfac, e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hc : f.ker ≤ center (X ⧸ P V M g) := by
    rw [hk]
    exact (map_mk_le_center_iff _ _).mpr (by rw [commutator_comm]; exact h.commutator_J_le_P)
  have hfour : 4 ≤ Nat.card F := by
    rw [hcard]
    exact (show 2^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm)
  have hF : 3 < Nat.card F := by omega
  let : Group.IsPerfect (Sp F) := (CentralCovers.Even.isQuasisimple hF).toIsPerfect
  let c := CentralExtension.derivedCover f hf hc
  have hD : IsPGroup 2 c.toMonoidHom.ker := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr (CentralCovers.Even.cover_injective hF c)]
    exact IsPGroup.of_subsingleton 2 _
  let π := (QuotientGroup.mk' (commutator (X ⧸ P V M g))).comp q
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  let : IsMulCommutative ((X ⧸ P V M g) ⧸ commutator (X ⧸ P V M g)) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  have hAb := CentralExtension.abelian_image_isPGroup_of_sup V (W V g)
    (IsElementaryAbelian.isPGroup 2 V)
    ((IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g).toMonoidHom)
    h.generate π hπ
  have hK := CentralExtension.kernel_isPGroup_of_derived_kernel f hf hc hD hAb
  have hJtwo : IsPGroup 2 (J M) := by
    rw [hk] at hK
    have hp : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.to_le h.P_le_twoCore
    have hh := hK.comap_of_ker_isPGroup q hp
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hPJ] at hh
    exact hh
  exact le_antisymm (le_sSup ⟨inferInstance,hJtwo⟩) h.twoCore_le_J

@[expose] noncomputable def quotient_core_equiv_symplectic_four (h : Hypotheses T V M g)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Sp F) :
    letI := h.Z_normal
    ((X ⧸ Z V g) ⧸ pCore 2 (X ⧸ Z V g)) ≃* Sp F := by
  let := h.Z_normal
  let q := QuotientGroup.mk' (Z V g)
  have hp : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.to_le ((h.core_geometry.2.2.trans inf_le_left).trans h.P_le_twoCore)
  exact (q.pCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hp).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (h.J_eq_twoCore_of_symplectic_four m hm hcard ξ).symm).trans ξ)

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
