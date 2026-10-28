module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SpecificGroups.KleinFourPointStabilizer
public import Theory.ElementaryAbelian.Basic

/-!
# Relative normality in the faithful central-quotient action

The point-plane stabilizer is C_G(V₂)U: this follows from [U,V₂]=V₁
and the two-element automorphism stabilizer of a point in a four-group.
The plane centralizer normalizes W^g and Z(U)^g, and U acts trivially on
U/Z(U). Consequently the literal images of both actors are normal in
the image of H∩G₂. The relative two-core calculation places X in the
fixed ambient Sylow T and proves normality in its actual quotient image.

The action is parameterized by its full evaluation equation on U/Z(U),
the interface supplied by the earlier §12.8 action construction. As a
homomorphism to automorphisms it uses left conjugation; the subgroup
notation `conjugate` retains the source right-conjugation convention.
No normality conclusion or kernel inclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.12(2), printed p.855 / PDF p.872. Earlier §12.8 clauses
remain explicit for discharge by the section assembly.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem plane_centralizer_le_H (F : InvariantFlag T V n) :
    centralizer (F.Vi 2 : Set G) ≤ F.H :=
  (centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans (centralizer_le_normalizer _)

private theorem normalizes_conjugate_of_invariant
    (A C : Subgroup G) (g : G) (hC : g ∈ normalizer (C : Set G))
    (h : C ≤ normalizer (A : Set G)) : C ≤ normalizer (conjugate A g : Set G) := by
  have hc : C.map (MulAut.conj g⁻¹).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (C : Set G)).inv_mem hC)
  rw [conjugate, ← map_equiv_normalizer_eq A (MulAut.conj g⁻¹), ← hc]
  exact map_mono h

/-- The centralizer of the marked plane preserves both actors before taking
the faithful action quotient. -/
theorem plane_centralizer_normalizes_actors (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.Gi 2) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (F.X g : Set G) ∧
      centralizer (F.Vi 2 : Set G) ≤ normalizer (conjugate F.ZU g : Set G) := by
  let C := centralizer (F.Vi 2 : Set G)
  have hC : g ∈ normalizer (C : Set G) := normalizer_le_normalizer_centralizer _ hg
  have hU : C ≤ normalizer (F.U : Set G) :=
    F.plane_centralizer_le_H.trans (le_normalizer_conjugateSpanBy V F.H)
  constructor
  · apply normalizes_conjugate_of_invariant F.W C g hC
    exact (le_inf hU C.le_normalizer).trans inf_normalizer_le_normalizer_inf
  · apply normalizes_conjugate_of_invariant F.ZU C g hC
    exact hU.trans (normalizer_le_normalizer_characteristic_image F.U (center F.U))

/-- The conjugate central actor lies in the conjugate plane centralizer. -/
theorem conjugate_ZU_le_X (F : InvariantFlag T V n) (g : G) :
    conjugate F.ZU g ≤ F.X g := by
  apply map_mono
  apply le_inf (map_subtype_le _)
  rintro z ⟨z, hz, rfl⟩ v hv
  exact congrArg Subtype.val (mem_center_iff.mp hz
    ⟨v, (F.le_seed 2).trans (le_conjugateSpanBy V F.H) hv⟩)

/-- Both actors lie in the actual plane centralizer and hence in H. -/
theorem X_le_plane_centralizer (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ F.Gi 2) : F.X g ≤ centralizer (F.Vi 2 : Set G) := by
  have hC : g⁻¹ ∈ normalizer (centralizer (F.Vi 2 : Set G) : Set G) :=
    (normalizer _).inv_mem (normalizer_le_normalizer_centralizer _ hg)
  have heq := mem_normalizer_iff_map_conj_eq.mp hC
  change F.W.map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [← heq]
  exact map_mono inf_le_right

/-- The point-plane stabilizer factorization used in 12.8.12(2), derived
from the earlier equation [U,V₂]=V₁ and the actual four-group action. -/
theorem H2_eq_plane_centralizer_sup_U (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 (F.Vi 2)] (hn : 2 ≤ n)
    (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hcomm : ⁅F.U, F.Vi 2⁆ = F.Vi 1) :
    F.H ⊓ F.Gi 2 = centralizer (F.Vi 2 : Set G) ⊔ F.U := by
  have hcard : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 hn
  let : Nontrivial (F.Vi 2) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (F.Vi 2) := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hU2 : F.U ≤ F.Gi 2 := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [hcomm]
    exact F.monotone (by omega)
  have hmove : ¬ F.U ≤ centralizer (F.Vi 2 : Set G) := by
    intro hc
    have he := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hcomm, hz] at he
    have hzb := he ▸ mem_zpowers z
    exact hne (mem_bot.mp hzb)
  have hz2 : z ∈ F.Vi 2 := F.monotone (by omega : 1 ≤ 2) (hz ▸ mem_zpowers z)
  have hUc : F.U ≤ centralizer ({z} : Set G) := by
    rw [← F.H_eq_centralizer (by omega) z hz]
    exact F.U_le_H
  have he := kleinFour_point_stabilizer_eq_centralizer_sup (F.Vi 2) F.U
    ⟨z, hz2⟩ (fun he => hne (congrArg Subtype.val he)) hU2 hUc hmove
  rw [F.H_eq_centralizer (by omega) z hz, inf_comm]
  exact he

/-- The actor lies in the specified ambient Sylow subgroup by 12.8.9(1–2).
Normality is relative to G₂, so no ambient normality is imposed. -/
theorem X_le_T_of_parabolic_core (F : InvariantFlag T V n) (L : Subgroup G)
    (g : G) (hI : F.I₂ L ≤ F.Gi 2)
    (hN : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (hcore : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g) : F.X g ≤ (T : Subgroup G) := by
  let Q := (F.I₂ L).pCoreIn 2
  have hQ : Q ≤ F.Gi 2 := (pCoreIn_le 2 _).trans hI
  have hnorm : F.Gi 2 ≤ normalizer (Q : Set G) :=
    hN.trans (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  let : (Q.subgroupOf (F.Gi 2)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ).mpr hnorm
  have hp : IsPGroup 2 (Q.subgroupOf (F.Gi 2)) :=
    (isPGroup_pCoreIn 2 (F.I₂ L)).comap_subtype
  have hQT := hp.le_sylow_of_normal (T.subtype (F.invariant 2))
  intro x hx
  have hxQ : x ∈ Q := by
    change x ∈ (F.I₂ L).pCoreIn 2
    rw [hcore]
    exact (le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx
  exact hQT (show (⟨x, hQ hxQ⟩ : F.Gi 2) ∈ Q.subgroupOf (F.Gi 2) from hxQ)

namespace Symplectic

/-- The faithful quotient for a specified action on the literal central quotient. -/
abbrev Hdot (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat) := F.H ⧸ ρ.ker

/-- The induced faithful action on the original central quotient. -/
def faithfulAction (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat) :
    Hdot F ρ →* MulAut F.Uhat := QuotientGroup.lift ρ.ker ρ le_rfl

@[simp] theorem faithfulAction_mk (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (h : F.H) :
    faithfulAction F ρ (QuotientGroup.mk' ρ.ker h) = ρ h := rfl

theorem faithfulAction_injective (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) : Function.Injective (faithfulAction F ρ) :=
  (QuotientGroup.injective_lift_iff ρ.ker ρ le_rfl).mpr rfl

/-- The actual quotient image of an ambient subgroup. -/
def dotImage (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A : Subgroup G) : Subgroup (Hdot F ρ) :=
  (A.subgroupOf F.H).map (QuotientGroup.mk' ρ.ker)

/-- Taking an actor's image in the faithful quotient preserves its exact
image on the original central quotient. -/
theorem faithfulAction_dotImage (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (A : Subgroup G) :
    (dotImage F ρ A).map (faithfulAction F ρ) = (A.subgroupOf F.H).map ρ := by
  unfold dotImage faithfulAction
  rw [map_map, QuotientGroup.lift_comp_mk']

/-- Inner conjugation disappears on U/Z(U). This follows from the action
equation and commutativity of the central quotient. -/
theorem U_le_action_kernel (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsMulCommutative F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    F.U.subgroupOf F.H ≤ ρ.ker := by
  intro h hh
  apply MulEquiv.ext
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) q
  rw [hρ]
  let v : F.U := ⟨h, hh⟩
  have heq : F.U.normalizerMonoidHom
      ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u = v * u * v⁻¹ := rfl
  rw [heq, map_mul, map_mul, map_inv]
  simp [mul_comm]

private theorem dotImage_normalizer (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) {A C : Subgroup G}
    (hA : A ≤ F.H) (h : C ≤ normalizer (A : Set G)) :
    dotImage F ρ C ≤ normalizer (dotImage F ρ A : Set (Hdot F ρ)) := by
  apply (map_mono (f := QuotientGroup.mk' ρ.ker) ?_).trans (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq hA]
  exact comap_mono h

/-- The relative normality calculation of 12.8.12(2), once the point-plane
stabilizer factorization is supplied. The quotient maps and action equation
are literal; the kernel inclusion for U is proved, not assumed. -/
theorem actors_normal_in_dot_H2_of_factorization
    (F : InvariantFlag T V n) [IsMulCommutative V] [IsMulCommutative F.Uhat]
    (g : G) (hg : g ∈ F.Gi 2) (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (hfactor : F.H ⊓ F.Gi 2 = centralizer (F.Vi 2 : Set G) ⊔ F.U) :
    ((dotImage F ρ (F.X g)).subgroupOf (dotImage F ρ (F.H ⊓ F.Gi 2))).Normal ∧
      ((dotImage F ρ (conjugate F.ZU g)).subgroupOf
        (dotImage F ρ (F.H ⊓ F.Gi 2))).Normal := by
  have hC := F.plane_centralizer_le_H
  have hX := F.X_le_plane_centralizer g hg
  have hZ := F.conjugate_ZU_le_X g
  have hCX := (F.plane_centralizer_normalizes_actors g hg).1
  have hCZ := (F.plane_centralizer_normalizes_actors g hg).2
  have hdot : dotImage F ρ (F.H ⊓ F.Gi 2) =
      dotImage F ρ (centralizer (F.Vi 2 : Set G)) := by
    unfold dotImage
    rw [hfactor, subgroupOf_sup hC F.U_le_H, Subgroup.map_sup]
    have hker : (F.U.subgroupOf F.H).map (QuotientGroup.mk' ρ.ker) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [QuotientGroup.ker_mk'] using U_le_action_kernel F ρ hρ
    rw [hker, sup_bot_eq]
  rw [hdot]
  constructor
  · apply (normal_subgroupOf_iff_le_normalizer (map_mono (comap_mono hX))).mpr
    exact dotImage_normalizer F ρ (hX.trans hC) hCX
  · apply (normal_subgroupOf_iff_le_normalizer (map_mono (comap_mono (hZ.trans hX)))).mpr
    exact dotImage_normalizer F ρ (hZ.trans (hX.trans hC)) hCZ

/-- Source 12.8.12(2): both specified actor images are normal in the image
of H∩G₂. The extra factorization premise of the intermediate theorem is
now discharged by the four-group calculation. -/
theorem actors_normal_in_dot_H2
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    [IsElementaryAbelian 2 (F.Vi 2)] [IsMulCommutative F.Uhat]
    (hn : 2 ≤ n) (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hcomm : ⁅F.U, F.Vi 2⁆ = F.Vi 1)
    (g : G) (hg : g ∈ F.Gi 2) (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    dotImage F ρ (F.X g) ≤ dotImage F ρ (F.H ⊓ F.Gi 2) ∧
      ((dotImage F ρ (F.X g)).subgroupOf (dotImage F ρ (F.H ⊓ F.Gi 2))).Normal ∧
      dotImage F ρ (conjugate F.ZU g) ≤ dotImage F ρ (F.H ⊓ F.Gi 2) ∧
      ((dotImage F ρ (conjugate F.ZU g)).subgroupOf
        (dotImage F ρ (F.H ⊓ F.Gi 2))).Normal := by
  have hnormal := actors_normal_in_dot_H2_of_factorization F g hg ρ hρ
    (F.H2_eq_plane_centralizer_sup_U hn z hz hne hcomm)
  have hC : centralizer (F.Vi 2 : Set G) ≤ F.H ⊓ F.Gi 2 :=
    le_inf F.plane_centralizer_le_H (centralizer_le_normalizer _)
  have hX := (F.X_le_plane_centralizer g hg).trans hC
  exact ⟨map_mono (comap_mono hX), hnormal.1,
    map_mono (comap_mono ((F.conjugate_ZU_le_X g).trans hX)), hnormal.2⟩

/-- In particular the actual image of X is normal in the actual image of T.
The containment X≤T is the two-core containment from 12.8.9(2). -/
theorem Xdot_normal_in_Tdot_of_le
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    [IsElementaryAbelian 2 (F.Vi 2)] [IsMulCommutative F.Uhat]
    (hn : 2 ≤ n) (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hcomm : ⁅F.U, F.Vi 2⁆ = F.Vi 1)
    (g : G) (hg : g ∈ F.Gi 2) (hXT : F.X g ≤ (T : Subgroup G))
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    dotImage F ρ (F.X g) ≤ dotImage F ρ (T : Subgroup G) ∧
      ((dotImage F ρ (F.X g)).subgroupOf (dotImage F ρ (T : Subgroup G))).Normal := by
  have h := actors_normal_in_dot_H2 F hn z hz hne hcomm g hg ρ hρ
  have hle : dotImage F ρ (F.X g) ≤ dotImage F ρ (T : Subgroup G) :=
    map_mono (comap_mono hXT)
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  have hT : (T : Subgroup G) ≤ F.H ⊓ F.Gi 2 := le_inf (F.invariant 1) (F.invariant 2)
  exact (map_mono (comap_mono hT)).trans
    ((normal_subgroupOf_iff_le_normalizer h.1).mp h.2.1)

/-- The final Sylow-image clause of 12.8.12(2), using only the actual
normality and two-core equations of 12.8.9 for the Sylow containment. -/
theorem Xdot_normal_in_Tdot
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    [IsElementaryAbelian 2 (F.Vi 2)] [IsMulCommutative F.Uhat]
    (hn : 2 ≤ n) (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (hcomm : ⁅F.U, F.Vi 2⁆ = F.Vi 1)
    (L : Subgroup G) (g : G) (hg : g ∈ F.Gi 2)
    (hI : F.I₂ L ≤ F.Gi 2) (hN : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (hcore : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    dotImage F ρ (F.X g) ≤ dotImage F ρ (T : Subgroup G) ∧
      ((dotImage F ρ (F.X g)).subgroupOf (dotImage F ρ (T : Subgroup G))).Normal :=
  Xdot_normal_in_Tdot_of_le F hn z hz hne hcomm g hg
    (F.X_le_T_of_parabolic_core L g hI hN hcore) ρ hρ

end Symplectic
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
