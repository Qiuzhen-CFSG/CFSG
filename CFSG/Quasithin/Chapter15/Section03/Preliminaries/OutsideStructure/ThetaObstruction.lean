module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Thompson escape from the theta normalizer

A normal subgroup J of I containing Y₊ cannot lie in M ∩ I: monotonicity
and idempotence of theta would identify theta(J) with Y₊, making Y₊ normal
in I. This contradicts N_I(Y₊)=M∩I and I ≰ M. Containment of the action
kernel in M∩I carries the obstruction to the actual quotient I/C_I(U_I).

For J=J(I), the commutator equality Y₊=[Y₊,J(S)] and Sylow conjugacy put
Y₊ in J(I). This proves the last assertion of (10ii) and all of (11) in
that branch. The commutator equality itself remains a separate obligation;
neither normality nor theta alone supplies it.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(10ii),(11), p.1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G]

/-- A normal subgroup containing Y₊ cannot lie in M∩I, since taking theta
would make Y₊ normal in I, contrary to its proper normalizer. -/
theorem normal_subgroup_outside_of_theta (Yplus M I J : Subgroup G)
    (hJnormal : I ≤ normalizer (J : Set G))
    (hYJ : Yplus ≤ J) (hI : ¬ I ≤ M)
    (hθ : theta (M ⊓ I) = Yplus)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I) : ¬ J ≤ M ⊓ I := by
  intro hJM
  have hθY : theta Yplus = Yplus := by rw [← hθ, theta_idempotent]
  have hθJ : theta J = Yplus := le_antisymm ((theta_mono hJM).trans_eq hθ)
    (hθY.ge.trans (theta_mono hYJ))
  have hn : I ≤ normalizer (Yplus : Set G) := by
    rw [← hθJ]
    exact hJnormal.trans (normalizer_le_normalizer_theta J)
  exact hI (fun x hx => (hN.le ⟨hx, hn hx⟩).1)

/-- Kernel containment lifts image containment to M, so the preceding
obstruction holds in the actual centralizer quotient. -/
theorem action_image_outside_of_theta (Z Yplus M I J : Subgroup G)
    (hJI : J ≤ I) (hJnormal : I ≤ normalizer (J : Set G))
    (hYJ : Yplus ≤ J) (hI : ¬ I ≤ M)
    (hC : I ⊓ centralizer (localSpan Z I : Set G) ≤ M ⊓ I)
    (hθ : theta (M ⊓ I) = Yplus)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I) :
    ¬ localActionImage Z I J ≤ localActionImage Z I M := by
  intro him
  have hker : (localActionMap Z I).ker ≤ M.subgroupOf I := by
    rw [localActionMap, QuotientGroup.ker_mk']
    exact fun x hx => (hC ⟨x.property, hx⟩).1
  have hpre : J.subgroupOf I ≤ M.subgroupOf I ⊔ (localActionMap Z I).ker :=
    map_le_map_iff.mp him
  rw [sup_eq_left.mpr hker] at hpre
  apply normal_subgroup_outside_of_theta Yplus M I J hJnormal hYJ hI hθ hN
  intro j hj
  exact ⟨hpre (show (⟨j, hJI hj⟩ : I) ∈ J.subgroupOf I from hj), hJI hj⟩

/-- The global Thompson subgroup is normalized by its ambient subgroup. -/
theorem ambient_normalizes_thompson (I : Subgroup G) :
    I ≤ normalizer (elementaryAbelianMaxJ I : Set G) := by
  intro i hi
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ I).map (MulAut.conj i).toMonoidHom = elementaryAbelianMaxJ I
  rw [← elementaryAbelianMaxJ_map_equiv]
  exact congrArg elementaryAbelianMaxJ (mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer hi))

/-- The noncentral branch's commutator identity implies both the image
containment in (10ii) and the Thompson noncontainment in (11). -/
theorem lemma_15_3_11_11_of_commutator [Finite G]
    (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hθ : theta (d.MI I) = d.Yplus)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hcomm : d.Yplus = ⁅d.Yplus, elementaryAbelianMaxJ d.S⁆) :
    d.starImage I d.Yplus ≤ d.starImage I (elementaryAbelianMaxJ I) ∧
      ¬ d.starImage I (elementaryAbelianMaxJ I) ≤ d.starImage I d.M := by
  obtain ⟨P, hP⟩ := hSyl
  have hJS : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ I := by
    have h := map_mono (f := I.subtype) (elementaryAbelianMaxJ_sylow_le_top P)
    rw [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
      ← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
      hP, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hJnormal := ambient_normalizes_thompson I
  have hYJ : d.Yplus ≤ elementaryAbelianMaxJ I := by
    rw [hcomm]
    exact (commutator_mono le_rfl hJS).trans
      (le_normalizer_iff_commutator_le_right.mp (hYI.trans hJnormal))
  refine ⟨map_mono (comap_mono hYJ), ?_⟩
  exact action_image_outside_of_theta d.Z d.Yplus d.M I (elementaryAbelianMaxJ I)
    (sSup_le (fun _ ha => ha.1)) hJnormal hYJ hI.2 hC hθ hN

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
