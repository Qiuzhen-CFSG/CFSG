module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Normalization
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Marked subgroup images in X/C_X(K*)

Restricting the star map through X retains the original star images.
Its kernel lies in C_X(K*), so image orders can only decrease and
commuting star images still commute in X̂. The selected nontrivial
V*-action makes V̂ nontrivial, hence of order two. It centralizes the
marked image of T_X, which is itself Sylow when T_X is Sylow in X.
The two 13.5.19 conclusions likewise ensure the nontrivial image of Y.

Source: Aschbacher–Smith, combined manuscript, 13.5.21 conditions
(i) and the first inclusions of (ii), p.923 (PDF p.940).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis)

/-- Restricting the star map through X gives the original marked image. -/
theorem starHom_map (A : Subgroup G) (hA : A ≤ X D K) :
    (A.subgroupOf (X D K)).map (starHom s h) = starImage D.H A := by
  change (A.subgroupOf (X D K)).map
    ((QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion (s.X_le_H h))) = _
  rw [← map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨x, hA hx⟩, hx, rfl⟩

variable [(componentCentralizer s h).Normal]

/-- Every marked subgroup is the image under X → X/C_X(K*). -/
def markedImage (A : Subgroup G) : Subgroup (Xhat s h) :=
  (A.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h))

abbrev Khat := markedImage s h K
abbrev Vhat := markedImage s h D.V
abbrev L1hat := markedImage s h D.L₁
abbrev That := markedImage s h (TX D K)

/-- The quotient representative of a member of A is in its marked image. -/
theorem markedImage_mk (A : Subgroup G) (a : X D K) (ha : (a : G) ∈ A) :
    QuotientGroup.mk' (componentCentralizer s h) a ∈ markedImage s h A :=
  mem_map_of_mem _ ha

theorem markedImage_mono {A B : Subgroup G} (hAB : A ≤ B) :
    markedImage s h A ≤ markedImage s h B := map_mono (comap_mono hAB)

omit [(componentCentralizer s h).Normal] in
private theorem star_kernel_le : (starHom s h).ker ≤ componentCentralizer s h := by
  intro x hx
  change starHom s h x ∈ centralizer (starImage D.H K : Set (Hstar D.H))
  rw [MonoidHom.mem_ker.mp hx]
  exact one_mem _

/-- Nontrivial action on K* survives precisely the centralizer quotient. -/
theorem markedImage_ne_bot_of_moved (A : Subgroup G) (hA : A ≤ X D K)
    (hm : ⁅starImage D.H K, starImage D.H A⁆ ≠ ⊥) : markedImage s h A ≠ ⊥ := by
  intro hz
  have hc : A.subgroupOf (X D K) ≤ componentCentralizer s h := by
    simpa only [markedImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz
  have ha : starImage D.H A ≤ centralizer (starImage D.H K : Set (Hstar D.H)) := by
    rw [← starHom_map s h A hA]
    exact map_le_iff_le_comap.mpr hc
  exact hm ((commutator_comm _ _).trans (commutator_eq_bot_iff_le_centralizer.mpr ha))

/-- Factoring the star kernel can only divide the order of each marked image. -/
theorem markedImage_card_dvd_star (A : Subgroup G) (hA : A ≤ X D K) :
    Nat.card (markedImage s h A) ∣ Nat.card (starImage D.H A) := by
  rw [← starHom_map s h A hA, markedImage, ← relIndex_ker, ← relIndex_ker,
    QuotientGroup.ker_mk']
  exact relIndex_dvd_of_le_left _ (star_kernel_le s h)

/-- Star-centralizing subgroups still centralize after taking the marked quotient. -/
theorem markedImage_commutator_eq_bot (A B : Subgroup G)
    (hA : A ≤ X D K) (hB : B ≤ X D K)
    (hc : ⁅starImage D.H A, starImage D.H B⁆ = ⊥) :
    ⁅markedImage s h A, markedImage s h B⁆ = ⊥ := by
  have hk : ⁅A.subgroupOf (X D K), B.subgroupOf (X D K)⁆ ≤ (starHom s h).ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator, starHom_map s h A hA, starHom_map s h B hB, hc]
  unfold markedImage
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hk.trans (star_kernel_le s h)

/-- The originally chosen T_X maps onto a Sylow subgroup of X̂. -/
theorem marked_TX_sylow (hs : Chapter1.IsSylowIn 2 (TX D K) (X D K)) :
    ∃ S : Sylow 2 (Xhat s h), (S : Subgroup (Xhat s h)) = That s h := by
  obtain ⟨P, hP⟩ := hs
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (componentCentralizer s h)), ?_⟩
  change (P : Subgroup (X D K)).map _ = _
  unfold That markedImage
  congr 1
  rw [← hP]
  exact (comap_map_eq_self_of_injective (X D K).subtype_injective _).symm

/-- The order-two star actor remains nontrivial, hence of order two, in X̂. -/
theorem Vhat_card_two (hv : D.V ≤ normalizer (K : Set G))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH) :
    Nat.card (Vhat s h) = 2 := by
  have hVX : D.V ≤ X D K :=
    (le_inf h.V_le_T hv).trans (le_sup_right.trans le_sup_right)
  have hd := markedImage_card_dvd_star s h D.V hVX
  rw [LocalGeometry.star_V_card_two h hindex hU] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact (markedImage_ne_bot_of_moved s h D.V hVX s.moved
      ((eq_bot_iff_card _).mpr he)).elim
  · exact he

/-- V̂ lies in and centralizes the marked Sylow image. -/
theorem Vhat_central (hv : D.V ≤ normalizer (K : Set G))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH) :
    Vhat s h ≤ That s h ∧
      Vhat s h ≤ centralizer (That s h : Set (Xhat s h)) := by
  have hVT : D.V ≤ TX D K := le_inf h.V_le_T hv
  have hTX : TX D K ≤ X D K := le_sup_right.trans le_sup_right
  refine ⟨markedImage_mono s h hVT, commutator_eq_bot_iff_le_centralizer.mp ?_⟩
  apply markedImage_commutator_eq_bot s h D.V (TX D K) (hVT.trans hTX) hTX
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply (star_actor_centralizes_sylow D h (LocalGeometry.star_V_card_two h hindex hU)).trans
  apply centralizer_le
  change starImage D.H (TX D K) ≤ starImage D.H D.T
  exact map_mono (comap_mono inf_le_left)

/-- The two conclusions of 13.5.19 force the actual image of Y to be nontrivial. -/
theorem Yhat_ne_bot (Y : Subgroup G) (hY : Y ≤ D.L₁)
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    markedImage s h Y ≠ ⊥ ∧ markedImage s h Y ≤ L1hat s h := by
  exact ⟨markedImage_ne_bot_of_moved s h Y
    (hY.trans (le_sup_left.trans le_sup_right)) (s.moved_by_Y Y himage hcore),
    markedImage_mono s h hY⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
