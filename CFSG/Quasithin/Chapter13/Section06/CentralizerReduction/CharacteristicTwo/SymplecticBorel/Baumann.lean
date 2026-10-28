module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation
public import CFSG.Quasithin.ChapterB.Section02.ThompsonProduct

/-!
# Assembly of the symplectic Baumann and Borel argument

The specified Sylow identifies T_K with T_v ∩ K; T_C is literally C_{T_v}(K).
Maximum-elementary placement and the kernel of the action on Ω₁(Z(T_K)) imply
the Thompson product, the omega-center product, and Baum(T_v)=T_K Baum(T_C).
The multiplication equivalence keeps both factor embeddings. The actual Borel
N_K(T_K) then normalizes Baum(T_v), giving its containment in C_{M_V}(v)
from precisely the 13.6.4 equality and the relative 13.6.5 normalizer control.

The two geometric premises remain explicit in the exported reductions. They
must be established from the normalized symplectic component configuration
before this supplies the source conclusion; no completed 13.6.6 is asserted.
The independent maximal-elementary and center-action branches can import
Baumann.Basic without importing this assembly module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.927 (PDF p.944).
-/

public section
open Subgroup Stellmacher CFSG.Quasithin.ChapterB
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2] [Finite H]
variable (K : Subgroup H) (e : K ≃* Sp F)


theorem decomposition_of_local_geometry {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (R : Subgroup H) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R,
      E ≤ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)))
    (hkernel : R ⊓ centralizer (omegaOneCenterAmbient (R ⊓ K) : Set H) ≤
      (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H))) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (R ⊓ K) ⊔
        elementaryAbelianMaxJ (R ⊓ centralizer (K : Set H)) ∧
    thompsonAlpha R = (center ↥(R ⊓ K)).map (R ⊓ K).subtype ⊔
        thompsonAlpha (R ⊓ centralizer (K : Set H)) ∧
    baumann R = (R ⊓ K) ⊔ baumann (R ⊓ centralizer (K : Set H)) := by
  have hd := component_inter_centralizer_disjoint K e R
  have hc : R ⊓ K ≤ centralizer (R ⊓ centralizer (K : Set H) : Set H) :=
    inf_le_right.trans (le_centralizer_iff.mpr inf_le_right)
  have hJ : elementaryAbelianMaxJ (R ⊓ K) = R ⊓ K := by
    rw [← hSyl]
    exact localSylow_thompson K e hF hn.le S
  have hz : omegaOneCenterAmbient (R ⊓ K) =
      (center ↥(R ⊓ K)).map (R ⊓ K).subtype := by
    rw [← hSyl]
    exact localSylow_omegaCenter K e hF hn.le S
  refine ⟨thompson_product_of_maximal_placement R _ _ inf_le_left inf_le_left hd hc hmax, ?_,
    baumann_product_of_maximal_placement R _ _ inf_le_left inf_le_left hd hc hmax hJ hkernel⟩
  rw [← hz]
  exact thompsonAlpha_product_of_maximal_placement R _ _ inf_le_left inf_le_left hd hc hmax hJ

/-- The source's internal product retains multiplication and the ambient embeddings. -/
theorem baumann_mulEquiv_of_local_geometry {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (R : Subgroup H) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R,
      E ≤ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)))
    (hkernel : R ⊓ centralizer (omegaOneCenterAmbient (R ⊓ K) : Set H) ≤
      (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H))) :
    ∃ d : ↥(R ⊓ K) × baumann (R ⊓ centralizer (K : Set H)) ≃* baumann R,
      ∀ a c, (d (a,c) : H) = (a : H) * (c : H) := by
  have hd := (component_inter_centralizer_disjoint K e R).mono_right
    (show baumann (R ⊓ centralizer (K : Set H)) ≤ R ⊓ centralizer (K : Set H) from inf_le_left)
  have hc : R ⊓ K ≤ centralizer (baumann (R ⊓ centralizer (K : Set H)) : Set H) := by
    apply le_centralizer_iff.mpr
    exact (inf_le_left.trans inf_le_right).trans (centralizer_le (show R ⊓ K ≤ K from inf_le_right))
  obtain ⟨d, hd⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  have hB := (decomposition_of_local_geometry K e hF hn R S hSyl hmax hkernel).2.2
  exact ⟨d.trans (MulEquiv.subgroupCongr hB.symm), hd⟩

theorem borel_normalizes_baumann_of_local_geometry {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (R : Subgroup H) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups R,
      E ≤ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)))
    (hkernel : R ⊓ centralizer (omegaOneCenterAmbient (R ⊓ K) : Set H) ≤
      (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H))) :
    borelIn K e S ≤ normalizer (baumann R : Set H) := by
  have hB := (decomposition_of_local_geometry K e hF hn R S hSyl hmax hkernel).2.2
  rw [hB]
  apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · rw [← hSyl]
    exact borelIn_normalizes_localSylow K e S
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact (inf_le_left.trans inf_le_right).trans (centralizer_le (borelIn_le_component K e S))

/-- Application of exactly 13.6.4 and the relative normalizer control of 13.6.5.
The two local geometry premises are still to be discharged for the source theorem. -/
theorem source_borel_containment_of_local_geometry {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (T M V : Subgroup H) (v : H)
    (hK : K ≤ Gv v) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = Tv T v ⊓ K)
    (hmax : ∀ E ∈ elementaryAbelianMaxSubgroups (Tv T v),
      E ≤ (Tv T v ⊓ K) ⊔ (Tv T v ⊓ centralizer (K : Set H)))
    (hkernel : Tv T v ⊓ centralizer (omegaOneCenterAmbient (Tv T v ⊓ K) : Set H) ≤
      (Tv T v ⊓ K) ⊔ (Tv T v ⊓ centralizer (K : Set H)))
    (h1364 : baumann T = baumann (Tv T v))
    (h1365 : Gv v ⊓ normalizer (baumann T : Set H) ≤ Mv M v)
    (hMv : Mv M v = normalizer (V : Set H) ⊓ Gv v) :
    borelIn K e S ≤ normalizer (baumann T : Set H) ∧
      borelIn K e S ≤ normalizer (V : Set H) ⊓ Gv v := by
  have hN : borelIn K e S ≤ normalizer (baumann T : Set H) := by
    rw [h1364]
    exact borel_normalizes_baumann_of_local_geometry K e hF hn (Tv T v) S hSyl hmax hkernel
  exact ⟨hN, (le_inf ((borelIn_le_component K e S).trans hK) hN).trans
    (h1365.trans_eq hMv)⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
