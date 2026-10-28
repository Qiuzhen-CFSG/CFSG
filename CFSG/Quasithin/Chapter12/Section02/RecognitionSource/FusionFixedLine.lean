module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.GlobalTI
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.CentralizerSylowNormalizerFusion
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Fixed-line fusion in the reducible cases of 12.2.16

Suppose the original fixed subgroup C_V(L) has one nonidentity element z.
The structural alternative in 12.2.2 forces V to be normalized by M=N_G(L),
and M fixes z. NoEscape therefore identifies C_G(z) with M. A conjugate
of z lying in V has a centralizer contained in M of the same order, so it
also centralizes L and must equal z. This proves weak closure from the
original hypotheses, without assuming fusion control.

This yields two actual source applications. Transitivity off the fixed
line suffices for global TI (the module calculation in row (b)). In the
remaining reducible cases, a common Sylow centralizer whose central omega
contains z and lies in V gives an M-conjugator by Sylow conjugacy. In
particular this consumes the final omega-center containment in the A₈
argument; that containment remains a separate module-geometric obligation.
Source: Aschbacher--Smith 12.2.16, printed p.800.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- The structural normality alternative makes the original fixed involution central in M. -/
theorem normalizer_centralizes_fixed_line
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z) :
    normalizer (L : Set G) ≤ centralizer ({z} : Set G) := by
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural G T L h).2.2 V D).2.2.2 with hN | he
    · exact hN
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hz,hzL⟩)))).elim
  intro m hm
  have hmzV : m * z * m⁻¹ ∈ V := (mem_normalizer_iff.mp (hMV hm) z).mp hz
  have hmzL : m * z * m⁻¹ ∈ centralizer (L : Set G) :=
    (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer L hm) z).mp hzL
  have he : m * z * m⁻¹ = z := (hfixed _ hmzV hmzL).resolve_left
    (fun he => hz1 ((MulAut.conj m).map_eq_one_iff.mp he))
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- The fixed involution is weakly closed in the original V, by centralizer orders. -/
theorem fixed_line_weakly_closed
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    {w : G} (hw : w ∈ V) (hzw : IsConj z w) : w = z := by
  have hCz : centralizer ({z} : Set G) = normalizer (L : Set G) :=
    le_antisymm (hnone z hz hz1)
      (normalizer_centralizes_fixed_line h D structural hz hz1 hzL hfixed)
  obtain ⟨g,hg⟩ := isConj_iff.mp hzw
  have hw1 : w ≠ 1 := fun he => hz1
    ((MulAut.conj g).map_eq_one_iff.mp (hg.trans he))
  have hc : Nat.card (centralizer ({w} : Set G)) =
      Nat.card (normalizer (L : Set G)) := by
    rw [← hCz]
    have he := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z).toEquiv
    simpa only [MulAut.conj_apply,hg] using he.symm
  have hCw : centralizer ({w} : Set G) = normalizer (L : Set G) :=
    eq_of_le_of_card_ge (hnone w hw hw1) hc.ge
  have hwL : w ∈ centralizer (L : Set G) := by
    intro l hl
    have hh : l ∈ centralizer ({w} : Set G) := hCw ▸ L.le_normalizer hl
    exact mem_centralizer_singleton_iff.mp hh
  exact (hfixed w hw hwL).resolve_left hw1

/-- Transporting the fixed involution back into V forces membership in M. -/
theorem conjugator_mem_of_fixed_line_image
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    {g : G} (hgz : g * z * g⁻¹ ∈ V) : g ∈ normalizer (L : Set G) := by
  have he := fixed_line_weakly_closed h D structural hnone hz hz1 hzL hfixed hgz
    (isConj_iff.mpr ⟨g,rfl⟩)
  exact hnone z hz hz1 (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he))

/-- The final omega-center containment in the A₈ argument forces its normalizer into M. -/
theorem normalizer_le_of_fixed_line_in_omega
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (R : Subgroup G) (hzR : z ∈ omegaCenterIn R) (hRV : omegaCenterIn R ≤ V) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  apply conjugator_mem_of_fixed_line_image h D structural hnone hz hz1 hzL hfixed
  exact hRV ((mem_normalizer_iff.mp (normalizer_le_normalizer_omegaCenterIn R hg) z).mp hzR)

/-- A common centralizer Sylow with its central omega inside V supplies actual M-fusion. -/
theorem fusion_of_common_sylow_of_omega_le
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    {x y : G} (S : Sylow 2 (centralizer ({x} : Set G)))
    (hy : (S : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ≤ centralizer ({y} : Set G))
    (hzR : z ∈ omegaCenterIn ((S : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype))
    (hRV : omegaCenterIn ((S : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) ≤ V)
    (hxy : IsConj x y) : ∃ m ∈ normalizer (L : Set G), m * x * m⁻¹ = y := by
  obtain ⟨m,hm,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow x y S hy hxy
  exact ⟨m,normalizer_le_of_fixed_line_in_omega h D structural hnone hz hz1 hzL hfixed
    _ hzR hRV hm,he⟩

/-- Global TI follows from the off-fixed-line orbit calculation, as used in row (b). -/
theorem globalTI_of_transitive_off_fixed_line
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (ht : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 → x ≠ z → y ≠ z →
      ∃ l ∈ L, l * x * l⁻¹ = y) : IsTISubgroup V := by
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed h D structural hnone hz hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed h D structural hnone hz hz1 hzL hfixed hx hc.symm)
  obtain ⟨l,hl,he⟩ := ht x y hx hy hx1 hy1 hxz hyz
  exact ⟨l,L.le_normalizer hl,he⟩
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
