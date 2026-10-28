module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Symplectic.Orbit

/-!
# The symplectic TI contradiction

The proved intermediate assembly constructs the subgroup orbit and the actual
set β from multiplication coordinates, derives their TI and containment
properties from tight embedding and the genuine Δ₀ detector, and obtains the
Cartan lower bound using subgroup stabilizers. The published counting theorem
then contradicts the odd orbit length forced by the ambient Sylow subgroup.

This is not yet the source Sp₄ exclusion. The earlier Δ₀/common-residual setup
must still produce `U* ≤ Z(T_L*)`, elementary `C = Ω₁(T_C) ≃ U`,
`J(T) = T_L C`, and the fusion into `N_G(J(T))`; its center and Frattini
identities must identify V and W. The actual two-root-plane and Cartan witnesses
must also be constructed. These obligations are deliberately separate from
this intermediate theorem and are not asserted by a record projection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.5.13, printed p.1202.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic
open Subgroup
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The geometric TI contradiction with every counting premise discharged.
This is an intermediate assembly: its Thompson configuration must still be
constructed from the earlier source setup. -/
theorem contradiction_of_root_plane_configuration
    (T : Sylow 2 G) {L M V W C U : Subgroup G} (eL : L ≃* Sp F)
    (d : Splitting V C W) (p : RootPlane L W eL) (A : CartanAction p)
    (n : ℕ) (hq : Nat.card F = 2^n) (hn : 1 < n)
    (hK : Theory.GroupTheory.IsTightlyEmbedded (centralizer (L : Set G)))
    (hLK : Disjoint L (centralizer (L : Set G)))
    (hC : V ⊓ centralizer (L : Set G) = C)
    (hCT : C ≤ (T : Subgroup G)) (hC2 : ∀ c ∈ C, c ^ 2 = 1)
    (hr : 1 < Nat.card C)
    (hMV : M ≤ normalizer (V : Set G))
    (hMW : M ≤ normalizer (W : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hUC : ∃ m : M, C.conjBy m = U) (hU_ne : U ≠ C)
    (hAM : ∀ a, (A.hom a : G) ∈ M)
    (hdetect : ∀ J : Subgroup G,
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsModelRoot eL w) : False := by
  classical
  have hCK : C ≤ centralizer (L : Set G) := hC ▸ inf_le_right
  have hd : Disjoint C W := by
    apply Subgroup.disjoint_def.mpr
    intro x hxC hxW
    exact Subgroup.disjoint_def.mp hLK (p.le_component hxW) (hCK hxC)
  have hCp : IsPGroup 2 C := T.isPGroup'.to_le hCT
  have hTI : ∀ D ∈ conjugateFamily M C, ∀ E ∈ conjugateFamily M C,
      D ≠ E → Disjoint D E := by
    intro D hD E hE hne
    obtain ⟨a, rfl⟩ := (mem_conjugateFamily M C D).mp hD
    obtain ⟨b, rfl⟩ := (mem_conjugateFamily M C E).mp hE
    have hp : IsPGroup 2 ↥(V ⊓ centralizer (L : Set G)) := hC ▸ hCp
    simpa only [hC] using ti_conjugates_of_tightlyEmbedded_intersection
      hK hp hMV a.property b.property (by simpa only [hC] using hne)
  have hβ : ∀ D ∈ conjugateFamily M C, ∀ x ∈ D, x ≠ 1 → x ∈ beta d p := by
    intro D hD x hx hx1
    obtain ⟨a, rfl⟩ := (mem_conjugateFamily M C D).mp hD
    exact conjugate_mem_beta d p hd hLK hCK hC2 hMV hMW hdetect havoid a.property hx hx1
  obtain ⟨m, hm⟩ := hUC
  have hUf : U ∈ conjugateFamily M C := (mem_conjugateFamily M C U).mpr ⟨m, hm⟩
  have hCf : C ∈ conjugateFamily M C := (mem_conjugateFamily M C C).mpr ⟨1, C.conjBy_one⟩
  have hUcard : Nat.card U = Nat.card C := by
    rw [← hm]
    exact card_map_of_injective (MulAut.conj (m : G)).injective
  have hUV : U ≤ V := by
    rw [← hm]
    have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) d.left_le
    rwa [MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp (hMV m.property)] at hh
  have hUW : Disjoint U W := by
    rw [← hm]
    exact disjoint_conjugate_right hd (hMW m.property)
  have hUCdis := hTI U hUf C hCf hU_ne
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (hUcard ▸ hr)
  obtain ⟨x, hx⟩ := exists_ne (1 : U)
  have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hxC : (x : G) ∉ C := fun h => hx1 (Subgroup.disjoint_def.mp hUCdis x.property h)
  have hxβ := (mem_beta d p ⟨x, hUV x.property⟩).mp (hβ U hUf x x.property hx1)
  have hcoords :
      (p.coordinates (d.equiv ⟨x, hUV x.property⟩).2).1 ≠ 1 ∧
      (p.coordinates (d.equiv ⟨x, hUV x.property⟩).2).2 ≠ 1 := by
    rcases (mem_allowedProjections _).mp hxβ.2 with hz | hh
    · have hw : (d.equiv ⟨x, hUV x.property⟩).2 = 1 :=
        p.coordinates.injective (hz.trans (map_one p.coordinates).symm)
      exact (hxC ((d.mem_left_iff hd _).mpr hw)).elim
    · exact hh
  let ρ : (Fˣ × Fˣ) →* G := L.subtype.comp A.hom
  have hρC : ∀ a, ρ a ∈ normalizer (C : Set G) := by
    intro a
    apply centralizer_le_normalizer _
    intro c hc
    exact (mem_centralizer_iff.mp (hCK hc) (A.hom a) (A.hom a).property).symm
  have hfree : ∀ a, U.conjBy (ρ a) = U → a = 1 := by
    intro a ha
    exact cartan_subgroup_stabilizer d p A hd hCK hUV hUW (fun a => hMV (hAM a))
      x.property hcoords.1 hcoords.2 a ha
  have hlower := conjugateFamily_lower_bound ρ hAM hρC ⟨m, hm⟩ hU_ne hfree
  have hPcard : Fintype.card (Fˣ × Fˣ) = (Nat.card F - 1)^2 := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, Nat.card_units, pow_two]
  rw [hPcard] at hlower
  have hqeven : Even (Nat.card F) := by
    rw [hq]
    cases n with
    | zero => omega
    | succ n => exact ⟨2^n, by simp [pow_succ, mul_two]⟩
  have hq2 : 2 ≤ Nat.card F := by
    rw [hq]
    calc
      2 = 2^1 := by simp
      _ ≤ 2^n := Nat.pow_le_pow_right (by omega) (by omega)
  exact symplectic_ti_count_contradiction T M C hTM hTC (conjugateFamily M C)
    (beta d p) (Nat.card F) (Nat.card C) hqeven hq2 hr
    (mem_conjugateFamily M C) rfl hTI hβ (le_of_eq (card_beta d p)) hlower

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic
