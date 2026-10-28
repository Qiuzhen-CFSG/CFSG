module
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Basic
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Conjugate

/-!
# The I.7.6 step of 16.2.12

The normalizer has index two in T, whereas a component Sylow has order
greater than two. Its proposed third conjugate therefore has nontrivial
relative normalizer. The checked I.7.6 theorem gives commutation. Conjugating
back by u gives the second commutation, with the actual swapped Sylow.
The subsequent placement and inner-action argument remain separate.

Source: Aschbacher–Smith, proof of 16.2.12, printed p.1176.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

public section

namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open CFSG.Quasithin.ChapterI.Section06To08

/-- The part of 16.1.6 used after the rank-one alternatives in 16.2.5
exclude its A₆ exception. The actor has arbitrary two-power order.
This is an explicit model premise; it does not assert its own validity. -/
@[expose] def SylowCentralizingInner (M : Type*) [Group M] : Prop :=
  ∀ (P : Sylow 2 M) (a : MulAut M), (∃ n : ℕ, a ^ (2 ^ n) = 1) →
    (∀ x ∈ (P : Subgroup M), a x = x) → ∃ m : M, a = MulAut.conj m

/-- The concrete Sylow-centralizing innerness property is invariant under
actual group isomorphisms, including arbitrary two-elements. -/
theorem SylowCentralizingInner.of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (h : SylowCentralizingInner A) (e : A ≃* B) : SylowCentralizingInner B := by
  intro P a ha hfix
  let Q : Sylow 2 A := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let b : MulAut A := (MulAut.congr e.symm) a
  have hb : ∃ n, b ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, by change (MulAut.congr e.symm) a ^ (2 ^ n) = 1; rw [← map_pow, hn, map_one]⟩
  have hQ : ∀ x ∈ (Q : Subgroup A), b x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e.symm (a (e (e.symm y))) = e.symm y
    rw [e.apply_symm_apply, hfix y hy]
  obtain ⟨x, hx⟩ := h Q b hb hQ
  refine ⟨e x, ?_⟩
  ext y
  have hh := congrArg e (DFunLike.congr_fun hx (e.symm y))
  change e (e.symm (a (e (e.symm y)))) = e (x * e.symm y * x⁻¹) at hh
  simpa only [e.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using hh

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

/-- The actual Sylow intersection is maximal among two-subgroups of L. -/
theorem component_sylow_maximal (h : CentralComponentSetup T z L)
    (R : Subgroup G) (hp : IsPGroup 2 R) (hRL : R ≤ L)
    (hQR : componentSylow T L ≤ R) : R ≤ componentSylow T L := by
  obtain ⟨P, hP⟩ := h.exists_component_sylow
  have hle : (P : Subgroup L) ≤ R.subgroupOf L := by
    rw [hP]
    intro x hx
    exact hQR ⟨hx, x.property⟩
  have heq := P.is_maximal' (hp.of_equiv (subgroupOfEquivOfLe hRL).symm) hle
  intro x hx
  have hx' : (⟨x, hRL hx⟩ : L) ∈ R.subgroupOf L := hx
  rw [heq, hP] at hx'
  exact ⟨hx', hRL hx⟩

/-- The index-two normalizer and I.7.6 make a distinct conjugate centralize T_L. -/
theorem first_centralization (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hsize : 2 < Nat.card (componentSylow T L))
    {g : G} (hgT : conjSubgroup (componentSylow T L) g ≤ T)
    (hne : conjSubgroup (componentSylow T L) g ≠ componentSylow T L) :
    componentSylow T L ≤ centralizer (conjSubgroup (componentSylow T L) g : Set G) := by
  have hQne : componentSylow T L ≠ ⊥ := by
    intro hb
    simp [hb] at hsize
  have hsetup : TightPGroupSetup L ⊤ (componentSylow T L) T := by
    refine ⟨htight, T.isPGroup'.to_le inf_le_left, hQne,
      le_inf le_top inf_le_right, ?_, T.isPGroup', le_top, inf_le_left⟩
    intro R hp hRL hQR
    exact component_sylow_maximal h.localSetup R hp (hRL.trans inf_le_right) hQR
  have hN : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer (componentSylow T L : Set G) := by
    exact (inf_le_inf (T : Subgroup G).le_normalizer le_rfl).trans
      inf_normalizer_le_normalizer_inf
  have hi : (normalizer (L : Set G)).relIndex (conjSubgroup (componentSylow T L) g) ≤ 2 := by
    have hi := relIndex_le_of_le_right (H := normalizer (L : Set G)) hgT (by rw [h.index_sylow]; decide)
    rwa [h.index_sylow] at hi
  have hin : conjSubgroup (componentSylow T L) g ⊓ normalizer (L : Set G) ≠ ⊥ := by
    intro hb
    rw [← inf_relIndex_right, inf_comm, hb, relIndex_bot_left, card_conjSubgroup] at hi
    omega
  have hn : conjSubgroup (componentSylow T L) g ⊓ normalizer (componentSylow T L : Set G) ≠ ⊥ := by
    intro hb
    apply hin
    apply eq_bot_iff.mpr
    calc
      conjSubgroup (componentSylow T L) g ⊓ normalizer (L : Set G) ≤
          conjSubgroup (componentSylow T L) g ⊓ normalizer (componentSylow T L : Set G) :=
        le_inf inf_le_left ((le_inf (inf_le_left.trans hgT) inf_le_right).trans hN)
      _ = ⊥ := hb
  exact (lemma_I_7_6_commuting hsetup (mem_top g) hne hgT hn).2

omit [Finite G] in
/-- Transport pointwise commutation by conjugation. -/
theorem conjugate_centralizes {A B : Subgroup G} (hab : A ≤ centralizer (B : Set G)) (g : G) :
    conjSubgroup A g ≤ centralizer (conjSubgroup B g : Set G) := by
  rintro a ⟨a, ha, rfl⟩ b ⟨b, hb, rfl⟩
  exact (MulAut.conj g).toMonoidHom.map_mul b a ▸
    ((MulAut.conj g).toMonoidHom.map_mul a b ▸ congrArg (MulAut.conj g) (hab ha b hb))

/-- The same argument for the swapped component, using the inverse conjugator. -/
theorem second_centralization (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hsize : 2 < Nat.card (componentSylow T L))
    {g : G} (hgT : conjSubgroup (componentSylow T L) g ≤ T)
    (hne : conjSubgroup (componentSylow T L) g ≠ componentSylow T (conjSubgroup L u)) :
    componentSylow T (conjSubgroup L u) ≤
      centralizer (conjSubgroup (componentSylow T L) g : Set G) := by
  have ht : conjSubgroup (T : Subgroup G) u⁻¹ = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer (T.inv_mem h.u_mem))
  have hgt : conjSubgroup (componentSylow T L) (u⁻¹ * g) ≤ T := by
    rw [← conjSubgroup_conjSubgroup]
    exact (conjSubgroup_mono hgT u⁻¹).trans_eq ht
  have hne' : conjSubgroup (componentSylow T L) (u⁻¹ * g) ≠ componentSylow T L := by
    intro he
    apply hne
    have he' := congrArg (fun A => conjSubgroup A u) he
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left, h.swapped_sylow] at he'
    exact he'
  have hc := conjugate_centralizes (first_centralization h htight hsize hgt hne') u
  rw [h.swapped_sylow, conjSubgroup_conjSubgroup, mul_inv_cancel_left] at hc
  exact hc

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
