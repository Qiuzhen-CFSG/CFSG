module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.SL2.EvenBorel
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The marked binary PSL₂ Sylow and its torus

Keep the field and projective equivalence supplied by the model. The
characteristic-two SL₂ quotient equivalence and Sylow conjugacy put the marked
Sylow in upper-unipotent coordinates. Its centralizer is itself. Squaring is
surjective in the field, so diagonal conjugation is irreducible on the root
group and has no common nonidentity fixed element when the field has at least
four elements. Transporting the diagonal complement retains its cyclic group
and its exact order.

These intrinsic calculations supply the binary linear branch of the Borel
action argument in Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.8(1), printed pp.247–248, using the argument on printed p.246.
-/

public section

open Subgroup Matrix Matrix.SpecialLinearGroup BenderSuzuki.Converse
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.LinearAction

variable {H : Type*} [Group H] [Finite H]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Sylow coordinates retain the originally supplied field and equivalence. -/
theorem sylow_coordinates (e : H ≃* PSL2 F) (S : Sylow 2 H) :
    ∃ f : H ≃* SL2 F, (S : Subgroup H).map f.toMonoidHom = upperUnipotent F := by
  let e0 := e.trans (MulEquiv.ofBijective (pi F) ⟨pi_injective, pi_surjective⟩).symm
  let R := S.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) R (upperUnipotentSylow F 2)
  refine ⟨e0.trans (MulAut.conj g), ?_⟩
  change (S : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e0.toMonoidHom) = _
  rw [← Subgroup.map_map]
  exact congrArg Sylow.toSubgroup hg

theorem fixing_sylow_inner (e : H ≃* PSL2 F) (S : Sylow 2 H)
    (a : MulAut H) (ha : ∀ x ∈ S, a x = x) : ∃ s ∈ S, a = MulAut.conj s := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨y, hy, he⟩ := Theory.PSL2.aut_fixing_sylow_inner R (MulAut.congr e a) (by
    rintro y ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, ha x hx])
  obtain ⟨s, hs, rfl⟩ := hy
  refine ⟨s, hs, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he

private theorem upper_not_fixed (hq : 4 ≤ Nat.card F)
    (s : SL2 F) (hs : s ∈ upperUnipotent F) (hne : s ≠ 1) :
    ∃ b ∈ rankOneBorel F, ⁅s, b⁆ ≠ 1 := by
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]; omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have ha2 : (a : F)^2 ≠ 1 := by
    intro he
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using he)
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F s).mp hs
  refine ⟨diag2 (a : F) a.ne_zero, diag_mem_rankOneBorel _ _, ?_⟩
  intro hc
  have he := commutatorElement_eq_one_iff_mul_comm.mp hc
  have he' : diag2 (a : F) a.ne_zero * transvection zero_ne_one t *
      (diag2 (a : F) a.ne_zero)⁻¹ = transvection zero_ne_one t := by
    rw [← he, mul_inv_cancel_right]
  rw [diag_conj_upper] at he'
  have ht : (a : F)^2 * t = t := by
    have hv := congrArg (fun x : SL2 F => x.val 0 1) he'
    simpa [transvection_coe] using hv
  have hz : t = 0 := (mul_eq_zero.mp (show ((a : F)^2 - 1) * t = 0 by
    linear_combination ht)).resolve_left (sub_ne_zero.mpr ha2)
  exact hne (by rw [hz, transvection_coeff_zero])

/-- Intrinsic matrix facts for the marked Sylow subgroup. -/
structure SylowGeometry (S : Sylow 2 H) (q : ℕ) : Prop where
  card : Nat.card S = q
  centralizer : Subgroup.centralizer (S : Set H) ≤ S
  moving : ∀ s ∈ S, s ≠ 1 → ∃ b ∈ normalizer (S : Set H), ⁅s, b⁆ ≠ 1
  irreducible : ∀ W : Subgroup H, W ≤ S →
    normalizer (S : Set H) ≤ normalizer (W : Set H) → W ≠ ⊥ → W = S
  complement : ∃ D : Subgroup H,
    IsCyclic D ∧ Nat.card D = q - 1 ∧ Disjoint (S : Subgroup H) D ∧
      (S : Subgroup H) ⊔ D = normalizer (S : Set H)

theorem sylow_geometry (e : H ≃* PSL2 F) (hq : 4 ≤ Nat.card F) (S : Sylow 2 H) :
    SylowGeometry S (Nat.card F) := by
  obtain ⟨f, hf⟩ := sylow_coordinates e S
  have hN : (normalizer (S : Set H)).map f.toMonoidHom = Borel F := by
    change (normalizer ((S : Subgroup H) : Set H)).map f.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hf, ← ChapterF.Source.Linear.unip_eq_upper,
      ChapterF.Source.Linear.unip_normalizer]
  have hU : upperUnipotent F = Unip F := ChapterF.Source.Linear.unip_eq_upper.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← card_map_of_injective (K := (S : Subgroup H)) (f := f.toMonoidHom) f.injective,
      hf, card_upperUnipotent]
  · intro x hx
    have hc : f x ∈ Subgroup.centralizer (upperUnipotent F : Set (SL2 F)) := by
      rw [← hf]
      exact map_centralizer_le_centralizer_image _ _ (mem_map_of_mem f.toMonoidHom hx)
    rw [Theory.SpecificGroups.SL2.EvenBorel.unipotent_centralizer, ← hf] at hc
    simpa only [f.symm_apply_apply] using (mem_map_equiv.mp hc)
  · intro s hs hne
    obtain ⟨b, hb, hmove⟩ := upper_not_fixed hq (f s)
      (hf ▸ mem_map_of_mem f.toMonoidHom hs) (fun he => hne (f.injective (he.trans (map_one f).symm)))
    have hb' : b ∈ (normalizer (S : Set H)).map f.toMonoidHom := by
      rw [hN]
      rwa [← ChapterF.Source.Linear.unip_normalizer, ChapterF.Source.Linear.unip_eq_upper]
    obtain ⟨b, hbN, rfl⟩ := hb'
    refine ⟨b, hbN, fun hc => hmove ?_⟩
    change ⁅f s, f b⁆ = 1
    rw [← map_commutatorElement, hc, map_one]
  · intro W hWS hn hne
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [hf]
    apply eq_upperUnipotent_of_normalized
    · exact hf ▸ map_mono hWS
    · intro hb
      apply hne
      exact Subgroup.map_injective (f := f.toMonoidHom) f.injective (hb.trans (Subgroup.map_bot _).symm)
    · have hn' := (map_mono (f := f.toMonoidHom) hn).trans (le_normalizer_map _)
      rw [hN] at hn'
      rwa [← ChapterF.Source.Linear.unip_normalizer, ChapterF.Source.Linear.unip_eq_upper] at hn'
  · let D := (Torus F).map f.symm.toMonoidHom
    have hd : D.map f.toMonoidHom = Torus F := by simp [D, Subgroup.map_map]
    have hc : IsCyclic (Torus F) := by
      rw [Torus_eq_range]
      exact isCyclic_of_surjective _ (torHom F).rangeRestrict_surjective
    have hcD : IsCyclic D := by
      let _ := hc
      exact isCyclic_of_surjective _
        (Subgroup.equivMapOfInjective (Torus F) f.symm.toMonoidHom f.symm.injective).surjective
    refine ⟨D, hcD, ?_, ?_, ?_⟩
    · rw [← card_map_of_injective (K := D) (f := f.toMonoidHom) f.injective, hd, Torus_eq_range]
      exact (Nat.card_congr (MonoidHom.ofInjective (torHom_injective (F := F))).toEquiv).symm.trans
        (Nat.card_units (α := F))
    · apply disjoint_iff.mpr
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [Subgroup.map_inf _ _ _ f.injective, hf, hd, hU, disjoint_iff.mp Unip_disjoint_Torus,
        Subgroup.map_bot]
    · apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [Subgroup.map_sup, hf, hd, hU, Unip_sup_Torus, hN]

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.LinearAction
