module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Conjugation
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Pointwise fixers of quadratic four-group displacement

A quadratic four-subgroup of the eight-element point core fixes its moved
plane pointwise. The full point core does not fix that plane, so its pointwise
fixer has order four and equals the actor. The statement is transported by the
literal permutation conjugation. Thus an intermediate point-core subgroup
centralizing the moved space and strictly larger than a nontrivial quadratic
actor forces that actor to have order two.

Source: MS93 (3.3)(ii) and its distance-two application (3.6), pp.867,871.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
open NaturalGeometry Representation.BinaryOffender

private theorem core_not_fix_plane :
    ¬ pointCore ≤ subspaceKernel (naturalRepresentation Ω) canonicalPlane pointCore := by
  intro h
  let b : S := Equiv.swap 0 2 * Equiv.swap 1 3
  have hb : b ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp [b])
  have hh := (h hb).2 (pairVector 0 1)
    (Submodule.subset_span (by simp))
  rw [pairVector_map] at hh
  have he : pair (b 0) (b 1) = pair 0 1 :=
    (pairVector_eq_iff (b.injective.ne (by decide)) (by decide)).mp hh
  have hn : pair (b 0) (b 1) ≠ pair 0 1 := by decide
  exact hn he

private theorem pointCore_normalized : H1 ≤ normalizer (pointCore : Set S) := by
  rw [← H1_core_eq_pointCore]
  exact H1.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H1 (pCore 2 H1))

theorem four_moved_fixer (A : Subgroup S) (hA : A ≤ pointCore)
    (hq : Quadratic A) (hc : Nat.card A = 4) :
    subspaceKernel (naturalRepresentation Ω)
      (subspaceCommutator (naturalRepresentation Ω) ⊤ A) pointCore = A := by
  let B := subspaceKernel (naturalRepresentation Ω)
    (subspaceCommutator (naturalRepresentation Ω) ⊤ A) pointCore
  have hAB : A ≤ B := by
    intro a ha
    refine ⟨hA ha, ?_⟩
    have hf : subspaceCommutator (naturalRepresentation Ω) ⊤ A ≤
        LinearMap.ker (naturalRepresentation Ω a - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,_,rfl⟩
      change naturalRepresentation Ω a (naturalRepresentation Ω b v-v) -
        (naturalRepresentation Ω b v-v)=0
      rw [hq a ha b hb v,sub_self]
    intro v hv
    have hh := hf hv
    simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hh
  have hB : B ≤ pointCore := subspaceKernel_le _ _ _
  have hne : B ≠ pointCore := by
    intro he
    obtain ⟨g,hg,hplane⟩ := quadratic_four_moved_plane A hA hq hc
    have hn := le_normalizer_iff.mp pointCore_normalized g hg.1
    apply core_not_fix_plane
    intro b hb
    refine ⟨hb, ?_⟩
    intro v hv
    have hbg : g*b*g⁻¹ ∈ B := by
      rw [he]
      exact hn b hb
    have hh := hbg.2 (naturalRepresentation Ω g v) (by
      rw [hplane]
      exact Submodule.mem_map_of_mem hv)
    apply (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation Ω).asGroupHom g)).injective
    change naturalRepresentation Ω g (naturalRepresentation Ω b v) = naturalRepresentation Ω g v
    rw [←hh]
    have hcancel : (g*b*g⁻¹)*g=g*b := by group
    simp only [←Module.End.mul_apply,←map_mul,hcancel]
  have hcard : Nat.card B ≤ 4 := by
    have hd : Nat.card B ∣ 8 := pointCore_card ▸ card_dvd_of_le hB
    have hn : Nat.card B ≠ 8 := by
      intro hh
      exact hne (eq_of_le_of_card_ge hB (by rw [hh,pointCore_card]))
    have hl : Nat.card B ≤ 8 := Nat.le_of_dvd (by decide) hd
    by_contra hh
    have hr : Nat.card B = 5 ∨ Nat.card B = 6 ∨ Nat.card B = 7 := by omega
    rcases hr with hr | hr | hr <;> rw [hr] at hd <;> norm_num at hd
  exact (eq_of_le_of_card_ge hAB (hc ▸ hcard)).symm

theorem conjugate_four_moved_fixer (A : Subgroup S) (g : S)
    (hA : A ≤ pointCore.map (MulAut.conj g).toMonoidHom)
    (hq : Quadratic A) (hc : Nat.card A = 4) :
    subspaceKernel (naturalRepresentation Ω)
      (subspaceCommutator (naturalRepresentation Ω) ⊤ A)
      (pointCore.map (MulAut.conj g).toMonoidHom) = A := by
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : B ≤ pointCore := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩ := hA ha
    rw [←he]
    change g⁻¹*(g*b*g⁻¹)*g ∈ pointCore
    have heq : g⁻¹*(g*b*g⁻¹)*g=b := by group
    rw [heq]
    exact hb
  have hBc : Nat.card B = 4 := (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hc
  have hfix := four_moved_fixer B hB (quadratic_conjugate A hq g⁻¹) hBc
  apply le_antisymm
  · rintro a ⟨ha,haf⟩
    let b := (MulAut.conj g⁻¹) a
    have hb : b ∈ B := by
      rw [←hfix]
      refine ⟨?_,?_⟩
      · obtain ⟨k,hk,rfl⟩ := ha
        simpa [b,MulAut.conj_apply,mul_assoc] using hk
      · intro v hv
        have hh := haf (naturalRepresentation Ω g v) (by
          rw [moved_conjugate A g]
          exact Submodule.mem_map_of_mem hv)
        apply (LinearMap.GeneralLinearGroup.toLinearEquiv
          ((naturalRepresentation Ω).asGroupHom g)).injective
        change naturalRepresentation Ω g (naturalRepresentation Ω b v) = naturalRepresentation Ω g v
        rw [←hh]
        have hgb : g*b=a*g := by dsimp [b];simp [mul_assoc]
        simp only [←Module.End.mul_apply,←map_mul,hgb]
    obtain ⟨k,hk,he⟩ := hb
    exact (MulAut.conj g⁻¹).injective he ▸ hk
  · intro a ha
    refine ⟨hA ha,?_⟩
    have hf : subspaceCommutator (naturalRepresentation Ω) ⊤ A ≤
        LinearMap.ker (naturalRepresentation Ω a - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,_,rfl⟩
      change naturalRepresentation Ω a (naturalRepresentation Ω b v-v) -
        (naturalRepresentation Ω b v-v)=0
      rw [hq a ha b hb v,sub_self]
    intro v hv
    simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hf hv

theorem card_two_of_centralizes_moved (A B : Subgroup S) (g : S)
    (hAB : A ≤ B) (hB : B ≤ pointCore.map (MulAut.conj g).toMonoidHom)
    (hfix : B ≤ subspaceKernel (naturalRepresentation Ω)
      (subspaceCommutator (naturalRepresentation Ω) ⊤ A) ⊤)
    (hne : A ≠ ⊥) (hproper : ¬ B ≤ A) : Nat.card A = 2 := by
  have hA := hAB.trans hB
  have hq : Quadratic A := by
    intro a ha b hb v
    exact (hfix (hAB ha)).2 _ (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
  have hle := conjugate_core_bound A g hA hq
  have hn4 : Nat.card A ≠ 4 := by
    intro hc
    apply hproper
    rw [←conjugate_four_moved_fixer A g hA hq hc]
    exact fun b hb => ⟨hB hb,(hfix hb).2⟩
  have hd : Nat.card A ∣ 8 := by
    have hd := card_dvd_of_le hA
    rwa [card_map_of_injective (MulAut.conj g).injective,pointCore_card] at hd
  have hn1 : 1 < Nat.card A := (A.one_lt_card_iff_ne_bot).mpr hne
  have hn3 : Nat.card A ≠ 3 := by intro h;rw [h] at hd;norm_num at hd
  omega

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
