module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelSylow
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
/-!
# The original kernel radical acts inner on the A₅ quotient

The nontrivial residual X=O²(C_H(U)) acts nontrivially on L/O₂(L).
The solvable overlap H∩L has the original Sylow subgroup T∩L as its
normal two-core. Hence XT preserves that same Sylow subgroup and its
image in the marked A₅ quotient. The normal-two-actor theorem then
makes O₂(XT) act inner on L/O₂(L).

This proves the inner-action sentence in the original 13.2.9 argument,
on the literal quotient and conjugation maps. Its two source inputs are
the earlier Baumann normalizer bound and solvability of the outside H.
Source: Aschbacher–Smith 13.2.9, printed pp.880–881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The actual radical of XT acts by inner automorphisms on the original
marked A₅ quotient; neither a parity nor an inner-action premise remains. -/
theorem source_kernel_radical_action_inner
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let P := X ⊔ (T : Subgroup G)
    let hXM := (source_kernel_residual_moves_component d hH hB hZ hs hne).2.1
    let hPM := sup_le hXM d.normalizes_L
    ∀ r : pCore 2 P,
      (MulAut.congr d.quotient) (quotientAut (pCore 2 L)
        (L.normalizerMonoidHom ⟨r,hPM r.val.property⟩)) ∈
        MulAut.innerSubgroup (alternatingGroup (Fin 5)) := by
  let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
  let X := ((pResidual 2 C).map C.subtype).map H.subtype
  let P := X ⊔ (T : Subgroup G)
  obtain ⟨hXH,hXM,hnX,hXne,hpX,hmove⟩ :=
    source_kernel_residual_moves_component d hH hB hZ hs hne
  have hPM : P ≤ normalizer (L : Set G) := sup_le hXM d.normalizes_L
  have hPH : P ≤ H := sup_le hXH hH.1.1.2
  let q₀ := QuotientGroup.mk' (pCore 2 L)
  let q := d.quotient.toMonoidHom.comp q₀
  let a : P →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr d.quotient).toMonoidHom.comp
      ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hPM)))
  have ha (x : P) (k : L) : a x (q k) =
      q (L.normalizerMonoidHom ⟨x,hPM x.property⟩ k) := by
    change d.quotient ((quotientAut (pCore 2 L) (L.normalizerMonoidHom
      ⟨x,hPM x.property⟩)) (d.quotient.symm (d.quotient (q₀ k)))) = _
    rw [d.quotient.symm_apply_apply,quotientAut_apply_mk]
    rfl
  obtain ⟨S,hS⟩ := source_component_sylow d
  let S' := S.mapSurjective (f := q) (d.quotient.surjective.comp (QuotientGroup.mk'_surjective _))
  have hnS : P ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf hPH hPM).trans (source_overlap_normalizes_component_sylow d hH.1.1.2 hs)
  have haS (x : P) : (S' : Subgroup (alternatingGroup (Fin 5))).map (a x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a x (q k) ∈ (S' : Subgroup (alternatingGroup (Fin 5)))
    rw [ha]
    apply mem_map_of_mem
    apply (mem_map_iff_mem L.subtype_injective).mp
    rw [hS]
    exact le_normalizer_iff.mp hnS x x.property k (hS ▸ mem_map_of_mem L.subtype hk)
  let D := X.subgroupOf P
  let eD : D ≃* X := subgroupOfEquivOfLe le_sup_left
  have hD : IsPPerfect 2 D := hpX.of_surjective eD.symm.toMonoidHom eD.symm.surjective
  have hnona : ∃ b : D, a b ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hmove
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx k hk
    let x' : D := ⟨⟨x,mem_sup_left hx⟩,hx⟩
    let k' : L := ⟨k,hk⟩
    let n : L := L.normalizerMonoidHom ⟨x,hXM hx⟩ k'
    have hfix : q n = q k' := by
      have hh := congrArg (fun b : MulAut (alternatingGroup (Fin 5)) => b (q k')) (hall x')
      rw [ha] at hh
      exact hh
    have hfix₀ : q₀ n = q₀ k' := d.quotient.injective hfix
    have hcore : n * k'⁻¹ ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q₀ (n * k'⁻¹) = 1
      rw [map_mul,map_inv,hfix₀,mul_inv_cancel]
    exact mem_map_of_mem L.subtype hcore
  exact Theory.SpecificGroups.Alternating.FiveSylowRadical.normal_two_action_inner
    S' a haS D (pCore 2 P) hD pCore_isPGroup hnona
end CFSG.Quasithin.Chapter13.Section02.A5Outside
