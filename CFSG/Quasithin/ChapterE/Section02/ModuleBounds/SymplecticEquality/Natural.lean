module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticEquality.Irreducible
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import Theory.Representation.Quotient

/-!
# Natural recognition of the actual nonbinary symplectic core

At actor rank at most 2m, a noncentral chief factor exhausts P/Z.
The original action is therefore irreducible; J=O₂(X) acts trivially.
Its descent along the actual X/J marking is a faithful Sp₄ action.
The genuine binary degree-gap theorem recognizes that action as the
natural module, allowing the graph automorphism in the group equivalence.
Both the linear chart and its original conjugation identity are retained.

Source: Aschbacher–Smith E.2.15, printed p.228, using G.9.3(9).
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem symplectic_four_core_natural_of_rank_le
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Sp F)
    (hrank : Nat.log 2 ((Z V g).relIndex (A V M g)) ≤ 2*m) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    letI := ZMod.algebra F 2
    ∃ η : (X ⧸ J M) ≃* commutator (Sp F),
    ∃ e : Additive ((P V M g).map q) ≃ₗ[ZMod 2] ((Fin 2 ⊕ Fin 2) → F),
      ∀ x u, e (normalRepresentation ((P V M g).map q) (q x) u) =
        binaryNatural F (η (QuotientGroup.mk' (J M) x)) (e u) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.elementary
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  let ρ := normalRepresentation U
  let σ := ρ.comp q
  let : IsIrreducible ρ := h.symplectic_four_core_action_irreducible_of_rank_le
    hproper hfit m hm hcard ξ hrank
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q
    (QuotientGroup.mk'_surjective _) ρ).mpr inferInstance
  have hk : J M ≤ σ.ker := by
    rw [h.J_eq_twoCore_of_symplectic_four m hm hcard ξ]
    exact normal_p_subgroup_le_ker σ _ pCore_isPGroup
  let τ := quotientOfLEKer σ (J M) hk
  let ψ := τ.comp ξ.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff σ _ hk).mpr inferInstance
  let : IsIrreducible ψ := (irreducible_comp_surjective_iff ξ.symm.toMonoidHom
    ξ.symm.surjective τ).mpr inferInstance
  have hact (x : X) (u : Additive U) :
      ψ (ξ (QuotientGroup.mk' (J M) x)) u = ρ (q x) u := by
    simp only [ψ,τ,σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      ξ.symm_apply_apply,quotientOfLEKer_apply]
  have hn : ∃ a, ψ a ≠ 1 := by
    by_contra! hn
    have hr := h.quotient_core_noncentral_chief_exists hproper hfit
    obtain ⟨s⟩ := SeriesOn.exists_series U
    obtain ⟨i,hi⟩ := hr s
    apply hi
    rw [s.central_iff_action]
    intro x u
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Z V g) x
    have hs : ρ (q x) = 1 := by
      ext v
      rw [← hact x v,hn]
    -- The whole original action is trivial, hence so is every literal chief factor.
    obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) u
    rw [← hz,s.action_mk]
    congr 1
    apply Subtype.ext
    have he := congrArg (fun a => (a (Additive.ofMul
      ⟨z, s.term_le i.succ z.property⟩)).toMul) hs
    exact congrArg (fun z : U => (z : X ⧸ Z V g)) he
  have hdim : Module.finrank (ZMod 2) (Additive U) ≤ 4*m := by
    have hh := h.quotient_core_finrank_eq_twice_actor
    dsimp only [U,q] at ⊢
    omega
  have hF : 3 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hm
    rw [hcard]
    omega
  let : IsSimpleGroup (Sp F ⧸ center (Sp F)) := SimpleQuotients.isSimpleGroup hF
  let : IsSimpleGroup (Sp F) := (EvenProjective.equiv (F := F)).isSimpleGroup
  have hψ : Function.Injective ψ := by
    apply ψ.ker_eq_bot_iff.mp
    rcases ψ.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact hk
    obtain ⟨s,hs⟩ := hn
    exact (hs (show s ∈ ψ.ker from hk ▸ mem_top s)).elim
  let : Group.IsPerfect (Sp F) := (CentralCovers.Even.isQuasisimple hF).toIsPerfect
  let d : commutator (Sp F) ≃* Sp F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv
  let θ := ψ.comp d.toMonoidHom
  let : IsIrreducible θ := (irreducible_comp_surjective_iff d.toMonoidHom
    d.surjective ψ).mpr inferInstance
  have hθ : Function.Injective θ := hψ.comp d.injective
  have hnature := Nonbinary.small_quasiequivalent hm hcard hθ (by omega)
  obtain ⟨a,e,he⟩ := quasiequivalent_of_comp_equiv d.symm hnature
  refine ⟨ξ.trans a,e,?_⟩
  intro x u
  rw [← hact x u]
  exact he _ _
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
