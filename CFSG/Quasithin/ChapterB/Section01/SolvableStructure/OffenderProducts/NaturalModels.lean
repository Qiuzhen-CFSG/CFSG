module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction
public import Theory.Representation.BinaryTwoPlaneRecognition


/-!
# Natural coordinates for the faithful one- and two-factor actions

One factor is the whole group once the centralizer is trivial, and its
specified natural coordinates are therefore coordinates for every actor.
With two factors, conjugation permutes their actual complementary planes.
The binary two-plane recognition theorem then identifies the faithful
order-72 action with the full specified quadratic isometry group.
Both alternatives intertwine the original representation pointwise.

Source: Aschbacher–Smith, 14.1.7, printed p.977, with the concrete binary
plus-four model described on printed pp.1121–1122.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem action_mem_factor_support (g : G) (i : Fin d.count) {v : V}
    (hv : v ∈ subspaceCommutator ρ ⊤ (d.factor i)) :
    ρ g v ∈ subspaceCommutator ρ ⊤ (d.factor (d.factorConjugation g i)) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, w, _, rfl⟩ := hv
    have hx' : g * x * g⁻¹ ∈ d.factor (d.factorConjugation g i) := by
      rw [← d.factor_map_conj]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    have he : ρ g (ρ x w - w) = ρ (g * x * g⁻¹) (ρ g w) - ρ g w := by
      rw [map_sub]
      congr 1
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [he]
    exact Submodule.subset_span ⟨_, hx', ρ g w, Submodule.mem_top, rfl⟩
  | zero => simp
  | add x y hx hy hfx hfy => simpa only [map_add] using Submodule.add_mem _ hfx hfy
  | smul a x hx hfx => simpa only [map_smul] using Submodule.smul_mem _ a hfx

theorem one_factor_natural_coordinates (hn : d.count = 1)
    (hW : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤)
    (hc : centralizer (offenderSubgroup ρ : Set G) = ⊥) :
    ∃ (c : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v) := by
  let : Subsingleton (Fin d.count) := by rw [hn]; infer_instance
  let i : Fin d.count := ⟨0, d.count_pos⟩
  have hK : offenderSubgroup ρ = ⊤ := by
    apply top_unique
    intro g _
    have hh := d.factorConjugation_kernel_le
      (show g ∈ d.factorConjugation.ker from Subsingleton.elim _ _)
    simpa only [hc, sup_bot_eq] using hh
  have hi : d.factor i = ⊤ := by
    apply top_unique
    rw [← hK, ← d.iSup_factor]
    exact iSup_le fun j => (Subsingleton.elim j i).symm ▸ le_rfl
  have hWi : subspaceCommutator ρ ⊤ (d.factor i) = ⊤ := by
    rw [hi, ← hK]
    exact hW
  let eg : d.factor i ≃* G := MulEquiv.ofBijective (d.factor i).subtype
    ⟨Subtype.val_injective, fun g => ⟨⟨g, hi.symm ▸ mem_top g⟩, rfl⟩⟩
  let ev : subspaceCommutator ρ ⊤ (d.factor i) ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (subspaceCommutator ρ ⊤ (d.factor i)).subtype
      ⟨Subtype.val_injective, fun v => ⟨⟨v, hWi.symm ▸ Submodule.mem_top⟩, rfl⟩⟩
  let c := ev.symm.trans (d.naturalEquiv i)
  let e := eg.symm.trans (d.factorModel i)
  have hcval (w : subspaceCommutator ρ ⊤ (d.factor i)) : c (w : V) = d.naturalEquiv i w := by
    change d.naturalEquiv i (ev.symm (ev w)) = _
    rw [ev.symm_apply_apply]
  refine ⟨c, e, fun g v => ?_⟩
  have he := d.naturalEquiv_action i (eg.symm g) (ev.symm v)
  change ρ (eg (eg.symm g)) (ev (ev.symm v)) = _ at he
  rw [eg.apply_symm_apply, ev.apply_symm_apply] at he
  rw [he, hcval]
  exact (d.naturalEquiv i).apply_symm_apply _

theorem two_factor_orthogonal_coordinates [Finite G] [FiniteDimensional (ZMod 2) V]
    (hn : d.count = 2) (hf : Function.Injective ρ)
    (hW : subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤)
    (hc : centralizer (offenderSubgroup ρ : Set G) = ⊥)
    (hp : Function.Surjective d.factorConjugation) :
    ∃ (c : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : G ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ g v, c (ρ g v) = (e g).val (c v) := by
  let i : Fin d.count := ⟨0, d.count_pos⟩
  let j : Fin d.count := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; change 0 = 1 at this; omega
  have hall (k : Fin d.count) : k = i ∨ k = j := by
    have hk : k.val = 0 ∨ k.val = 1 := by omega
    exact hk.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  let A := subspaceCommutator ρ ⊤ (d.factor i)
  let B := subspaceCommutator ρ ⊤ (d.factor j)
  have hsup : (⨆ k, subspaceCommutator ρ ⊤ (d.factor k)) = A ⊔ B := by
    apply le_antisymm
    · exact iSup_le fun k => (hall k).elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
    · exact sup_le
        (le_iSup (fun k => subspaceCommutator ρ ⊤ (d.factor k)) i)
        (le_iSup (fun k => subspaceCommutator ρ ⊤ (d.factor k)) j)
  have hAB : IsCompl A B := ⟨d.supports_independent.pairwiseDisjoint hij,
    codisjoint_iff.mpr (hsup.symm.trans (d.iSup_support.trans hW))⟩
  have hmem (v : V) : (v ∈ A ∨ v ∈ B) ↔ ∃ k, v ∈ subspaceCommutator ρ ⊤ (d.factor k) := by
    constructor
    · exact fun h => h.elim (fun h => ⟨i, h⟩) (fun h => ⟨j, h⟩)
    · rintro ⟨k, hk⟩
      rcases hall k with rfl | rfl
      · exact Or.inl hk
      · exact Or.inr hk
  have hforward (g : G) {v : V} (hv : v ∈ A ∨ v ∈ B) : ρ g v ∈ A ∨ ρ g v ∈ B := by
    obtain ⟨k, hk⟩ := (hmem v).mp hv
    exact (hmem _).mpr ⟨d.factorConjugation g k, d.action_mem_factor_support g k hk⟩
  apply Representation.BinaryTwoPlaneRecognition.exists_isometry_coordinates ρ hf
    (by have hg := d.card_of_full_factorConjugation hc hp; rw [hn] at hg; norm_num at hg; exact hg) A B hAB
      (d.support_finrank i) (d.support_finrank j)
  intro g v
  constructor
  · intro hv
    have hh := hforward g⁻¹ hv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] using hh
  · exact hforward g

end CFSG.Quasithin.ChapterB.SolvableFFFactors
