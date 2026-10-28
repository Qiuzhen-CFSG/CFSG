module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.FFExtraction
public import CFSG.Quasithin.ChapterG.Section06.Elementary
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Initial branches of the transvection source argument

G.6.2 identifies the whole original space with the space moved by the normal
closure of the distinguished involution. Thus the hyperplane alternative of
B.5.6 is impossible. In its S3 alternative that space has dimension two;
faithfulness embeds the full ambient actor into GL2(2). The normal closure
already has order six, so the actor equals it, with the exact natural action.
This proves every clause of G.6.4 in that branch.

Source: Aschbacher–Smith, G.6.2 and G.6.4, printed pp.345–346, and B.5.6.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction ChapterB.QuasisimpleSource BinaryLinear.SmallParabolicLevi
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

private theorem moved_subtype_top (K : Subgroup G) :
  moved (ρ.comp K.subtype) ⊤ = subspaceCommutator ρ ⊤ K := by
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨g, _, w, hw, rfl⟩
    exact ⟨g, g.property, w, hw, rfl⟩
  · rintro ⟨g, hg, w, hw, rfl⟩
    exact ⟨⟨g, hg⟩, mem_top _, w, hw, rfl⟩

theorem Hypotheses.normalClosure_moved_eq_top (h : Hypotheses κ ρ a q) :
    moved (ρ.comp (normalClosure ({a} : Set G)).subtype) ⊤ = ⊤ := by
  rw [moved_subtype_top]
  exact lemma_G_6_2_1 ρ a h.generated

theorem Hypotheses.normalClosure_not_hyperplane (h : Hypotheses κ ρ a q)
    (d : HyperplaneCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) : False := by
  have hd := d.hyperplane
  rw [h.normalClosure_moved_eq_top, top_sup_eq] at hd
  have hz : Module.finrank (ZMod 2) (V ⧸ (⊤ : Submodule (ZMod 2) V)) = 0 :=
    Module.finrank_eq_zero_of_subsingleton _ _
  omega

theorem Hypotheses.conclusion_of_symmetricThree_normalClosure
    (h : Hypotheses κ ρ a q)
    (d : SymmetricThreeCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) :
    Conclusion ρ a := by
  classical
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  have hm := moved_subtype_top (ρ := ρ) K
  have hdim : Module.finrank (ZMod 2) V = 2 := by
    have hd := d.dimension
    change Module.finrank (ZMod 2) (moved (ρ.comp K.subtype) ⊤) = 2 at hd
    rw [hm, lemma_G_6_2_1 ρ a h.generated, finrank_top] at hd
    exact hd
  let E : V ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let j₀ : G →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hj₀ : Function.Injective j₀ := by
    intro x y he
    apply h.faithful
    exact congrArg LinearEquiv.toLinearMap he
  let j : G →* BinaryLinear.GL (Fin 2 → ZMod 2) :=
    (linearGroupCongr E).toMonoidHom.comp j₀
  have hj : Function.Injective j := (linearGroupCongr E).injective.comp hj₀
  let : Finite (BinaryLinear.GL (Fin 2 → ZMod 2)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Fin 2 → ZMod 2) => (g : (Fin 2 → ZMod 2) → _))
      DFunLike.coe_injective
  have hGL : Nat.card (BinaryLinear.GL (Fin 2 → ZMod 2)) = 6 := by
    rw [Nat.card_congr linearTwoEquivSymmetricThree.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hKcard : Nat.card K = 6 := by
    rw [Nat.card_congr d.equiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hGle : Nat.card G ≤ 6 := by simpa only [hGL] using Nat.card_le_card_of_injective j hj
  have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K (by
    have hl := K.card_le_card_group
    omega)
  have hGcard : Nat.card G = 6 := by simpa only [hKtop, Subgroup.card_top] using hKcard
  let e : G ≃* BinaryLinear.GL (Fin 2 → ZMod 2) :=
    MulEquiv.ofBijective j (hj.bijective_of_nat_card_le (by rw [hGL, hGcard]))
  have he (g : G) (v : V) : e g (E v) = E (ρ g v) := by
    change E ((j₀ g) (E.symm (E v))) = E (ρ g v)
    rw [E.symm_apply_apply]
    rfl
  have hmodel : HasModelOn ρ ⊤ ⊤ (binaryLinearAction 2) := by
    refine ⟨topEquiv.trans e, (Submodule.topEquiv).trans E, ?_, ?_⟩
    · intro g v
      exact Submodule.mem_top
    · intro g v
      exact (he g v).symm
  have hmoved : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    have hm := lemma_G_6_2_1 ρ a h.generated
    rwa [show normalClosure ({a} : Set G) = ⊤ from hKtop] at hm
  refine ⟨Or.inl ⟨hKtop, ?_, hmoved⟩, ?_⟩
  · rw [hmoved]
    exact Or.inl ⟨2, le_rfl, by decide, hmodel⟩
  · intro T _
    exact ⟨hKtop, Or.inl ⟨2, le_rfl, by decide, hmodel⟩⟩
end CFSG.Quasithin.ChapterG.Section06
