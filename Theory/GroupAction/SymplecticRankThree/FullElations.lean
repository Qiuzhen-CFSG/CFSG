module
public import Theory.GroupAction.SymplecticRankThree.Kernel

/-!
# Full polar-block fixers from Higman condition (i)

Evaluation of the actual pointwise block kernel is a bijection onto each
punctured hyperbolic line: both have q elements and the action is semiregular.
Consequently every incidence permutation fixing that block pointwise belongs
to the original action. Transitivity gives the same assertion at every pole.
This will put all model transvections in the source action once the incidence
space is coordinatized, without assuming an equivariant model map.

Source: Higman (1964), §7(vii)–(viii) and Theorem 2(i), pp.152–154.
The proof uses q ≥ 2 and includes the binary field.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
open MulAction
variable {Ω G : Type*} [Finite Ω] [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
variable {q : ℕ} (D : PolarityDesign Ω q)
variable (hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y)

include hact

theorem kernel_eval_surjective (hq : 2 ≤ q) {a b : Ω}
    (hab : ¬ D.incident a b) (hk : q ≤ Nat.card (fixingSubgroup G (D.block a))) :
    ∀ x ∈ D.line a b \ {a}, ∃ g : fixingSubgroup G (D.block a), (g : G) • b = x := by
  let f : fixingSubgroup G (D.block a) → ↥(D.line a b \ {a}) := fun g =>
    ⟨(g : G) • b, D.map_mem_line_of_fixes_block (MulAction.toPerm (g : G))
      (hact g) ((mem_fixingSubgroup_iff G).mp g.property) b, by
        intro hh
        have ha := ((mem_fixingSubgroup_iff G).mp g.property) a (D.refl a)
        have hba := (MulAction.injective (g : G)) (hh.trans ha.symm)
        exact hab (hba.symm ▸ D.refl a)⟩
  have hi : Function.Injective f := fun g h he =>
    D.kernel_eval_injective hact hq hab (congrArg Subtype.val he)
  have hc : Nat.card (fixingSubgroup G (D.block a)) = Nat.card ↥(D.line a b \ {a}) := by
    change Nat.card (fixingSubgroup G (D.block a)) = (D.line a b \ {a}).ncard
    rw [D.kernel_card_eq hact hq hab hk,
      Set.ncard_sdiff_singleton_of_mem (D.left_mem_line a b),
      D.hyperbolic_line_card_of_kernel hact hq hab hk]
    omega
  intro x hx
  obtain ⟨g,hg⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩).surjective ⟨x,hx⟩
  exact ⟨g,congrArg Subtype.val hg⟩

theorem block_fixer_mem_action (hq : 2 ≤ q) {a b : Ω}
    (hab : ¬ D.incident a b) (hk : q ≤ Nat.card (fixingSubgroup G (D.block a)))
    (e : Equiv.Perm Ω)
    (he : ∀ x y, D.incident (e x) (e y) ↔ D.incident x y)
    (hf : ∀ x ∈ D.block a, e x = x) :
    ∃ g : fixingSubgroup G (D.block a), MulAction.toPerm (g : G) = e := by
  have hne : e b ≠ a := by
    intro hh
    have hba := e.injective (hh.trans (hf a (D.refl a)).symm)
    exact hab (hba.symm ▸ D.refl a)
  obtain ⟨g,hgb⟩ := D.kernel_eval_surjective hact hq hab hk (e b)
    ⟨D.map_mem_line_of_fixes_block e he hf b,hne⟩
  have hgf := (mem_fixingSubgroup_iff G).mp g.property
  have hcomp := D.eq_refl_of_fixes_block_and_point hq
    (e.trans (MulAction.toPerm (g : G)⁻¹))
    (fun x y => (hact _ _ _).trans (he x y))
    (fun x hx => by
      change (g : G)⁻¹ • e x = x
      rw [hf x hx]
      exact inv_smul_eq_iff.mpr (hgf x hx).symm) hab
    (by change (g : G)⁻¹ • e b = b; rw [← hgb,inv_smul_smul])
  refine ⟨g,?_⟩
  ext x
  have hx := Equiv.congr_fun hcomp x
  change (g : G)⁻¹ • e x = x at hx
  exact eq_inv_smul_iff.mp hx.symm

theorem all_block_fixers_mem_action [IsPretransitive G Ω]
    (hq : 2 ≤ q) {a b : Ω} (hab : ¬ D.incident a b)
    (hk : q ≤ Nat.card (fixingSubgroup G (D.block a)))
    (x : Ω) (e : Equiv.Perm Ω)
    (he : ∀ u v, D.incident (e u) (e v) ↔ D.incident u v)
    (hf : ∀ y ∈ D.block x, e y = y) :
    ∃ g : G, MulAction.toPerm g = e := by
  obtain ⟨t,ht⟩ := exists_smul_eq G a x
  let e' := (MulAction.toPerm t).trans (e.trans (MulAction.toPerm t⁻¹))
  have he' : ∀ u v, D.incident (e' u) (e' v) ↔ D.incident u v :=
    fun u v => (hact _ _ _).trans ((he _ _).trans (hact _ _ _))
  have hf' : ∀ y ∈ D.block a, e' y = y := by
    intro y hy
    have hty : t • y ∈ D.block x := ht ▸ (hact t a y).mpr hy
    change t⁻¹ • e (t • y) = y
    rw [hf _ hty,inv_smul_smul]
  obtain ⟨g,hg⟩ := D.block_fixer_mem_action hact hq hab hk e' he' hf'
  refine ⟨t * g * t⁻¹,?_⟩
  ext y
  have hh := Equiv.congr_fun hg (t⁻¹ • y)
  change (g : G) • (t⁻¹ • y) = t⁻¹ • e (t • (t⁻¹ • y)) at hh
  simp only [MulAction.toPerm_apply,mul_smul]
  rw [hh,smul_inv_smul,smul_inv_smul]

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
