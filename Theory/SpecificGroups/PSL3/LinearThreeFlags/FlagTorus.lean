module
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.SubspaceTransport
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Split torus order in three-space flag stabilizers

A proper partial flag in a three-space has one or two members. For a full
flag, an adapted basis puts the diagonal determinant-one torus inside its
literal stabilizer. A single subspace is transported to the standard point
or plane parabolic, each containing the standard Borel. Thus the square of
q−1 divides the stabilizer order. In particular, over an even-degree binary
field its order is divisible by nine.

This supplies the actual normalizer-order obstruction in Aschbacher--Smith,
13.3.12, printed pp.889--890, after the C.2.7 type-A radical flag theorem.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.HigherLinear Matrix.HigherLinear.SubspaceTransport
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.LinearThree.FlagTorus
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem torus_preserves_basis_span
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) (s : Set (Fin 3))
    (d : Fˣ × Fˣ) :
    slConj b.equivFun.symm (torusSL F d) ∈ parabolicSL (Submodule.span F (b '' s)) := by
  let W := Submodule.span F (b '' s)
  have hf (a : Fˣ × Fˣ) (x : Fin 3 → F) (hx : x ∈ W) :
      Matrix.SpecialLinearGroup.toLin' (slConj b.equivFun.symm (torusSL F a)) x ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,hi,rfl⟩ := hx
        have he : Matrix.SpecialLinearGroup.toLin'
            (slConj b.equivFun.symm (torusSL F a)) (b i) =
              (![(a.1 : F), ((a.1 * a.2)⁻¹ : Fˣ), (a.2 : F)] i) • b i := by
          apply b.equivFun.injective
          rw [slConj_apply]
          simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, map_smul]
          change (torusSL F a).val.mulVec (b.equivFun (b i)) = _
          ext j
          fin_cases i <;> fin_cases j <;>
            simp [torusSL_val, Matrix.mulVec, dotProduct]
        rw [he]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using W.add_mem ihx ihy
    | smul a x hx ih => simpa only [map_smul] using W.smul_mem a ih
  intro x
  constructor
  · intro hx
    have hh := hf d⁻¹ _ hx
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using hh
  · exact hf d x

omit [Finite F] in
private theorem square_dvd_basis_flag
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) {ι : Type*} (s : ι → Set (Fin 3)) :
    (Nat.card F - 1)^2 ∣ Nat.card (⨅ i, parabolicSL (Submodule.span F (b '' s i)) : Subgroup SL(3,F)) := by
  let f := (slConj b.equivFun.symm).toMonoidHom.comp (torusSL F)
  have hinj : Function.Injective f :=
    (slConj b.equivFun.symm).injective.comp (BorelQuotient.torusSL_injective F)
  have hle : f.range ≤ ⨅ i, parabolicSL (Submodule.span F (b '' s i)) := by
    rintro _ ⟨d,rfl⟩
    exact mem_iInf.mpr (fun i => torus_preserves_basis_span b (s i) d)
  have hc : Nat.card f.range = (Nat.card F - 1)^2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_prod, Nat.card_units, pow_two]
  exact hc ▸ card_dvd_of_le hle

omit [Finite F] in
private theorem span_prefix (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (m : ℕ) (hm : m ≤ 3) :
    Set.range (fun i : Fin m => b (Fin.castLE hm i)) = b '' {i | i.val < m} := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.castLE hm,i.isLt,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i.val,hi⟩,rfl⟩

private theorem inf_pair {A : Type*} [CompleteLattice A] (f : Fin 2 → A) :
    (⨅ i, f i) = f 0 ⊓ f 1 := by
  apply le_antisymm (le_inf (iInf_le f 0) (iInf_le f 1))
  refine le_iInf (fun i => ?_)
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

omit [Finite F] in
private theorem square_dvd_pair (U W : Submodule F (Fin 3 → F))
    (hU : U ≠ ⊥) (hUW : U < W) (hW : W ≠ ⊤) :
    (Nat.card F - 1)^2 ∣ Nat.card (parabolicSL U ⊓ parabolicSL W : Subgroup SL(3,F)) := by
  have hpos : 0 < Module.finrank F U :=
    Nat.pos_of_ne_zero (fun h => hU (Submodule.finrank_eq_zero.mp h))
  have hlt := Submodule.finrank_lt_finrank_of_lt hUW
  have htop := Submodule.finrank_lt hW
  rw [Module.finrank_fin_fun] at htop
  have hu : Module.finrank F U = 1 := by omega
  have hw : Module.finrank F W = 2 := by omega
  let C : ℕ → Submodule F (Fin 3 → F) := fun i =>
    if i = 0 then ⊥ else if i = 1 then U else if i = 2 then W else ⊤
  have hm : Monotone C := by
    intro i j hij
    simp only [C]
    split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | exact hUW.le | omega
  have hd (i : ℕ) : Module.finrank F (C i) = min i (Module.finrank F (Fin 3 → F)) := by
    by_cases h0 : i = 0
    · subst i; simp [C]
    by_cases h1 : i = 1
    · subst i; simp [C,hu]
    by_cases h2 : i = 2
    · subst i; simp [C,hw]
    have hCi : C i = ⊤ := by simp [C,h0,h1,h2]
    rw [hCi,finrank_top,Module.finrank_fin_fun]
    omega
  have hb0 := Theory.AlgebraicGroup.exists_basis_adapted_to_full_submodule_chain C hm hd
  rw [Module.finrank_fin_fun] at hb0
  obtain ⟨b,hb⟩ := hb0
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  simp only [C,show (1 : ℕ) ≠ 0 by decide,show (2 : ℕ) ≠ 0 by decide,
    show (2 : ℕ) ≠ 1 by decide, if_false, if_true, span_prefix] at h1 h2
  have hh := square_dvd_basis_flag b (fun i : Fin 2 => {j | j.val < i.val+1})
  simpa only [inf_pair,Fin.val_zero,Fin.val_one,Nat.zero_add,Nat.reduceAdd,
    ←h1,←h2] using hh

/-- The literal partial-flag stabilizer contains a full split torus in SL₃. -/
theorem square_dvd_partialFlag {k : ℕ} (W : Fin k → Submodule F (Fin 3 → F))
    (hk : k = 1 ∨ k = 2) (hm : StrictMono W)
    (hp : ∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) :
    (Nat.card F - 1)^2 ∣ Nat.card (⨅ i, parabolicSL (W i) : Subgroup SL(3,F)) := by
  rcases hk with rfl | rfl
  · simp only [iInf_unique]
    rw [Subsingleton.elim (default : Fin 1) 0]
    have htorus : (Nat.card F - 1)^2 ∣ Nat.card (borelSL F) := by
      have hh := card_dvd_of_le (BorelQuotient.torusSL_le_borel F)
      rw [←Nat.card_congr (BorelQuotient.torusSLEquiv F).toEquiv,
        Nat.card_prod,Nat.card_units,←pow_two] at hh
      exact hh
    rcases SubspaceTransport.exists_parabolic_equiv (W 0) (hp 0).1 (hp 0).2 with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact htorus.trans (card_dvd_of_le inf_le_left)
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact htorus.trans (card_dvd_of_le inf_le_right)
  · rw [inf_pair]
    exact square_dvd_pair (W 0) (W 1) (hp 0).1 (hm (by decide)) (hp 1).2

/-- Three dividing q−1 forces nine to divide every proper partial-flag stabilizer. -/
theorem nine_dvd_partialFlag {k : ℕ} (W : Fin k → Submodule F (Fin 3 → F))
    (hk : k = 1 ∨ k = 2) (hm : StrictMono W)
    (hp : ∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) (hthree : 3 ∣ Nat.card F - 1) :
    9 ∣ Nat.card (⨅ i, parabolicSL (W i) : Subgroup SL(3,F)) := by
  have hh : 9 ∣ (Nat.card F - 1)^2 := by
    simpa only [pow_two, show 3*3=9 by decide] using Nat.mul_dvd_mul hthree hthree
  exact hh.trans (square_dvd_partialFlag W hk hm hp)

end Matrix.PSL3.LinearThree.FlagTorus
