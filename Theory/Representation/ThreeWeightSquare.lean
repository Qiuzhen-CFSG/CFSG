module
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Frattini.SquareImage
public import Mathlib.RepresentationTheory.Intertwining
/-!
# Two-power automorphisms in three character weights

A faithful abelian representation of degree at most three has at most three
occurring characters, and they separate its actor. A natural or contragredient
automorphism permutes these characters, possibly inverting all of them.
Six iterations therefore act trivially, so a two-power automorphism has
square one. The actual Frattini subgroup of any acting two-group is killed.

This is the small weight argument for the nondefining odd degree-three
source cases in Aschbacher–Smith A.3.15 and Proposition1.3.4, pp.50–51,
510–511. The model-specific natural/contragredient formulas are separate.
-/

public section
noncomputable section
namespace Representation.ThreeWeightSquare
open Subgroup

private theorem perm_six {I : Type*} [Finite I] (hc : Nat.card I≤3)
    (π : Equiv.Perm I) : π^6=1 := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α:=I) (β:=Fin 3)
    (by simpa only [← Nat.card_eq_fintype_card,Nat.card_fin] using hc)
  apply Equiv.Perm.viaEmbeddingHom_injective e
  rw [map_pow,map_one]
  have hc6 : Nat.card (Equiv.Perm (Fin 3))=6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]; decide
  simpa only [hc6] using (pow_card_eq_one' (x := (Equiv.Perm.viaEmbeddingHom e) π))

/-- A two-power automorphism preserving three separating characters up to
simultaneous inversion has square one. -/
theorem square_eq_one {B U I : Type*} [Group B] [CommGroup U] [Finite I]
    (χ : I→B→*U) (hc : Nat.card I≤3)
    (hsep : ∀a b:B,(∀i,χ i a=χ i b)→a=b)
    (α : MulAut B) (ha : ∃n:ℕ,α^(2^n)=1)
    (π : Equiv.Perm I) (neg : Bool)
    (h : ∀i b,χ i (α b)=if neg then (χ (π i) b)⁻¹ else χ (π i) b) : α^2=1 := by
  have hp := perm_six hc π
  have hpi (i:I) : π (π (π (π (π (π i)))))=i := by
    simpa only [pow_succ,pow_zero,Equiv.Perm.mul_apply,Equiv.Perm.one_apply] using
      congrArg (fun f:Equiv.Perm I=>f i) hp
  have h6 : α^6=1 := by
    apply MulEquiv.ext
    intro b
    apply hsep
    intro i
    change χ i (α (α (α (α (α (α b))))))=χ i b
    cases neg <;> simp only [h,Bool.false_eq_true,if_false,if_true,inv_inv,hpi]
  obtain ⟨n,hn⟩ := ha
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h6)
  have hg : Nat.gcd (2^n) 6 ∣ 2 := by
    have h3 : Nat.Coprime (2^n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    exact h3.coprime_dvd_left (Nat.gcd_dvd_left (2^n) 6) |>.dvd_of_dvd_mul_right
      (show Nat.gcd (2^n) 6 ∣ 2*3 from Nat.gcd_dvd_right (2^n) 6)
  exact orderOf_dvd_iff_pow_eq_one.mp (hd.trans hg)

variable {E B V W : Type*} [Field E] [Group B]
  [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

theorem weight_comp (ρ : Representation E B V) (α : MulAut B)
    (χ : ρ.CharacterWeight) :
    characterWeightSpace (ρ.comp α.toMonoidHom) (χ.val.comp α.toMonoidHom)≠⊥ := by
  obtain ⟨v,hv,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.property
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v,?_,hn⟩
  simp only [characterWeightSpace,Submodule.mem_iInf,Module.End.mem_eigenspace_iff] at hv ⊢
  exact fun b=>hv (α b)

theorem weight_equiv {ρ : Representation E B V} {σ : Representation E B W}
    (e : Representation.Equiv ρ σ) (χ : B→*Eˣ)
    (hχ : ρ.characterWeightSpace χ≠⊥) : σ.characterWeightSpace χ≠⊥ := by
  obtain ⟨v,hv,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨e v,?_,fun he=>hn (e.injective (he.trans (map_zero e).symm))⟩
  simp only [characterWeightSpace,Submodule.mem_iInf,Module.End.mem_eigenspace_iff] at hv ⊢
  intro b
  have hh := LinearMap.congr_fun (e.isIntertwining' b) v
  change e (ρ b v)=σ b (e v) at hh
  rw [← hh,hv b,map_smul]

theorem weight_dual_inv [IsAlgClosed E] [FiniteDimensional E V] [IsMulCommutative B]
    (ρ : Representation E B V) (horder : (Nat.card B : E)≠0)
    (χ : B→*Eˣ) (hχ : ρ.dual.characterWeightSpace χ≠⊥) :
    ρ.characterWeightSpace χ⁻¹≠⊥ := by
  obtain ⟨f,hf,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  simp only [characterWeightSpace,Submodule.mem_iInf,Module.End.mem_eigenspace_iff] at hf
  by_contra hz
  have hzero : ∀ψ:ρ.CharacterWeight, ∀v∈ρ.characterWeightSpace ψ.val,f v=0 := by
    intro ψ v hv
    have hne : ψ.val≠χ⁻¹ := fun he=>ψ.property (he ▸ hz)
    obtain ⟨b,hb⟩ := DFunLike.ne_iff.mp hne
    have hcoeff : (ψ.val b : E)≠(χ b : E)⁻¹ := by
      intro he
      exact hb (Units.ext (by simpa using he))
    have hvb : ∀b,ρ b v=(ψ.val b : E) • v := by
      simpa only [characterWeightSpace,Submodule.mem_iInf,Module.End.mem_eigenspace_iff] using hv
    specialize hvb b
    change ρ b v=(ψ.val b : E) • v at hvb
    have hh := congrArg (fun l:Module.Dual E V=>l v) (hf b⁻¹)
    change f (ρ (b⁻¹)⁻¹ v)=((χ (b⁻¹) : E)) * f v at hh
    rw [inv_inv,hvb,map_smul] at hh
    simp only [map_inv,Units.val_inv_eq_inv_val,smul_eq_mul] at hh
    exact (mul_eq_mul_right_iff.mp hh).resolve_left hcoeff
  apply hn
  apply LinearMap.ext
  intro v
  have hh : (⊤ : Submodule E V) ≤ f.ker := by
    rw [← ρ.iSup_characterWeightSpace_eq_top horder]
    exact iSup_le fun ψ v hv=>hzero ψ v hv
  exact hh (Submodule.mem_top : v∈(⊤:Submodule E V))


/-- Natural or contragredient equivalence in dimension at most three makes
every two-power automorphism of the faithful abelian actor involutory. -/
theorem square_eq_one_of_equiv_or_dual
    [IsAlgClosed E] [FiniteDimensional E V] [IsMulCommutative B]
    (ρ : Representation E B V) (hρ : Function.Injective ρ)
    (horder : (Nat.card B : E)≠0) (hd : Module.finrank E V≤3)
    (α : MulAut B) (ha : ∃n:ℕ,α^(2^n)=1)
    (he : Nonempty (Representation.Equiv (ρ.comp α.toMonoidHom) ρ) ∨
      Nonempty (Representation.Equiv (ρ.comp α.toMonoidHom) ρ.dual)) : α^2=1 := by
  classical
  obtain ⟨hfin,hcard⟩ := characterWeight_card_le ρ horder
  let _ := hfin
  have hs (a b:B) (hh:∀χ:ρ.CharacterWeight,χ.val a=χ.val b) : a=b :=
    eq_of_characterWeight_values ρ hρ horder a b hh
  have main (neg : Bool)
      (hn : ∀χ:ρ.CharacterWeight, ρ.characterWeightSpace
        (if neg then (χ.val.comp α.toMonoidHom)⁻¹ else χ.val.comp α.toMonoidHom)≠⊥) :
      α^2=1 := by
    let f : ρ.CharacterWeight→ρ.CharacterWeight := fun χ=>⟨_,hn χ⟩
    have hf : Function.Injective f := by
      intro χ ψ heq
      have hh := congrArg Subtype.val heq
      apply Subtype.ext
      apply MonoidHom.ext
      intro b
      have hb := DFunLike.congr_fun hh (α.symm b)
      cases neg <;> simpa only [f,Bool.false_eq_true,if_false,if_true,
        MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MonoidHom.inv_apply,MulEquiv.apply_symm_apply,inv_inj] using hb
    let π : Equiv.Perm ρ.CharacterWeight := Equiv.ofBijective f
      ⟨hf,Finite.surjective_of_injective hf⟩
    apply square_eq_one (fun χ:ρ.CharacterWeight=>χ.val) (hcard.trans hd) hs α ha π neg
    intro χ b
    change χ.val (α b)=if neg then ((f χ).val b)⁻¹ else (f χ).val b
    cases neg <;> simp only [f,Bool.false_eq_true,if_false,if_true,
      MonoidHom.inv_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,inv_inv]
  rcases he with he | he
  · obtain ⟨e⟩ := he
    apply main false
    intro χ
    exact weight_equiv e _ (weight_comp ρ α χ)
  · obtain ⟨e⟩ := he
    apply main true
    intro χ
    exact weight_dual_inv ρ horder _ (weight_equiv e _ (weight_comp ρ α χ))

/-- The actual Frattini subgroup acts trivially through such a two-group action. -/
theorem frattini_le_ker [IsAlgClosed E] [FiniteDimensional E V] [IsMulCommutative B]
    (ρ : Representation E B V) (hρ : Function.Injective ρ)
    (horder : (Nat.card B : E)≠0) (hd : Module.finrank E V≤3)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A) (f : A→*MulAut B)
    (he : ∀a:A,Nonempty (Representation.Equiv (ρ.comp (f a).toMonoidHom) ρ) ∨
      Nonempty (Representation.Equiv (ρ.comp (f a).toMonoidHom) ρ.dual)) :
    frattini A≤f.ker := by
  apply Theory.GroupTheory.frattini_le_ker_of_square_image f
  intro a
  obtain ⟨n,hn⟩ := hA a
  exact square_eq_one_of_equiv_or_dual ρ hρ horder hd (f a)
    ⟨n,by rw [← map_pow,hn,map_one]⟩ (he a)

end Representation.ThreeWeightSquare
