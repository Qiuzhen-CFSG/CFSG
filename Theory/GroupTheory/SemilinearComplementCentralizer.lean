module
public import Theory.GroupTheory.OddComplementSylowCentralizer
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Transporting a fixed coefficient Sylow to the original odd complement

Suppose a finite group H has normal subgroup L with odd complement E and
embeds into an actual semidirect product X ⋊ A. Its L image is exactly a
specified subgroup D of X, and its E image consists of pure coefficients.
If each odd coefficient subgroup fixes some Sylow two-subgroup of D, and
every such Sylow has a two-group centralizer in D, then E is the actual
ambient odd core of a Sylow centralizer in H.

The given embedding identifies L with D. Project the actual E image to A,
choose the fixed Sylow in D, and transport it back to L. Injectivity of the
embedding turns coefficient fixation into commutation in H. The same
identification embeds its internal centralizer into the model centralizer,
so it is a two-group. The odd-complement centralizer theorem gives the
exact ambient subgroup equality. Cyclicity of E is not required.

This is the common transport step for the linear and unitary alternatives
in ABG II.3 Proposition 3, article pages 27--28. The model-specific fixed
Sylow and centralizer bounds remain explicit inputs supplied by their
independently proved matrix theorems. The action homomorphism is retained.
-/

namespace Subgroup

private theorem linear_equiv {H X A : Type*} [Group H] [Group X] [Group A]
    (α : A →* MulAut X) (L : Subgroup H) (D : Subgroup X)
    (f : H →* X ⋊[α] A) (hf : Function.Injective f)
    (hL : L.map f = D.map SemidirectProduct.inl) :
    ∃ e : L ≃* D, ∀ l : L, SemidirectProduct.inl (e l : X) = f l := by
  let jL := L.equivMapOfInjective f hf
  let jD := D.equivMapOfInjective (SemidirectProduct.inl : X →* X ⋊[α] A)
    SemidirectProduct.inl_injective
  let e := jL.trans ((MulEquiv.subgroupCongr hL).trans jD.symm)
  refine ⟨e, ?_⟩
  intro l
  have he := congrArg Subtype.val (jD.apply_symm_apply ((MulEquiv.subgroupCongr hL) (jL l)))
  simpa only [jD, jL, e, MulEquiv.trans_apply, coe_equivMapOfInjective_apply,
    MulEquiv.subgroupCongr_apply] using he

public theorem exists_oddCore_sylowCentralizer_of_semilinear_model {H X A : Type*} [Group H] [Finite H] [Group X] [Finite X]
    [Group A] [Finite A] (α : A →* MulAut X) (D : Subgroup X)
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (hodd : Odd (Nat.card E)) (f : H →* X ⋊[α] A) (hf : Function.Injective f)
    (hL : L.map f = D.map SemidirectProduct.inl)
    (hE : E.map f ≤ (SemidirectProduct.inr : A →* X ⋊[α] A).range)
    (hfixed : ∀ B : Subgroup A, Odd (Nat.card B) → ∃ T : Sylow 2 D,
      ∀ (b : B) (t : T), α b.val t.val.val = t.val.val)
    (hcent : ∀ T : Sylow 2 D, IsPGroup 2 (centralizer (T : Set D))) :
    ∃ S : Sylow 2 L,
      E = (pPrimeCore 2 (centralizer (((S : Subgroup L).map L.subtype) : Set H))).map
        (centralizer (((S : Subgroup L).map L.subtype) : Set H)).subtype := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL, heL⟩ := linear_equiv α L D f hf hL
  let π : H →* A := SemidirectProduct.rightHom.comp f
  let B := E.map π
  have hB : Odd (Nat.card B) := Nat.coprime_two_left.mp
    ((Nat.coprime_two_left.mpr hodd).of_dvd_right (E.card_map_dvd π))
  obtain ⟨T, hT⟩ := hfixed B hB
  let S := T.mapSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hST (s : S) : eL s.val ∈ (T : Subgroup D) := by
    have hs : s.val ∈ (T : Subgroup D).map eL.symm.toMonoidHom := s.property
    obtain ⟨t, ht, he⟩ := hs
    change eL.symm t = s.val at he
    rw [← he, eL.apply_symm_apply]
    exact ht
  have hTS (t : T) : eL.symm t.val ∈ (S : Subgroup L) := by
    change eL.symm t.val ∈ (T : Subgroup D).map eL.symm.toMonoidHom
    exact mem_map_of_mem _ t.property
  have hEC : E ≤ centralizer (((S : Subgroup L).map L.subtype) : Set H) := by
    intro a ha
    obtain ⟨b, hb⟩ := hE (mem_map_of_mem f ha)
    have hπ : π a = b := by
      change SemidirectProduct.rightHom (f a) = b
      rw [← hb, SemidirectProduct.rightHom_inr]
    have hbB : b ∈ B := hπ ▸ mem_map_of_mem π ha
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    apply hf
    rw [map_mul, map_mul]
    change f (s : H) * f a = f a * f (s : H)
    rw [← heL s, ← hb]
    have hfix := hT ⟨b, hbB⟩ ⟨eL s, hST ⟨s, hs⟩⟩
    ext <;> simp [hfix]
  have hCmap : ∀ c : centralizer (S : Set L),
      eL c.val ∈ centralizer (T : Set D) := by
    intro c
    rw [mem_centralizer_iff]
    intro t ht
    have hcomm := mem_centralizer_iff.mp c.property (eL.symm t) (hTS ⟨t, ht⟩)
    simpa only [map_mul, eL.apply_symm_apply] using congrArg eL hcomm
  let j : centralizer (S : Set L) →* centralizer (T : Set D) :=
    (eL.toMonoidHom.comp (centralizer (S : Set L)).subtype).codRestrict _ hCmap
  have hj : Function.Injective j := by
    intro c d h
    exact Subtype.ext (eL.injective (congrArg Subtype.val h))
  exact ⟨S, oddComplement_eq_oddCore_sylowCentralizer L E hcomp hodd S hEC
    ((hcent T).of_injective j hj)⟩


end Subgroup

