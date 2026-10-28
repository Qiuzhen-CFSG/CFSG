module

public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.Maschke
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Finite.Perm

/-!
# The faithful elementary-nine by four semidirect product

An elementary abelian group `D` of order four acting faithfully on an
elementary abelian group `E` of order nine, and preserving a subgroup `L`
of order three, has semidirect product isomorphic to `S₃ × S₃`.

Maschke's theorem supplies a `D`-invariant complement `M` to `L`. The given
semidirect product acts on each of the three-element quotients `E/L` and
`E/M` by affine permutations: `(e,d)` sends `xH` to `e ρ(d)(x)H`.
An element trivial on both quotients has trivial translation part because
`L ∩ M = 1`; its actor part is then trivial by faithfulness of `ρ`.
The resulting injection into `Sym(E/L) × Sym(E/M)` is surjective since both
groups have order 36. Numbering the quotients gives the stated equivalence.
This retains the specified action without assuming diagonal coordinates or
independent inversion characters.

This intrinsic recognition result supplies the elementary-nine action step
in Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.3.11(5),
printed p.1124, combined manuscript of 1 March 2004. Its application to the
actual local quotient is separate. Only `|D| = 4` is needed in the proof;
the elementary abelian hypothesis on `D` is retained in the public contract.
-/

open scoped IsMulCommutative Pointwise
namespace ElementaryNineFourSemidirect
variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
  [IsElementaryAbelian 3 E]

omit [Finite E] in
private theorem invariant_complement (ρ : D →* MulAut E) (hD : Nat.card D = 4)
    (L : Subgroup E) (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) :
    ∃ M : Subgroup E, L.IsComplement' M ∧
      ∀ d : D, ∀ x ∈ M, ρ d x ∈ M := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : MulDistribMulAction D E := MulDistribMulAction.compHom E ρ
  let σ := Representation.ofElementaryAbelianAction (A := D) (G := E) (p := 3)
  let U : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule (n := 3) (Subgroup.toAddSubgroup L)
    apply_mem_toSubmodule := fun d x hx => hL d x.toMul hx }
  have hc : Fintype.card D = 4 := by simpa using hD
  let : NeZero (Fintype.card D : ZMod 3) := ⟨by rw [hc]; decide⟩
  obtain ⟨Q, hQ⟩ := MonoidAlgebra.Submodule.exists_isCompl' U.asSubmodule
  let W := Subrepresentation.ofSubmodule' Q
  let M : Subgroup E := W.toSubmodule.toAddSubgroup.toSubgroup'
  have hd : Disjoint L M := Subgroup.disjoint_def.mpr fun {x} hx hm => by
    have hz := Submodule.disjoint_def.mp hQ.disjoint (Additive.ofMul x) hx hm
    exact congrArg Additive.toMul hz
  have hp : (L : Set E) * (M : Set E) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : Additive.ofMul x ∈ U.asSubmodule ⊔ Q := by rw [hQ.sup_eq_top]; trivial
    obtain ⟨u, hu, v, hv, huv⟩ := (Submodule.mem_sup (p := U.asSubmodule) (p' := Q)).mp hx
    exact ⟨u.toMul, hu, v.toMul, hv, congrArg Additive.toMul huv⟩
  refine ⟨M, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd hp, ?_⟩
  intro d x hx
  exact W.apply_mem_toSubmodule d hx

private def quotientAction (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) : D →* MulAut (E ⧸ L) := by
  let f (d : D) : E ⧸ L →* E ⧸ L :=
    QuotientGroup.map L L (ρ d).toMonoidHom (hL d)
  refine {
    toFun := fun d => { f d with
      invFun := f d⁻¹
      left_inv := ?_
      right_inv := ?_ }
    map_one' := ?_
    map_mul' := ?_ }
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ d⁻¹ (ρ d x)) = QuotientGroup.mk x
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ d (ρ d⁻¹ x)) = QuotientGroup.mk x
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  · ext q
    induction q using QuotientGroup.induction_on with
    | H x => change QuotientGroup.mk (ρ 1 x) = QuotientGroup.mk x; simp
  · intro d e
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ (d * e) x) = QuotientGroup.mk (ρ d (ρ e x))
      rw [map_mul, MulAut.mul_apply]

private def affineHom {N A : Type*} [Group N] [Group A] (φ : A →* MulAut N) :
    N ⋊[φ] A →* Equiv.Perm N where
  toFun g := Equiv.mulLeft g.left * (φ g.right).toEquiv
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    change (g.left * φ g.right h.left) * φ (g.right * h.right) x =
      g.left * φ g.right (h.left * φ h.right x)
    simp only [map_mul, MulAut.mul_apply, mul_assoc]

private def affineQuotientHom (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) : E ⋊[ρ] D →* Equiv.Perm (E ⧸ L) :=
  (affineHom (quotientAction ρ L hL)).comp
    (SemidirectProduct.map (QuotientGroup.mk' L) (MonoidHom.id D)
      (fun _ => MonoidHom.ext fun _ => rfl))

omit [Finite E] [Finite D] in
private theorem affineQuotientHom_apply (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) (g : E ⋊[ρ] D) (x : E) :
    affineQuotientHom ρ L hL g (QuotientGroup.mk x) =
      QuotientGroup.mk (g.left * ρ g.right x) := rfl


omit [Finite E] [Finite D] in
private theorem quotient_pair_injective (ρ : D →* MulAut E)
    (hρ : Function.Injective ρ) (L M : Subgroup E) (hd : Disjoint L M)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L)
    (hM : ∀ d : D, ∀ x ∈ M, ρ d x ∈ M) :
    Function.Injective ((affineQuotientHom ρ L hL).prod (affineQuotientHom ρ M hM)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have heL (x : E) : (QuotientGroup.mk (g.left * ρ g.right x) : E ⧸ L) =
      QuotientGroup.mk x := by
    rw [← affineQuotientHom_apply ρ L hL]
    have hh := congrArg (fun z : Equiv.Perm (E ⧸ L) × Equiv.Perm (E ⧸ M) =>
      z.1 (QuotientGroup.mk x)) hg
    exact hh
  have heM (x : E) : (QuotientGroup.mk (g.left * ρ g.right x) : E ⧸ M) =
      QuotientGroup.mk x := by
    rw [← affineQuotientHom_apply ρ M hM]
    exact congrArg (fun z : Equiv.Perm (E ⧸ L) × Equiv.Perm (E ⧸ M) =>
      z.2 (QuotientGroup.mk x)) hg
  have hn : g.left = 1 := Subgroup.disjoint_def.mp hd
    ((QuotientGroup.eq_one_iff _).mp (by simpa using heL 1))
    ((QuotientGroup.eq_one_iff _).mp (by simpa using heM 1))
  have hr : g.right = 1 := by
    apply hρ
    rw [map_one]
    ext x
    change ρ g.right x = x
    apply mul_inv_eq_one.mp
    apply Subgroup.disjoint_def.mp hd
    · apply (QuotientGroup.eq_one_iff _).mp
      have hx := heL x
      simp only [hn, one_mul] at hx
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
    · apply (QuotientGroup.eq_one_iff _).mp
      have hx := heM x
      simp only [hn, one_mul] at hx
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
  exact SemidirectProduct.ext hn hr

/-- A faithful elementary-four action on an elementary-nine group, preserving a cubic
subgroup, identifies the specified semidirect product with `S₃ × S₃`. -/
public theorem nonempty_mulEquiv [IsElementaryAbelian 2 D] (ρ : D →* MulAut E)
    (hE : Nat.card E = 9) (hD : Nat.card D = 4) (hρ : Function.Injective ρ)
    (L : Subgroup E) (hLcard : Nat.card L = 3)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) :
    Nonempty ((E ⋊[ρ] D) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  classical
  obtain ⟨M, hcomp, hM⟩ := invariant_complement ρ hD L hL
  have hMcard : Nat.card M = 3 := by
    have hh := hcomp.card_mul_card
    rw [hE, hLcard] at hh
    omega
  have hQL : Nat.card (E ⧸ L) = 3 := hcomp.symm.index_eq_card.trans hMcard
  have hQM : Nat.card (E ⧸ M) = 3 := hcomp.index_eq_card.trans hLcard
  let f := (affineQuotientHom ρ L hL).prod (affineQuotientHom ρ M hM)
  have hf : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨quotient_pair_injective ρ hρ L M hcomp.disjoint hL hM, ?_⟩
    rw [Nat.card_congr (SemidirectProduct.equivProd : (E ⋊[ρ] D) ≃ E × D),
      Nat.card_prod, hE, hD, Nat.card_prod, Nat.card_perm, Nat.card_perm, hQL, hQM]
    decide
  let eL := Finite.equivFinOfCardEq hQL
  let eM := Finite.equivFinOfCardEq hQM
  exact ⟨(MulEquiv.ofBijective f hf).trans
    (MulEquiv.prodCongr eL.permCongrHom eM.permCongrHom)⟩

end ElementaryNineFourSemidirect
