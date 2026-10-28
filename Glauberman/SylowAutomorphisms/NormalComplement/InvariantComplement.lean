module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Sylow-invariant complements

A projection onto an invariant subspace, commuting with a subgroup P, can
be averaged over the left cosets of P. When the index is invertible, its
average is an equivariant retraction. Its kernel gives a complement invariant
under the whole actor, even when the actor order is divisible by the
characteristic. In particular a Sylow p-invariant complement in an elementary
abelian p-group extends to a whole-actor-invariant complement.

The application identifies an existing complement with the displacement of
an actor that fixes the other summand. It consequently makes that existing
complement invariant under the whole group. The last theorem transports the
argument to actual conjugation on subgroups of a finite ambient group.

Source: Glauberman, “On the automorphism group of a finite group having no
non-identity normal subgroups of odd order”, Math. Z. 93 (1966), Lemma 4,
p.157, and its application in Theorem 1(b), p.158; DOI 10.1007/BF01111033.
-/

public section

open scoped BigOperators IsMulCommutative

namespace Glauberman.SylowAutomorphisms.NormalComplement

variable {k J V : Type*} [Field k] [Group J] [Finite J]
  [AddCommGroup V] [Module k V]

/-- Average the projection over cosets of a subgroup with invertible index.
Only the original complement has to be invariant under this subgroup. -/
theorem exists_invariant_complement_of_index
    (ρ : Representation k J V) (W : Subrepresentation ρ)
    (P : Subgroup J) (hindex : (P.index : k) ≠ 0)
    (U : Submodule k V) (hcompl : IsCompl W.toSubmodule U)
    (hU : ∀ g ∈ P, ∀ v ∈ U, ρ g v ∈ U) :
    ∃ U₀ : Submodule k V, IsCompl W.toSubmodule U₀ ∧
      ∀ g : J, ∀ v ∈ U₀, ρ g v ∈ U₀ := by
  classical
  let π : V →ₗ[k] W.toSubmodule := W.toSubmodule.projectionOnto U hcompl
  let σ := ρ.linHom W.toRepresentation
  have hπ (g : J) (hg : g ∈ P) (v : V) :
      π (ρ g v) = W.toRepresentation g (π v) := by
    obtain ⟨w, u, hwu, _⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
    rw [← hwu, map_add, map_add, map_add]
    have hleft : π (ρ g w) = W.toRepresentation g w :=
      Submodule.projectionOnto_apply_of_mem_left hcompl (W.apply_mem_toSubmodule g w.property)
    have hright : π (ρ g u) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hcompl (hU g hg u u.property)
    simp only [hleft, hright, π, Submodule.projectionOnto_apply_left,
      Submodule.projectionOnto_apply_right, add_zero]
  have hfixed (g : J) (hg : g ∈ P) : σ g π = π := by
    apply LinearMap.ext
    intro v
    change W.toRepresentation g (π (ρ g⁻¹ v)) = π v
    rw [hπ g⁻¹ (P.inv_mem hg)]
    change (W.toRepresentation g * W.toRepresentation g⁻¹) (π v) = π v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  let : Fintype (J ⧸ P) := Fintype.ofFinite _
  let f : J ⧸ P → (V →ₗ[k] W.toSubmodule) :=
    Quotient.lift (fun g => σ g π) (by
      intro a b hab
      have hs : a⁻¹ * b ∈ P := QuotientGroup.leftRel_apply.mp hab
      calc
        σ a π = σ a (σ (a⁻¹ * b) π) := congrArg (σ a) (hfixed _ hs).symm
        _ = σ b π := by simp [← Module.End.mul_apply, ← map_mul])
  have hf (g : J) (q : J ⧸ P) : σ g (f q) = f (g • q) := by
    induction q using Quotient.inductionOn with
    | h a => exact (congrArg (fun t : Module.End k (V →ₗ[k] W.toSubmodule) => t π)
        (σ.map_mul g a)).symm
  let π₀ : V →ₗ[k] W.toSubmodule := (P.index : k)⁻¹ • ∑ q, f q
  have hπ₀ (g : J) : σ g π₀ = π₀ := by
    simp only [π₀, map_smul, map_sum, hf]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm g) f
  have hret (q : J ⧸ P) (w : W.toSubmodule) : f q w = w := by
    induction q using Quotient.inductionOn with
    | h g =>
      change W.toRepresentation g (π (ρ g⁻¹ w)) = w
      rw [show π (ρ g⁻¹ w) = W.toRepresentation g⁻¹ w from
        Submodule.projectionOnto_apply_of_mem_left hcompl
          (W.apply_mem_toSubmodule g⁻¹ w.property)]
      change (W.toRepresentation g * W.toRepresentation g⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
  have hret₀ (w : W.toSubmodule) : π₀ w = w := by
    simp only [π₀, LinearMap.smul_apply, LinearMap.sum_apply, hret,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k]
    have hc : Fintype.card (J ⧸ P) = P.index := (Nat.card_eq_fintype_card).symm
    rw [hc, smul_smul, inv_mul_cancel₀ hindex, one_smul]
  refine ⟨π₀.ker, LinearMap.isCompl_of_proj hret₀, ?_⟩
  intro g v hv
  change π₀ (ρ g v) = 0
  have he := LinearMap.congr_fun (hπ₀ g) (ρ g v)
  change W.toRepresentation g (π₀ (ρ g⁻¹ (ρ g v))) = π₀ (ρ g v) at he
  have hi : ρ g⁻¹ (ρ g v) = v := by
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hi, show π₀ v = 0 from hv, map_zero] at he
  exact he.symm

/-- Glauberman's Lemma 4: extend a Sylow-invariant complement to a complement
invariant under the full finite actor. No coprimality of the actor order is used. -/
theorem exists_invariant_complement_of_sylow
    {p : ℕ} [Fact p.Prime] {A E : Type*} [Group A] [Finite A] [Group E]
    [IsElementaryAbelian p E]
    (ρ : A →* MulAut E) (P : Sylow p A)
    (W U : Subgroup E) (hW : ∀ a : A, ∀ x ∈ W, ρ a x ∈ W)
    (hcompl : IsCompl W U)
    (hU : ∀ a ∈ P, ∀ x ∈ U, ρ a x ∈ U) :
    ∃ U₀ : Subgroup E, IsCompl W U₀ ∧ ∀ a : A, ∀ x ∈ U₀, ρ a x ∈ U₀ := by
  let σ : Representation (ZMod p) A (Additive E) :=
    { toFun := fun a => (ρ a).toMonoidHom.toAdditive.toZModLinearMap p
      map_one' := by ext x; exact congrArg (fun f : MulAut E => f x.toMul) ρ.map_one
      map_mul' := by intro a b; ext x
                     exact congrArg (fun f : MulAut E => f x.toMul) (ρ.map_mul a b) }
  let e : Subgroup E ≃o Submodule (ZMod p) (Additive E) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)
  let M : Subrepresentation σ := ⟨e W, hW⟩
  have hi : ((P : Subgroup A).index : ZMod p) ≠ 0 := by
    intro hz
    exact P.not_dvd_index ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  obtain ⟨N, hMN, hN⟩ := exists_invariant_complement_of_index σ M P hi (e U)
    (e.isCompl_iff.mp hcompl) hU
  refine ⟨e.symm N, ?_, ?_⟩
  · apply e.isCompl_iff.mpr
    simpa using hMN
  · exact hN

/-- If x fixes W and its displacement covers a Sylow-invariant complement U,
then U is invariant under the whole actor. This is the use of Lemma 4 in 1(b). -/
theorem invariant_of_surjective_displacement
    {p : ℕ} [Fact p.Prime] {A E : Type*} [Group A] [Finite A] [Group E]
    [IsElementaryAbelian p E]
    (ρ : A →* MulAut E) (P : Sylow p A)
    (W U : Subgroup E) (hW : ∀ a : A, ∀ x ∈ W, ρ a x ∈ W)
    (hcompl : IsCompl W U)
    (hU : ∀ a ∈ P, ∀ x ∈ U, ρ a x ∈ U)
    (x : A) (hxW : ∀ w ∈ W, ρ x w = w)
    (hmove : ∀ u ∈ U, ∃ v : E, ρ x v * v⁻¹ = u) :
    ∀ a : A, ∀ u ∈ U, ρ a u ∈ U := by
  obtain ⟨U₀, hc₀, hU₀⟩ := exists_invariant_complement_of_sylow ρ P W U hW hcompl hU
  have hle : U ≤ U₀ := by
    intro u hu
    obtain ⟨v, rfl⟩ := hmove u hu
    have hv : v ∈ W ⊔ U₀ := by rw [hc₀.sup_eq_top]; trivial
    obtain ⟨w, hw, v₀, hv₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
    have he : ρ x (w * v₀) * (w * v₀)⁻¹ = ρ x v₀ * v₀⁻¹ := by
      rw [map_mul, hxW w hw, mul_inv_rev]
      simp only [mul_assoc, mul_left_comm w, mul_inv_cancel, mul_one]
    rw [he]
    exact U₀.mul_mem (hU₀ x v₀ hv₀) (U₀.inv_mem hv₀)
  have he : U = U₀ :=
    (le_iff_eq_of_codisjoint_of_disjoint hcompl.symm.codisjoint hc₀.disjoint).mp hle
  simpa only [he] using hU₀

/-- The displacement argument for literal conjugation inside an ambient group.
The complement is taken inside V, and the resulting normality is relative to J. -/
theorem normalizes_of_surjective_displacement
    {p : ℕ} [Fact p.Prime] {K : Type*} [Group K] [Finite K]
    (J V W U : Subgroup K) [IsElementaryAbelian p V]
    (hJV : J ≤ Subgroup.normalizer (V : Set K))
    (hJW : J ≤ Subgroup.normalizer (W : Set K))
    (hUV : U ≤ V)
    (hcompl : IsCompl (W.subgroupOf V) (U.subgroupOf V))
    (P : Sylow p J)
    (hPU : ∀ a : J, a ∈ P → (a : K) ∈ Subgroup.normalizer (U : Set K))
    (x : J) (hxW : (x : K) ∈ Subgroup.centralizer (W : Set K))
    (hmove : ∀ u ∈ U, ∃ v ∈ V, (x : K) * v * (x : K)⁻¹ * v⁻¹ = u) :
    J ≤ Subgroup.normalizer (U : Set K) := by
  let ρ : J →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hJV)
  have hW : ∀ a : J, ∀ v ∈ W.subgroupOf V, ρ a v ∈ W.subgroupOf V := by
    intro a v hv
    exact (Subgroup.mem_normalizer_iff.mp (hJW a.property) (v : K)).mp hv
  have hU : ∀ a ∈ P, ∀ v ∈ U.subgroupOf V, ρ a v ∈ U.subgroupOf V := by
    intro a ha v hv
    exact (Subgroup.mem_normalizer_iff.mp (hPU a ha) (v : K)).mp hv
  have hx : ∀ w ∈ W.subgroupOf V, ρ x w = w := by
    intro w hw
    apply Subtype.ext
    change (x : K) * (w : K) * (x : K)⁻¹ = (w : K)
    rw [← Subgroup.mem_centralizer_iff.mp hxW (w : K) hw, mul_inv_cancel_right]
  have hm : ∀ u ∈ U.subgroupOf V, ∃ v : V, ρ x v * v⁻¹ = u := by
    intro u hu
    obtain ⟨v, hv, he⟩ := hmove (u : K) hu
    exact ⟨⟨v, hv⟩, Subtype.ext he⟩
  have hi := invariant_of_surjective_displacement ρ P (W.subgroupOf V)
    (U.subgroupOf V) hW hcompl hU x hx hm
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact hi ⟨a, ha⟩ ⟨u, hUV hu⟩ hu
  · intro hu
    have he := hi ⟨a⁻¹, J.inv_mem ha⟩ ⟨a * u * a⁻¹, hUV hu⟩ hu
    change a⁻¹ * (a * u * a⁻¹) * (a⁻¹)⁻¹ ∈ U at he
    simpa [mul_assoc] using he

end Glauberman.SylowAutomorphisms.NormalComplement
