module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# The elementary dihedral cubic bound

For the genuine two-conjugate geometry, |VJ/J|=2 gives |V|=2|A|.
The kernel of the specified faithful conjugation action of A is C_A(V)=Z.
The actual fixed space contains Z, so its codimension is at most m(A/Z)+1.
E.2.10(9), using V<X and F*(X)=O₂(X), gives m(A/Z)>0 and hence the bound
2m(A/Z). Cubicity comes from the proved threefold group commutator identity.

The coordinate map is an actual multiplicative equivalence with V. The actor
quotient and fixed subgroup are identified explicitly; no ratio or numerical
module certificate is an input. The ambient application is in the parent.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10 and the dihedral upper-bound branch of
E.2.13(2–3), printed pp.222–225. The lower degree bounds and other quotient
families remain in the full E.2.13 assembly.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] in
lemma card_V_eq_twice_A (_h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    Nat.card V = 2 * Nat.card (A V M g) := by
  have hi := relIndex_ker V (QuotientGroup.mk' (J M))
  rw [QuotientGroup.ker_mk', hcard] at hi
  have hb : (J M).subgroupOf V = (B V M).subgroupOf V := by ext x; simp [B]
  have hc := ((J M).subgroupOf V).card_mul_index
  have he : Nat.card ((J M).subgroupOf V) = Nat.card (B V M) := by
    rw [hb]
    exact Nat.card_congr (subgroupOfEquivOfLe (show B V M ≤ V from inf_le_right)).toEquiv
  rw [he, ← relIndex, hi] at hc
  rw [← hc, A, card_map_of_injective (MulAut.conj g).injective, mul_comm]

variable {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

omit [Finite D] [Finite Q] in
lemma actor_kernel (h : Hypotheses T V M g) (e : V ≃* Q)
    (ρ : Representation (ZMod 2) D (Additive Q)) (hρ : Function.Injective ρ)
    (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) := by
  ext a
  change f a = 1 ↔ (a : X) ∈ Z V g
  rw [← h.A_inf_centralizer_eq_Z]
  constructor
  · intro hf
    refine ⟨a.property, ?_⟩
    intro v hv
    have hh := ha a ⟨v, hv⟩
    rw [hf, map_one] at hh
    simp only [Module.End.one_apply, toMul_ofMul, e.symm_apply_apply] at hh
    exact eq_mul_inv_iff_mul_eq.mp hh
  · rintro ⟨_, hc⟩
    apply hρ
    apply LinearMap.ext
    intro w
    rw [map_one]
    change ρ (f a) w = w
    apply Additive.toMul.injective
    apply e.symm.injective
    apply Subtype.ext
    have hh := ha a (e.symm w.toMul)
    simp only [e.apply_symm_apply, ofMul_toMul] at hh
    rw [hh, ← hc _ (e.symm w.toMul).property, mul_inv_cancel_right]

omit [Finite D] in
lemma actor_elementary (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g)) :
    IsElementaryTwo f.range := by
  let := h.A_elementary
  have he : IsElementaryAbelian 2 f.range := by
    exact IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨?_, he⟩
  intro hz
  have hc : A V M g ≤ centralizer (V : Set X) := by
    intro a ha
    have hf : f ⟨a, ha⟩ = 1 := by
      have : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
      rwa [hz] at this
    have hm : (⟨a, ha⟩ : A V M g) ∈ f.ker := hf
    rw [hk] at hm
    have hzC := h.core_geometry.2.2.trans inf_le_right
    exact center_le_centralizer _ (hzC hm)
  apply h.commutator_V_A_ne_bot hproper hfit
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

omit [Finite D] [Finite Q] in
lemma actor_cubic (h : Hypotheses T V M g) (e : V ≃* Q)
    (ρ : Representation (ZMod 2) D (Additive Q)) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) : IsCubic ρ f.range := by
  have hd (a : A V M g) (v : Additive Q) :
      (e.symm (displacement ρ (f a) v).toMul : X) =
        ⁅(a : X), (e.symm v.toMul : X)⁆ := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply]
    change (e.symm ((ρ (f a) v).toMul / v.toMul) : X) = _
    rw [map_div, div_eq_mul_inv]
    change (e.symm (ρ (f a) v).toMul : X) * (e.symm v.toMul : X)⁻¹ = _
    have hh := ha a (e.symm v.toMul)
    simp only [e.apply_symm_apply, ofMul_toMul] at hh
    rw [hh]
    rfl
  have hm (E : Subgroup X) (a : A V M g) (v : Additive Q)
      (hv : (e.symm v.toMul : X) ∈ E) :
      (e.symm (displacement ρ (f a) v).toMul : X) ∈ ⁅E, A V M g⁆ := by
    rw [hd, commutator_comm]
    exact commutator_mem_commutator a.property hv
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ v
  have hx := hm _ a _ (hm _ b _ (hm V c v (e.symm v.toMul).property))
  rw [h.cubic] at hx
  apply Additive.toMul.injective
  apply e.symm.injective
  apply Subtype.ext
  simpa only [toMul_zero, map_one, Subgroup.coe_one, mem_bot] using hx

lemma actor_fixed_bound (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g))
    (he : IsElementaryTwo f.range)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    fixedCodim ρ f.range ≤ 2 * rank f.range := by
  let := h.elementary
  let := IsElementaryAbelian.of_le (p := 2) (show Z V g ≤ V from inf_le_left)
  let C := fixedSpace ρ f.range
  have hzA : Z V g ≤ A V M g := h.Z_le_B_inf_A.trans inf_le_right
  have hcA : Nat.card (A V M g) = Nat.card (Z V g) * Nat.card f.range := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe hzA).toEquiv] at hc
    exact hc.symm
  have hZfix (z : Z V g) : Additive.ofMul (e ⟨z, z.property.1⟩) ∈ C := by
    intro d
    change ρ (d : D) (Additive.ofMul (e ⟨z, z.property.1⟩)) = _
    obtain ⟨a, heq⟩ := d.property
    rw [← heq]
    apply Additive.toMul.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [ha]
    simp only [toMul_ofMul, e.symm_apply_apply]
    have hz := (h.core_geometry.2.2 z.property).2
    rw [(mem_center_iff.mp hz) a, mul_inv_cancel_right]
  let j : Z V g → C := fun z => ⟨Additive.ofMul (e ⟨z, z.property.1⟩), hZfix z⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : V => (z : X))
      (e.injective (congrArg (fun z : C => z.val.toMul) hxy))
  have hle := Nat.card_le_card_of_injective j hj
  have hQ : Nat.card Q = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by
    rw [Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q))
  have hZ : Nat.card (Z V g) = 2 ^ Module.finrank (ZMod 2) (Additive (Z V g)) := by
    rw [Nat.card_congr (Additive.ofMul : Z V g ≃ Additive (Z V g))]
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Z V g)))
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) C := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C))
  have hv := h.card_V_eq_twice_A hcard
  rw [Nat.card_congr e.toEquiv, hQ, hcA, hZ, he.card_eq_two_pow_rank,
    ← pow_add, ← pow_succ'] at hv
  have hvdim := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hv
  rw [hZ, hC] at hle
  have hzdim := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hdim := fixedCodim_add_finrank ρ f.range
  have hp := he.rank_pos
  change fixedCodim ρ f.range + Module.finrank (ZMod 2) C = _ at hdim
  omega
/-- The dihedral branch of E.2.13: an actual nontrivial cubic actor in the
specified faithful conjugation action, with its exact kernel and fixed quotient. -/
theorem dihedral_cubic_actor (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hc := h.actor_cubic e ρ f ha
  have hb := h.actor_fixed_bound hcard e ρ f hk he ha
  exact ⟨hk, he, hc, hb, (cubicRatio_le_nat_iff ρ 2).mpr ⟨f.range, he, hc, hb⟩⟩

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Group Q]
  [IsElementaryAbelian 2 Q]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- The induced actor is the literal quotient A/Z, via the original actor map. -/
noncomputable def actorQuotientEquiv (h : Hypotheses T V M g)
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g)) :
    letI := h.Z_normal
    (A V M g ⧸ (Z V g).subgroupOf (A V M g)) ≃* f.range := by
  letI := h.Z_normal
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

/-- The rank used in the ratio is the dimension of the actual actor quotient. -/
theorem actor_rank (h : Hypotheses T V M g)
    (f : A V M g →* D) (hk : f.ker = (Z V g).subgroupOf (A V M g)) :
    let := h.A_elementary
    rank f.range = Module.finrank (ZMod 2)
      (Additive (A V M g ⧸ (Z V g).subgroupOf (A V M g))) := by
  let := h.A_elementary
  change Nat.log 2 (Nat.card f.range) = _
  rw [← index_ker, hk]
  exact log_relIndex_eq_quotient_finrank (A V M g) (Z V g)

omit [Finite X] in
/-- Fixed vectors are exactly the original relative centralizer, in the
specified coordinates; no numerical fixed-space certificate is assumed. -/
theorem mem_fixedSpace_actor (_h : Hypotheses T V M g) (e : V ≃* Q)
    (ρ : Representation (ZMod 2) D (Additive Q)) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹) (w : Additive Q) :
    w ∈ fixedSpace ρ f.range ↔ (e.symm w.toMul : X) ∈ centralizer (A V M g : Set X) := by
  have hh (a : A V M g) : (e.symm (ρ (f a) w).toMul : X) =
      (a : X) * (e.symm w.toMul : X) * (a : X)⁻¹ := by
    simpa only [e.apply_symm_apply, ofMul_toMul] using ha a (e.symm w.toMul)
  constructor
  · intro hw a ha
    have he := hw ⟨f ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
    change ρ (f ⟨a, ha⟩) w = w at he
    have he' := hh ⟨a, ha⟩
    rw [he] at he'
    exact (eq_mul_inv_iff_mul_eq.mp he').symm
  · intro hw a
    obtain ⟨b, hb⟩ := a.property
    change ρ (a : D) w = w
    rw [← hb]
    apply Additive.toMul.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [hh, hw b b.property, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
