module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Consumer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Centralizer

/-!
# The actual outer Sylow coset

The marked V-actor lies in K* because it preserves the first constituent.
Its nonzero pure natural displacement is fixed by C_H(V), using [U,V] ≤ V.
Hence C_H(V) has inner image. The source index-two subgroup U C_T(V) is
therefore precisely the inner preimage in T: the Sylow image cannot lie
inside the index-two K*. This proves the swap for every source outer t.
Source: Aschbacher–Smith 15.3.51 and 15.3.58(3), printed pp.1146,1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

namespace NaturalPair
variable (p : NaturalPair d a)

/-- The marked involution is in the recognized normal actor. -/
theorem marked_mem_K : v ∈ p.K :=
  (p.actorRecognition.stabilizer v).mp p.pair.first_invariant

/-- Coordinates of a pure natural vector, on the original quotient. -/
noncomputable def pureNatural (x : BinaryLinearThree.Vector) : VectorQuotient Z ZS :=
  p.coordinates.symm (Multiplicative.ofAdd (x, 0))

/-- The actual V displacement contains a nonzero pure natural vector. -/
theorem exists_pureNatural_displacement :
    ∃ x : BinaryLinearThree.Vector, x ≠ 0 ∧
      p.pureNatural x ∈ Fusion.Core.ResidualGeneration.vectorDisplacement Z ZS V := by
  have hvne : v ≠ 1 := by
    intro he
    have hc := d.Vstar_card
    rw [← d.marking, he, zpowers_one_eq_bot] at hc
    simp at hc
  have hvV : v ∈ actorImage Z V := d.marking ▸ mem_zpowers v
  obtain ⟨vh, hvhV, hmark⟩ := hvV
  let k : p.K := ⟨v, p.marked_mem_K⟩
  let g := Matrix.PSL3Two.equiv.symm (p.first_model.actor k)
  have hgone : g ≠ 1 := by
    intro he
    have hk : k = 1 := (p.first_model.actor.trans Matrix.PSL3Two.equiv.symm).injective
      (he.trans (map_one _).symm)
    exact hvne (congrArg Subtype.val hk)
  have hm : ∃ x : BinaryLinearThree.Vector, BinaryLinearThree.W g x ≠ x := by
    by_contra hn
    push Not at hn
    apply hgone
    apply BinaryLinearThree.natural_injective
    apply LinearMap.ext
    intro x
    simpa only [map_one, Module.End.one_apply] using hn x
  obtain ⟨x, hx⟩ := hm
  refine ⟨BinaryLinearThree.W g x - x, sub_ne_zero.mpr hx, ?_⟩
  have he : quotientAction Z ZS vh (p.pureNatural x) * (p.pureNatural x)⁻¹ =
      p.pureNatural (BinaryLinearThree.W g x - x) := by
    apply p.coordinates.injective
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [p.coordinates_equivariant vh k hmark]
    simp only [pureNatural, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      map_zero, Prod.mk_sub_mk, sub_self]
    rfl
  exact he ▸ Fusion.Core.ResidualGeneration.quotient_displacement_mem vh hvhV _

/-- Pointwise centralization of V precludes exchanging the two constituents. -/
theorem centralizer_mem_K (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (h : centralizerH Z) (hh : (h : G) ∈ centralizer (V : Set G)) :
    QuotientGroup.mk' (pCore 2 (centralizerH Z)) h ∈ p.K := by
  obtain ⟨x, hx, hxd⟩ := p.exists_pureNatural_displacement
  by_contra hout
  have he := congrArg (fun w : VectorQuotient Z ZS => (p.coordinates w).toAdd.1)
    (Fusion.Core.ResidualGeneration.vectorDisplacement_fixed h hh hcomm _ hxd)
  have hs := (p.outer_swaps (QuotientGroup.mk' _ h) hout).1 x
  change (p.coordinates (quotientAction Z ZS h (p.pureNatural x))).toAdd.1 = 0 at hs
  rw [hs] at he
  apply hx
  simpa only [pureNatural, MulEquiv.apply_symm_apply, toAdd_ofAdd] using he.symm

/-- The Sylow image is not contained in the normal index-two actor. -/
theorem actorSylow_not_le_K : ¬ (d.actorSylow : Subgroup (ActorQuotient Z)) ≤ p.K := by
  intro hle
  have hindex : p.K.index = 2 := by
    rw [← index_map_equiv p.K p.actorEquiv]
    change (p.K.map p.actorEquiv.toMonoidHom).index = 2
    rw [p.actorEquiv_K]
    exact SplitBranch.psl_inner_index
  have hdvd := index_dvd_of_le hle
  rw [hindex] at hdvd
  exact d.actorSylow.not_dvd_index hdvd

/-- Every element outside the source index-two subgroup has outer actor. -/
theorem outside_mem_outer
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hUT : closureU Z ZS ≤ (d.T : Subgroup G))
    (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (hindex : (closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))).relIndex
      (d.T : Subgroup G) = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hout : t ∉ closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))) :
    QuotientGroup.mk' (pCore 2 (centralizerH Z)) ⟨t, d.T_le_H ht⟩ ∉ p.K := by
  let B := closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))
  let A : Subgroup G :=
    ((p.K.comap (QuotientGroup.mk' (pCore 2 (centralizerH Z)))).map (centralizerH Z).subtype) ⊓
      (d.T : Subgroup G)
  have hBA : B ≤ A := by
    apply sup_le
    · intro x hx
      refine ⟨?_, hUT hx⟩
      let xh : centralizerH Z := ⟨x, d.T_le_H (hUT hx)⟩
      refine ⟨xh, ?_, rfl⟩
      change QuotientGroup.mk' _ xh ∈ p.K
      have he : QuotientGroup.mk' (pCore 2 (centralizerH Z)) xh = 1 :=
        (Fusion.Core.ResidualGeneration.actorProjection_eq_one_iff Z xh).mpr (hUQ hx)
      rw [he]
      exact p.K.one_mem
    · intro x hx
      exact ⟨⟨⟨x, d.T_le_H hx.1⟩, p.centralizer_mem_K hcomm _ hx.2, rfl⟩, hx.1⟩
  have hAT : A ≤ (d.T : Subgroup G) := inf_le_right
  have hTA : ¬ (d.T : Subgroup G) ≤ A := by
    intro hle
    apply p.actorSylow_not_le_K
    rw [d.actorSylow_coe]
    rintro x ⟨h, hh, rfl⟩
    obtain ⟨k, hk, he⟩ := (hle hh).1
    have hek : k = h := Subtype.ext he
    exact hek ▸ hk
  have hmul := relIndex_mul_relIndex B A (d.T : Subgroup G) hBA hAT
  change B.relIndex (d.T : Subgroup G) = 2 at hindex
  rw [hindex] at hmul
  have hdvd : A.relIndex (d.T : Subgroup G) ∣ 2 :=
    ⟨B.relIndex A, by simpa only [mul_comm] using hmul.symm⟩
  have hA2 : A.relIndex (d.T : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left
      (fun he => hTA (relIndex_eq_one.mp he))
  rw [hA2] at hmul
  have hAB : A ≤ B := relIndex_eq_one.mp (by omega : B.relIndex A = 1)
  intro htin
  exact hout (hAB ⟨⟨⟨t, d.T_le_H ht⟩, htin, rfl⟩, ht⟩)

/-- The literal action record for any source choice of outer t. -/
noncomputable def sourceRecognizedAction
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hUT : closureU Z ZS ≤ (d.T : Subgroup G))
    (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (hindex : (closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))).relIndex
      (d.T : Subgroup G) = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hout : t ∉ closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))) :
    Fusion.Core.ResidualGeneration.RecognizedAction (d.T : Subgroup G) Z ZS V t :=
  p.recognizedAction t ht (d.T_le_H ht) hout
    (p.outside_mem_outer hUQ hUT hcomm hindex t ht hout)

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
