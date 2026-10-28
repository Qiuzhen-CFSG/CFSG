module

public import Theory.GroupAction.BinaryFixedLineQuotient
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupAction.FixedLineIndecomposability
public import Mathlib.Data.Fintype.Perm
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The actual E₁₆ quotient actor in the Aut(M₁₂) branch

Let D be the larger local group Mc, Q = O₂(D) an elementary abelian group
of order sixteen, and Z a normal subgroup of order two contained in Q.
The source centralizer chain in D/Z makes literal conjugation on Q faithful
modulo Q. Normality and order two make every actor fix Z pointwise. On Q/Z,
the fixed-line kernel is a two-group, so O₂(D/Q) = 1 makes this action faithful.
The quotient Q/Z has order eight, hence its full automorphism group is GL₃(2),
of order 168. The actual image of H/Q has order 24 and is proper by strict
residual enlargement; its index is therefore seven. The action fills GL₃(2),
which the checked linear model identifies with PSL₃(2).

The whole-overlap Sylow subgroup is transported explicitly. Its containment
is not needed for recognition once the faithful rank-three action is known.
Finally Q ∩ C_D(QK) = Z, for the specified two-subgroup QK, obstructs any
nontrivial invariant direct decomposition. This is transported to D/Q and to
the binary vector space associated with the actual Q, including E₁₆ coordinates.

All base-model facts remain explicit inputs for the source assembly owner.
No action, faithfulness, rank-three embedding, or recognition is assumed.
Source: Aschbacher–Smith, proof of Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.E16Actor
variable {D : Type*} [Group D] (Q Z : Subgroup D) [Q.Normal]
  [IsElementaryAbelian 2 Q]

private theorem core_le_conj_ker : Q ≤ (MulAut.conjNormal : D →* MulAut Q).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change x * (q : D) * x⁻¹ = q
  have hc := congrArg Q.subtype (mul_comm (⟨x, hx⟩ : Q) q)
  change x * (q : D) = (q : D) * x at hc
  rw [hc, mul_inv_cancel_right]

/-- Literal conjugation on the abelian core, descended through its own quotient. -/
public def conjugation : D ⧸ Q →* MulAut Q :=
  QuotientGroup.lift Q MulAut.conjNormal (core_le_conj_ker Q)

/-- Evaluation on a representative is conjugation by that actual element of D. -/
public theorem conjugation_apply (d : D) (q : Q) :
    ((conjugation Q) (QuotientGroup.mk' Q d) q : D) = d * (q : D) * d⁻¹ := by
  unfold conjugation
  rfl

/-- The centralizer chain in D/Z identifies the conjugation kernel with Q. -/
public theorem conjugation_injective [Z.Normal] (hZQ : Z ≤ Q)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : Function.Injective (conjugation Q) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  apply le_antisymm (core_le_conj_ker Q)
  intro x hx
  have hxc : x ∈ centralizer (Q : Set D) := by
    intro q hq
    have he := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : D))
      (MonoidHom.mem_ker.mp hx)
    change x * q * x⁻¹ = q at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hm : (QuotientGroup.mk' Z) x ∈ Q.map (QuotientGroup.mk' Z) := by
    apply hchain
    rintro y ⟨q, hq, rfl⟩
    simpa only [← map_mul] using congrArg (QuotientGroup.mk' Z) (hxc q hq)
  have hm' : x ∈ (Q.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) := hm
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hZQ] at hm'

/-- Every quotient actor fixes each element of the normal subgroup of order two. -/
public theorem conjugation_fixes_line [Z.Normal] (hZ : Nat.card Z = 2)
    (a : D ⧸ Q) (x : Q) (hx : x ∈ Z.subgroupOf Q) : conjugation Q a x = x := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Q a
  have hf (z : Z) : (MulAut.conjNormal d : MulAut Z) z = z := by
    by_cases hz : z = 1
    · simp [hz]
    · apply ((Nat.card_eq_two_iff' (1 : Z)).mp hZ).unique
      · exact fun he => hz ((MulAut.conjNormal d : MulAut Z).injective (he.trans (map_one _).symm))
      · exact hz
  apply Subtype.ext
  exact congrArg Z.subtype (hf ⟨x, hx⟩)

omit [IsElementaryAbelian 2 Q] in
/-- Factoring out the actual two-core leaves trivial two-core. -/
public theorem quotient_core_eq_bot (hQ : Q = pCore 2 D) : pCore 2 (D ⧸ Q) = ⊥ := by
  let π := QuotientGroup.mk' Q
  have hk : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk', hQ]
    exact pCore_isPGroup
  have hpre : (pCore 2 (D ⧸ Q)).comap π ≤ Q := by
    calc
      _ ≤ pCore 2 D := le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_ker_isPGroup π hk⟩
      _ = Q := hQ.symm
  apply bot_unique
  intro x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff d).mpr (hpre hx)

/-- The literal quotient of the overlap is its image in the actual actor. -/
public noncomputable def overlapQuotientEquiv (H : Subgroup D) :
    (H ⧸ Q.subgroupOf H) ≃* H.map (QuotientGroup.mk' Q) := by
  let f := (QuotientGroup.mk' Q).subgroupMap H
  have hk : f.ker = Q.subgroupOf H := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' Q).subgroupMap_surjective H))

omit [IsElementaryAbelian 2 Q] in
/-- The overlap equivalence retains the literal quotient map. -/
public theorem overlapQuotientEquiv_apply (H : Subgroup D) (h : H) :
    (overlapQuotientEquiv Q H (QuotientGroup.mk' (Q.subgroupOf H) h) : D ⧸ Q) =
      QuotientGroup.mk' Q (h : D) := by
  unfold overlapQuotientEquiv
  rfl

omit [Q.Normal] [IsElementaryAbelian 2 Q] in
/-- The actual quotient Q/Z has eight elements. -/
public theorem quotient_line_card [Finite D] (hQ : Nat.card Q = 16)
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) : Nat.card (Q ⧸ Z.subgroupOf Q) = 8 := by
  have hL : Nat.card (Z.subgroupOf Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv).trans hZ
  have hh := (Z.subgroupOf Q).card_mul_index
  rw [hL, hQ, Subgroup.index_eq_card] at hh
  omega

/-- The actual actor acts on the actual quotient Q/Z. -/
public def quotientLineAction [Z.Normal] (hZ : Nat.card Z = 2) :
    D ⧸ Q →* MulAut (Q ⧸ Z.subgroupOf Q) :=
  BinaryFixedLine.quotientAction (conjugation Q) (Z.subgroupOf Q)
    (conjugation_fixes_line Q Z hZ)

/-- The action on Q/Z is induced by literal conjugation in D. -/
public theorem quotientLineAction_apply [Z.Normal] (hZ : Nat.card Z = 2)
    (d : D) (q : Q) :
    quotientLineAction Q Z hZ (QuotientGroup.mk' Q d)
        (QuotientGroup.mk' (Z.subgroupOf Q) q) =
      QuotientGroup.mk' (Z.subgroupOf Q) (MulAut.conjNormal d q) := by
  unfold quotientLineAction conjugation
  rfl

/-- The fixed-line two-group kernel vanishes in the two-core quotient. -/
public theorem quotientLineAction_injective [Z.Normal] (hZ : Nat.card Z = 2)
    (hZQ : Z ≤ Q) (hQ : Q = pCore 2 D)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) :
    Function.Injective (quotientLineAction Q Z hZ) :=
  BinaryFixedLine.quotientAction_injective (conjugation Q)
    (conjugation_injective Q Z hZQ hchain) (Z.subgroupOf Q)
    (conjugation_fixes_line Q Z hZ) (quotient_core_eq_bot Q hQ)

private theorem surjective_of_proper_twenty_four
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (hB : Nat.card B = 168)
    (S : Subgroup A) (hS : Nat.card S = 24) (hne : S ≠ ⊤) :
    Function.Surjective f := by
  have hScard : Nat.card (S.map f) = 24 :=
    (Subgroup.card_map_of_injective hf).trans hS
  have hSi : (S.map f).index = 7 := by
    have h := (S.map f).card_mul_index
    rw [hScard, hB] at h
    omega
  have hdiv : f.range.index ∣ 7 := hSi ▸ Subgroup.index_dvd_of_le (S.map_le_range f)
  rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hdiv with hi | hi
  · exact MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp hi)
  · have hr : Nat.card f.range = 24 := by
      have h := f.range.card_mul_index
      rw [hi, hB] at h
      omega
    have he : S.map f = f.range :=
      Subgroup.eq_of_le_of_card_ge (S.map_le_range f) (by omega)
    apply False.elim
    apply hne
    apply Subgroup.map_injective hf
    exact he.trans f.range_eq_map

/-- The proper S₄ image forces the action to fill Aut(Q/Z). -/
public theorem quotientLineAction_bijective [Finite D] [Z.Normal]
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) (hQ : Q = pCore 2 D)
    (hQcard : Nat.card Q = 16)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (H : Subgroup D) (hQH : Q ≤ H)
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 D) :
    Function.Bijective (quotientLineAction Q Z hZ) := by
  have hE := quotient_line_card Q Z hQcard hZ hZQ
  have hi := quotientLineAction_injective Q Z hZ hZQ hQ hchain
  refine ⟨hi, surjective_of_proper_twenty_four _ hi
    (card_mulAut_of_elementary_eight _ hE) (H.map (QuotientGroup.mk' Q)) ?_ ?_⟩
  · rw [← Nat.card_congr (overlapQuotientEquiv Q H).toEquiv,
      Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  · intro he
    apply Subgroup.ne_top_of_map_pResidual_lt 2 H hstrict
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' Q)) he
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hQH,
      Subgroup.comap_top] at hh

/-- Recognize the actual actor by its quotient action and the checked GL₃(2) model. -/
public noncomputable def quotientEquivPSL [Finite D] [Z.Normal]
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) (hQ : Q = pCore 2 D)
    (hQcard : Nat.card Q = 16)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (H : Subgroup D) (hQH : Q ≤ H)
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 D) :
    (D ⧸ Q) ≃* Matrix.PSL3Two.PSL :=
  (MulEquiv.ofBijective (quotientLineAction Q Z hZ)
    (quotientLineAction_bijective Q Z hZ hZQ hQ hQcard hchain H hQH eH hstrict)).trans
    ((elementaryEight_mulAut_equiv_GL (Q ⧸ Z.subgroupOf Q)
      (quotient_line_card Q Z hQcard hZ hZQ)).some.trans
        (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv))

/-- The actual actor and overlap image have orders 168 and 24, and index seven. -/
public theorem actor_card_and_overlap_index [Finite D] [Z.Normal]
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) (hQ : Q = pCore 2 D)
    (hQcard : Nat.card Q = 16)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (H : Subgroup D) (hQH : Q ≤ H)
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 D) :
    Nat.card (D ⧸ Q) = 168 ∧ Nat.card (H.map (QuotientGroup.mk' Q)) = 24 ∧
      (H.map (QuotientGroup.mk' Q)).index = 7 ∧ H.index = 7 := by
  have hD : Nat.card (D ⧸ Q) = 168 :=
    (Nat.card_congr (quotientEquivPSL Q Z hZ hZQ hQ hQcard hchain H hQH eH hstrict).toEquiv).trans
      Matrix.PSL3Two.card_PSL
  have hH : Nat.card (H.map (QuotientGroup.mk' Q)) = 24 := by
    rw [← Nat.card_congr (overlapQuotientEquiv Q H).toEquiv,
      Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  have hi : (H.map (QuotientGroup.mk' Q)).index = 7 := by
    have hh := (H.map (QuotientGroup.mk' Q)).card_mul_index
    rw [hH, hD] at hh
    omega
  refine ⟨hD, hH, hi, ?_⟩
  rwa [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective Q)
    (by simpa only [QuotientGroup.ker_mk'] using hQH)] at hi

/-- Choose the actual nonidentity generator of Z inside Q; every actor fixes it. -/
public theorem exists_fixed_generator [Z.Normal] (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) :
    ∃ z : Q, (z : D) ∈ Z ∧ z ≠ 1 ∧ Subgroup.zpowers z = Z.subgroupOf Q ∧
      ∀ a : D ⧸ Q, conjugation Q a z = z := by
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let zQ : Q := ⟨z, hZQ z.property⟩
  have hzQ : zQ ≠ 1 := by
    intro hh
    apply hz
    apply Subtype.ext
    exact congrArg Q.subtype hh
  refine ⟨zQ, z.property, hzQ, ?_, fun a => conjugation_fixes_line Q Z hZ a zQ z.property⟩
  apply le_antisymm (Subgroup.zpowers_le.mpr (show zQ ∈ Z.subgroupOf Q from z.property))
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ Subgroup.one_mem _
  · have he : (⟨(x : D), hx⟩ : Z) = z :=
      hu _ (fun hh => hx1 (Subtype.ext (congrArg Z.subtype hh)))
    have hex : x = zQ := Subtype.ext (congrArg Z.subtype he)
    rw [hex]
    exact Subgroup.mem_zpowers _

/-- The centralizer equality obstructs invariant decompositions for D/Q. -/
public theorem disjoint_invariant [Finite D] (QK : Subgroup D)
    (hQK : IsPGroup 2 QK) (hZ : Nat.card Z = 2)
    (hcentral : Q ⊓ centralizer (QK : Set D) = Z)
    (U V : Subgroup Q)
    (hU : ∀ a : D ⧸ Q, ∀ u ∈ U, conjugation Q a u ∈ U)
    (hV : ∀ a : D ⧸ Q, ∀ v ∈ V, conjugation Q a v ∈ V)
    (hd : Disjoint U V) : U = ⊥ ∨ V = ⊥ :=
  Subgroup.disjoint_invariant_of_centralizer_card_two Q QK Z hQK hZ hcentral U V
    (fun d u hu => hU (QuotientGroup.mk' Q d) u hu)
    (fun d v hv => hV (QuotientGroup.mk' Q d) v hv) hd

/-- The same conjugation action, viewed as binary linear automorphisms of Q. -/
public def binaryAction : D ⧸ Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) :=
  BinaryFixedLine.linearAutEquiv.toMonoidHom.comp (conjugation Q)

/-- The binary representation retains its conjugation evaluation equation. -/
public theorem binaryAction_apply (d : D) (q : Q) :
    binaryAction Q (QuotientGroup.mk' Q d) (Additive.ofMul q) =
      Additive.ofMul (MulAut.conjNormal d q) := by
  unfold binaryAction conjugation
  rfl

/-- The binary representation of the actual quotient is faithful. -/
public theorem binaryAction_injective [Z.Normal] (hZQ : Z ≤ Q)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : Function.Injective (binaryAction Q) :=
  BinaryFixedLine.linearAutEquiv.injective.comp (conjugation_injective Q Z hZQ hchain)

omit [Q.Normal] in
/-- The binary vector space associated with the actual E₁₆ has dimension four. -/
public theorem binary_finrank [Finite D] (hQcard : Nat.card Q = 16) :
    Module.finrank (ZMod 2) (Additive Q) = 4 := by
  have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
  change Nat.card Q = _ at hsize
  apply Nat.pow_right_injective (by decide : 1 < 2)
  simpa only [Nat.card_zmod, hQcard, show (2 : ℕ) ^ 4 = 16 by decide] using hsize.symm

omit [Q.Normal] in
/-- Concrete E₁₆ coordinates obtained from a basis of the actual Q. -/
public noncomputable def fourSpaceEquiv [Finite D] (hQcard : Nat.card Q = 16) :
    Q ≃* Multiplicative (Fin 4 → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) (Additive Q)
    (binary_finrank Q hQcard)).equivFun.toAddEquiv.toMultiplicativeRight

/-- The fixed-line obstruction transported to binary invariant subspaces. -/
public theorem disjoint_invariant_submodules [Finite D] (QK : Subgroup D)
    (hQK : IsPGroup 2 QK) (hZ : Nat.card Z = 2)
    (hcentral : Q ⊓ centralizer (QK : Set D) = Z)
    (U V : Submodule (ZMod 2) (Additive Q))
    (hU : ∀ a : D ⧸ Q, ∀ u ∈ U, binaryAction Q a u ∈ U)
    (hV : ∀ a : D ⧸ Q, ∀ v ∈ V, binaryAction Q a v ∈ V)
    (hd : Disjoint U V) : U = ⊥ ∨ V = ⊥ := by
  let S : Subgroup Q := U.toAddSubgroup.toSubgroup'
  let T : Subgroup Q := V.toAddSubgroup.toSubgroup'
  have hS : ∀ a : D ⧸ Q, ∀ u ∈ S, conjugation Q a u ∈ S :=
    fun a u hu => hU a (Additive.ofMul u) hu
  have hT : ∀ a : D ⧸ Q, ∀ v ∈ T, conjugation Q a v ∈ T :=
    fun a v hv => hV a (Additive.ofMul v) hv
  have hST : Disjoint S T := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hx0 : Additive.ofMul x ∈ (⊥ : Submodule (ZMod 2) (Additive Q)) :=
      (disjoint_iff.mp hd).le ⟨hx.1, hx.2⟩
    exact hx0
  rcases disjoint_invariant Q Z QK hQK hZ hcentral S T hS hT hST with he | he
  · left
    apply le_bot_iff.mp
    intro u hu
    have hu' : u.toMul ∈ S := hu
    rw [he] at hu'
    exact hu'
  · right
    apply le_bot_iff.mp
    intro v hv
    have hv' : v.toMul ∈ T := hv
    rw [he] at hv'
    exact hv'

/-- The source's E₁₆ larger-actor alternative, on the actual local quotient
and its literal four-dimensional binary conjugation representation. -/
public theorem larger_actor [Finite D] [Z.Normal]
    (hQ : Q = pCore 2 D) (hQcard : Nat.card Q = 16)
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (H : Subgroup D) (hQH : Q ≤ H)
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 D)
    (QK : Subgroup D) (hQK : IsPGroup 2 QK)
    (hcentral : Q ⊓ centralizer (QK : Set D) = Z) :
    Nonempty ((D ⧸ Q) ≃* Matrix.PSL3Two.PSL) ∧
      Nonempty (Q ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
      Function.Injective (conjugation Q) ∧
      Function.Injective (binaryAction Q) ∧
      Module.finrank (ZMod 2) (Additive Q) = 4 ∧
      (∃ z : Q, (z : D) ∈ Z ∧ z ≠ 1 ∧ Subgroup.zpowers z = Z.subgroupOf Q ∧
        ∀ a : D ⧸ Q, binaryAction Q a (Additive.ofMul z) = Additive.ofMul z) ∧
      (∀ U V : Submodule (ZMod 2) (Additive Q),
        (∀ a : D ⧸ Q, ∀ u ∈ U, binaryAction Q a u ∈ U) →
        (∀ a : D ⧸ Q, ∀ v ∈ V, binaryAction Q a v ∈ V) →
        Disjoint U V → U = ⊥ ∨ V = ⊥) := by
  refine ⟨⟨quotientEquivPSL Q Z hZ hZQ hQ hQcard hchain H hQH eH hstrict⟩,
    ⟨fourSpaceEquiv Q hQcard⟩,
    conjugation_injective Q Z hZQ hchain, binaryAction_injective Q Z hZQ hchain,
    binary_finrank Q hQcard, ?_, ?_⟩
  · obtain ⟨z, hz, hne, hgen, hfix⟩ := exists_fixed_generator Q Z hZ hZQ
    exact ⟨z, hz, hne, hgen, fun a => congrArg Additive.ofMul (hfix a)⟩
  · exact disjoint_invariant_submodules Q Z QK hQK hZ hcentral

/-- The whole overlap's Sylow subgroup descends to a Sylow eight-subgroup
inside the actual S₄ image. -/
public theorem whole_overlap_sylow [Finite D] [Z.Normal]
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) (hQ : Q = pCore 2 D)
    (hQcard : Nat.card Q = 16)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z))
    (H : Subgroup D) (hQH : Q ≤ H)
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 D)
    (T : Sylow 2 D) (hTH : (T : Subgroup D) ≤ H) :
    Nat.card (T.mapSurjective (QuotientGroup.mk'_surjective Q)) = 8 ∧
      (T.mapSurjective (QuotientGroup.mk'_surjective Q) : Subgroup (D ⧸ Q)) ≤
        H.map (QuotientGroup.mk' Q) := by
  constructor
  · rw [Sylow.card_eq_multiplicity,
      (actor_card_and_overlap_index Q Z hZ hZQ hQ hQcard hchain H hQH eH hstrict).1]
    decide +kernel
  · simpa only [Sylow.coe_mapSurjective] using
      (Subgroup.map_mono (f := QuotientGroup.mk' Q) hTH)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.E16Actor
