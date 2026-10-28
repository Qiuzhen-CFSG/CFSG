module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ActionTransport

/-!
# Identifying the component under an extension isomorphism

The component image in I/O_{3'}(I) lies in its three-prime residual. An
isomorphism of that residual with a model having a normal index-three
subgroup must carry the component onto that subgroup: the component is
perfect, the model quotient is abelian, and their orders agree. Thus the
nonsplit model's index and absence of a complement transfer to the literal
component image, without assuming a marked extension isomorphism.

For an extension realized in Aut(H) with abelian quotient over Inn(H), the
same argument constructs component coordinates from the extension map.
Conjugation in these coordinates is exactly the model action. Applying
this to the GL3 and unitary conjugation images gives diagonal actors when
Yplus is not contained in L, using the existing quotient-outerness proof.

These are conditional transport results. They do not construct A.3.16's
particular diagonal-field model, or infer local noncontainment from
noncontainment of theta(I). Those remain separate source obligations.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.16--18,
printed pp.51--52, and the reductions in 15.3.37 and 15.3.43, pp.1135, 1139.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels

variable {G H A : Type*} [Group G] [Group H] [Group A]

private theorem conj_injective (hz : center H = ⊥) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : H →* MulAut H).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hc : x ∈ center H := by
    apply mem_center_iff.mpr
    intro y
    have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [hz, mem_bot] using hc

private theorem identify_image [Finite H] (K : Subgroup A) [Group.IsPerfect K]
    (E : Subgroup (MulAut H)) (e : A ≃* E)
    (hz : center H = ⊥) (hc : Nat.card K = Nat.card H)
    (hcomm : ⁅E, E⁆ ≤ MulAut.innerSubgroup H) :
    K.map (E.subtype.comp e.toMonoidHom) = MulAut.innerSubgroup H := by
  let f := E.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := E.subtype_injective.comp e.injective
  let : Group.IsPerfect (K.map f) := Group.IsPerfect.map f
  have hle : K.map f ≤ MulAut.innerSubgroup H := by
    rw [← (K.map f).commutator_eq_self]
    exact (commutator_mono (map_le_iff_le_comap.mpr (by intro x hx; exact (e x).property))
      (map_le_iff_le_comap.mpr (by intro x hx; exact (e x).property))).trans hcomm
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective hf, hc]
  exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective hz)).toEquiv).ge

private theorem exists_coordinates [Finite H] (K : Subgroup A) [Group.IsPerfect K]
    (E : Subgroup (MulAut H)) (e : A ≃* E)
    (hz : center H = ⊥) (hc : Nat.card K = Nat.card H)
    (hcomm : ⁅E, E⁆ ≤ MulAut.innerSubgroup H) :
    ∃ c : K ≃* H, ∀ k : K, MulAut.conj (c k) = (e k : MulAut H) := by
  let f := E.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := E.subtype_injective.comp e.injective
  let j : H ≃* MulAut.innerSubgroup H := MonoidHom.ofInjective (conj_injective hz)
  let c := (K.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr (identify_image K E e hz hc hcomm)).trans j.symm)
  refine ⟨c, ?_⟩
  intro k
  have he := j.apply_symm_apply
    ((MulEquiv.subgroupCongr (identify_image K E e hz hc hcomm))
      (K.equivMapOfInjective f hf k))
  exact congrArg Subtype.val he

variable [Finite G]

/-- The literal component image is contained in the residual used in A.3.18. -/
theorem image_le_residual {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L) :
    (L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I)) ≤
      primeToResidual 3 (I ⧸ pPrimeCore 3 I) := by
  let := hcomp.2
  have hrK : 1 ≤ primeRank 3 (L.subgroupOf I) := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  rw [← theta_eq_self_of_quasisimple (component_center_eq_twoCore hcomp hodd).le hrK]
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  apply mem_primeToResidual_of_pow (n := 1)
  rw [pow_one, ← map_pow, ← hx3, pow_orderOf_eq_one, map_one]

/-- The literal image of the relative component in the three-prime-core quotient. -/
abbrev Image (I L : Subgroup G) :=
  (L.subgroupOf I).map (QuotientGroup.mk' (pPrimeCore 3 I))

/-- The residual in the quotient, rather than in the original overgroup. -/
abbrev Residual (I : Subgroup G) := primeToResidual 3 (I ⧸ pPrimeCore 3 I)

/-- Construct coordinates from the extension equivalence; the supplied component
model is used only for its order and the triviality of its center. -/
theorem exists_compatible_coordinates [Finite H] {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L)
    (E : Subgroup (MulAut H)) (e : Residual I ≃* E)
    (model : (L ⧸ pCore 2 L) ≃* H)
    (hcomm : ⁅E, E⁆ ≤ MulAut.innerSubgroup H) :
    ∃ c : (L ⧸ pCore 2 L) ≃* H,
      ∀ (y : G) (hyI : y ∈ I) (hy3 : orderOf y = 3)
        (hyN : y ∈ normalizer (L : Set G)),
        LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl c ⟨y, hyN⟩ =
          (e ⟨QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩,
            mem_primeToResidual_of_pow (n := 1)
              (by simpa only [pow_one, quotient_order_three hyI hy3] using
                pow_orderOf_eq_one (QuotientGroup.mk' (pPrimeCore 3 I) ⟨y, hyI⟩))⟩ : MulAut H) := by
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  have hKR := image_le_residual hLI hcomp hodd hr
  let K := (Image I L).subgroupOf (Residual I)
  let j := localQuotientEquiv hLI hcomp hodd hr
  let k : K ≃* Image I L := subgroupOfEquivOfLe hKR
  let g : Image I L ≃* H := j.symm.trans model
  let := hcomp.2
  let : Group.IsPerfect (Image I L) := Group.IsPerfect.map q
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := k.symm.toMonoidHom) k.symm.surjective
  have hz : center H = ⊥ := by
    apply card_eq_one.mp
    rw [← Nat.card_congr (centerCongr g).toEquiv]
    have hrK : 1 ≤ primeRank 3 (L.subgroupOf I) := by
      rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
    rw [image_center hcomp hodd hrK]
    exact Nat.card_unique
  obtain ⟨cK, hcK⟩ := exists_coordinates K E e hz
    (Nat.card_congr (k.trans g).toEquiv) hcomm
  let c := j.trans (k.symm.trans cK)
  have hc (x : L) : MulAut.conj (c (QuotientGroup.mk' (pCore 2 L) x)) =
      (e ⟨q ⟨x, hLI x.property⟩, hKR (mem_map_of_mem q x.property)⟩ : MulAut H) := by
    have hh := hcK (k.symm (j (QuotientGroup.mk' (pCore 2 L) x)))
    change MulAut.conj (c (QuotientGroup.mk' (pCore 2 L) x)) = _ at hh
    rw [hh]
    congr 2
    apply Subtype.ext
    exact localQuotientEquiv_mk hLI hcomp hodd hr x
  refine ⟨c, ?_⟩
  intro y hyI hy3 hyN
  let r : Residual I := ⟨q ⟨y, hyI⟩,
    mem_primeToResidual_of_pow (n := 1)
      (by simpa only [q, pow_one, quotient_order_three hyI hy3] using
        pow_orderOf_eq_one (q ⟨y, hyI⟩))⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := (c.surjective.comp (QuotientGroup.mk'_surjective _)) z
  simp only [Function.comp_apply]
  rw [LinearCore.quotientAction_apply]
  apply conj_injective hz
  rw [hc]
  have hconj (α : MulAut H) (z : H) :
      MulAut.conj (α z) = α * MulAut.conj z * α⁻¹ := by
    ext w
    simp [MulAut.conj_apply, MulAut.mul_apply]
  rw [hconj, hc]
  change (e _ : MulAut H) = (e r : MulAut H) * (e _ : MulAut H) * (e r : MulAut H)⁻¹
  rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul,
    ← map_inv, ← map_mul, ← map_mul]
  congr 2

/-- Any extension equivalence identifies the component with the model's normal
index-three subgroup, without assuming compatibility of the component model. -/
theorem component_image_of_index_three_model [Finite A] {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L)
    (N : Subgroup A) [N.Normal] (e : Residual I ≃* A)
    (model : (L ⧸ pCore 2 L) ≃* N) (hi : N.index = 3) :
    ((Image I L).subgroupOf (Residual I)).map e.toMonoidHom = N := by
  have hKR := image_le_residual hLI hcomp hodd hr
  let K := (Image I L).subgroupOf (Residual I)
  let k : K ≃* Image I L := subgroupOfEquivOfLe hKR
  let j := localQuotientEquiv hLI hcomp hodd hr
  let := hcomp.2
  let : Group.IsPerfect (Image I L) := Group.IsPerfect.map _
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := k.symm.toMonoidHom) k.symm.surjective
  let : Group.IsPerfect (K.map e.toMonoidHom) := Group.IsPerfect.map _
  let : IsCyclic (A ⧸ N) := isCyclic_of_prime_card (N.index_eq_card.symm.trans hi)
  let : Group.IsSolvable (A ⧸ N) := Group.isSolvable_of_comm
    (IsCyclic.isMulCommutative (α := A ⧸ N)).is_comm.comm
  apply eq_of_le_of_card_ge (le_of_isPerfect_of_solvable_quotient _ N)
  rw [card_map_of_injective e.injective]
  exact (Nat.card_congr ((k.trans j.symm).trans model).toEquiv).ge

/-- Transport a model nonsplitting result after proving which subgroup is the
component. The model input must be instantiated by the particular A.3.16 extension. -/
theorem nonsplit_model_transport [Finite A] {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L)
    (N : Subgroup A) [N.Normal] (e : Residual I ≃* A)
    (model : (L ⧸ pCore 2 L) ≃* N) (hi : N.index = 3)
    (hns : ¬ ∃ D : Subgroup A, N.IsComplement' D) :
    (Image I L).relIndex (Residual I) = 3 ∧
      ¬ ∃ D : Subgroup (Residual I), ((Image I L).subgroupOf (Residual I)).IsComplement' D := by
  let K := (Image I L).subgroupOf (Residual I)
  have hmark : K.map e.toMonoidHom = N :=
    component_image_of_index_three_model hLI hcomp hodd hr N e model hi
  refine ⟨?_, ?_⟩
  · change K.index = 3
    rw [← K.index_map_equiv e]
    change (K.map e.toMonoidHom).index = 3
    rw [hmark, hi]
  · rintro ⟨D, hD⟩
    apply hns
    refine ⟨D.map e.toMonoidHom, ?_⟩
    rw [← hmark]
    apply isComplement'_of_card_mul_and_disjoint
    · rw [card_map_of_injective e.injective, card_map_of_injective e.injective,
        hD.card_mul_card, Nat.card_congr e.toEquiv]
    · exact disjoint_map e.injective hD.disjoint

/-- A nonsplit model with an index-three normal component yields the theta identity.
No compatibility between the two supplied isomorphisms is assumed. -/
theorem theta_eq_of_nonsplit_model [Finite A] {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (N : Subgroup A) [N.Normal] (e : Residual I ≃* A)
    (model : (L ⧸ pCore 2 L) ≃* N) (hi : N.index = 3)
    (hns : ¬ ∃ D : Subgroup A, N.IsComplement' D) : theta I = L := by
  obtain ⟨hi', hns'⟩ := nonsplit_model_transport hLI hcomp hodd (by omega) N e model hi hns
  exact theta_eq_of_nonsplit hLI hcomp hodd hrankL hrankI hindex hi' hns'

open scoped MatrixGroups

/-- The GL3 extension determines compatible coordinates for every cubic actor. -/
theorem linear_action_range {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L)
    {F : Type} [Field F] [Finite F]
    (e : Residual I ≃* (Matrix.PSL3.OuterSolvable.linearConj F).range)
    (model : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    ∃ c : (L ⧸ pCore 2 L) ≃* PSL(3,F),
      ∀ (y : G), y ∈ I → orderOf y = 3 →
        ∀ hyN : y ∈ normalizer (L : Set G),
          LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl c ⟨y, hyN⟩ ∈
            (Matrix.PSL3.OuterSolvable.linearConj F).range := by
  have hcomm : ⁅(Matrix.PSL3.OuterSolvable.linearConj F).range,
      (Matrix.PSL3.OuterSolvable.linearConj F).range⁆ ≤ MulAut.innerSubgroup PSL(3,F) := by
    apply commutator_le.mpr
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    rw [← map_commutatorElement]
    apply Matrix.PSL3.OuterSolvable.det_ker_le_linearOuterAction_ker F
    simp [commutatorElement_def]
  obtain ⟨c, hc⟩ := exists_compatible_coordinates hLI hcomp hodd hr _ e model hcomm
  exact ⟨c, fun y hyI hy3 hyN => hc y hyI hy3 hyN ▸ (e _).property⟩

/-- The unitary extension determines coordinates using the same Hermitian form. -/
theorem unitary_action_range {I L : Subgroup G}
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hr : 1 ≤ primeRank 3 L)
    {F : Type} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (e : Residual I ≃* J.unitaryConjHom.range)
    (model : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ c : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ (y : G), y ∈ I → orderOf y = 3 →
        ∀ hyN : y ∈ normalizer (L : Set G),
          LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl c ⟨y, hyN⟩ ∈
            J.unitaryConjHom.range := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hcomm : ⁅J.unitaryConjHom.range, J.unitaryConjHom.range⁆ ≤
      MulAut.innerSubgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
    apply commutator_le.mpr
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    simpa only [J.unitaryConjHom_apply] using J.unitaryConj_commutator_is_inner u v
  obtain ⟨c, hc⟩ := exists_compatible_coordinates hLI hcomp hodd hr _ e model hcomm
  exact ⟨c, fun y hyI hy3 hyN => hc y hyI hy3 hyN ▸ (e _).property⟩

/-- Construct the linear diagonal actor once local noncontainment is known. -/
theorem linear_actor_of_not_le {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    {F : Type} [Field F] [Finite F] {q : ℕ} (hcard : Nat.card F = q)
    (e : Residual I ≃* (Matrix.PSL3.OuterSolvable.linearConj F).range)
    (model : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧ LinearDiagonalOnTwoQuotient L y q := by
  obtain ⟨c, hc⟩ := linear_action_range hLI hcomp hodd (by omega) e model
  obtain ⟨y, hy, hyN, hyI, hy3, hyL, _⟩ := exists_order_three_quotient_outer
    hθ hnot hLI hcomp hodd hrankL hrankI hindex c
  exact ⟨y, hy, hy3, hyL, linear_diagonal_of_action_range hLI hcomp hodd hrankL hrankI
    hyI hy3 hyL hyN hcard c (hc y hyI hy3 hyN)⟩

/-- Construct the unitary diagonal actor with the original q, field order q squared,
and q-Frobenius, once local noncontainment is known. -/
theorem unitary_actor_of_not_le {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hnot : ¬ Yplus ≤ L)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrankL : 2 ≤ primeRank 3 L)
    (hrankI : primeRank 3 I ≤ 2)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    {F : Type} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hfrob : ∀ x, J.conj x = x ^ q)
    (e : Residual I ≃* J.unitaryConjHom.range)
    (model : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ y ∈ Yplus, orderOf y = 3 ∧ y ∉ L ∧ UnitaryDiagonalOnTwoQuotient L y q := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨c, hc⟩ := unitary_action_range hLI hcomp hodd (by omega) J e model
  obtain ⟨y, hy, hyN, hyI, hy3, hyL, _⟩ := exists_order_three_quotient_outer
    hθ hnot hLI hcomp hodd hrankL hrankI hindex c
  exact ⟨y, hy, hy3, hyL, unitary_diagonal_of_action_range hLI hcomp hodd hrankL hrankI
    hyI hy3 hyL hyN J hcard hfrob c (hc y hyI hy3 hyN)⟩

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels
