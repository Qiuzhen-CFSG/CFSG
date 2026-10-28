module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.GroupTheory.PResidual.OrderSix
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The actual cubic in a field-plane normalizer

For a field plane U in the original natural module B, the fixed-field
marking identifies the action of N_L(U) with SL₂(2), with two-group kernel.
Its two-residual therefore has quotient C₃, and its two-core is exactly
its intersection with C_G(U). Cauchy's theorem constructs an actual cubic
in this residual. Its image in the original SL₂ quotient has order three,
so it fixes no nonzero vector of B and fully moves B by coprime action.

The companion LocalFieldCubicAction module uses this cubic on the original
field-plane quotient in the one-sided configuration. No LocalAnalysis or
later recognition hypothesis is used.

Source: Aschbacher--Smith, 6.2.4(5), printed p.680, and the first paragraph
of the proof of 6.2.7, printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open Representation.SL2NaturalOffenders.FixedField
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}


omit [Finite G] in
private theorem natural_cubic_fixed (hnatural : IsNaturalModule L B n)
    {d : G} (hdL : d ∈ L) (hd3 : orderOf d = 3) :
    B ⊓ centralizer ({d} : Set G) = ⊥ := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let a : L := ⟨d,hdL⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha3 : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans hd3
  have hq3 : orderOf (q a) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (ha3 ▸ orderOf_map_dvd q a) with he | he
    · have hk : a ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff _).mp
        apply e.injective
        exact (orderOf_eq_one_iff.mp he).trans e.map_one.symm
      have hc := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
        (by decide : Nat.Coprime 2 3) (⟨a,hk⟩ : pCore 2 L)
      have ho : orderOf (⟨a,hk⟩ : pCore 2 L) = 3 :=
        (Subgroup.orderOf_coe _).symm.trans ha3
      rw [ho] at hc
      norm_num at hc
    · exact he
  apply eq_bot_iff.mpr
  intro b hb
  let v : B := ⟨b,hb.1⟩
  have hv : (q a).val.mulVec (f v).toAdd = (f v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hc := mem_centralizer_singleton_iff.mp hb.2
    have he := hf a v
    change (f.symm (Multiplicative.ofAdd ((q a).val.mulVec (f v).toAdd)) : G) = d * b * d⁻¹ at he
    rw [← hc,mul_inv_cancel_right] at he
    simpa only [ofAdd_toAdd, MulEquiv.symm_apply_apply] using he
  have hz := Matrix.SL2.cubic_fixed_eq_zero (q a) hq3 (f v).toAdd hv
  have hv1 : v = 1 := f.injective (by exact hz.trans f.map_one.symm)
  exact congrArg Subtype.val hv1

omit [Finite G] in
private theorem field_plane_marking
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUc : Nat.card U = 4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ∧
      ∃ p : (L ⊓ normalizer (U : Set G) : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective p ∧ IsPGroup 2 p.ker ∧
        ∃ f : U ≃* Multiplicative (Fin 2 → F),
          ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
            (f.symm (Multiplicative.ofAdd ((p l).val.mulVec (f u).toAdd)) : G) =
              (l : G) * (u : G) * (l : G)⁻¹ := by
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, d, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := field_quotientActor e d t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    let v : B := ⟨u, (hU.le u.property).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le u.property).2
  obtain ⟨τ, _, _, p, hp, hk, fU, hfU⟩ := fixedNormalizer_marking e f hf t htB hU hi hasq haout
  let E := FixedBy.subfield F τ
  have hc : Nat.card E = 2 := by
    have he := Nat.card_congr fU.toEquiv
    rw [hUc, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → E) ≃ (Fin 2 → E)), Nat.card_fun, Nat.card_fin] at he
    nlinarith
  exact ⟨E,inferInstance,inferInstance,inferInstance,hc,p,hp,hk,fU,hfU⟩

/-- An order-three element in the literal plane-normalizer residual fixes
no nonidentity element of the original natural layer. -/
theorem exists_field_plane_cubic
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUc : Nat.card U = 4) :
    ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧
      B ⊓ centralizer ({d} : Set G) = ⊥ := by
  obtain ⟨F, _, _, _, hF, p, hp, _, _, _⟩ := field_plane_marking hnatural hfield hUc
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
    let : Fintype F := Fintype.ofFinite F
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
    decide
  have hdiv : 3 ∣ Nat.card (L ⊓ normalizer (U : Set G) : Subgroup G) :=
    (show 3 ∣ 6 by decide).trans (hcard ▸ Subgroup.card_dvd_of_surjective p hp)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := (L ⊓ normalizer (U : Set G) : Subgroup G)) 3 hdiv
  refine ⟨d, ⟨d,mem_pResidual_of_orderOf_coprime (by rw [hd]; decide),rfl⟩,?_,?_⟩
  · simpa only [Subgroup.orderOf_coe] using hd
  · exact natural_cubic_fixed hnatural d.property.1 (by simpa only [Subgroup.orderOf_coe] using hd)
omit [Finite G] in
private theorem marking_kernel
    {F : Type*} [Field F]
    (N : Subgroup G) (p : N →* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : U ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : N) (u : U),
      (f.symm (Multiplicative.ofAdd ((p l).val.mulVec (f u).toAdd)) : G) =
        (l : G) * (u : G) * (l : G)⁻¹) :
    p.ker = (centralizer (U : Set G)).subgroupOf N := by
  ext l
  change p l = 1 ↔ (l : G) ∈ centralizer (U : Set G)
  constructor
  · intro hl u hu
    have he := hf l ⟨u,hu⟩
    rw [hl] at he
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
      ofAdd_toAdd, MulEquiv.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hl
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    have he := hf l (f.symm (Multiplicative.ofAdd v))
    rw [f.apply_symm_apply] at he
    have hc := hl _ (f.symm (Multiplicative.ofAdd v)).property
    rw [← hc, mul_inv_cancel_right] at he
    have he' := congrArg f (Subtype.ext he)
    simpa only [f.apply_symm_apply,ofAdd_toAdd,toAdd_ofAdd,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mulVec] using congrArg Multiplicative.toAdd he'

/-- The actual two-residual of the plane normalizer has cubic quotient,
with two-core exactly its intersection with the plane centralizer. -/
theorem field_plane_residual_structure
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUc : Nat.card U = 4) :
    let K := fieldLocalResidual L U
    K.pCoreIn 2 = K ⊓ centralizer (U : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨F, _, _, _, hF, p, hp, hk, f, hf⟩ := field_plane_marking hnatural hfield hUc
  let N := L ⊓ normalizer (U : Set G)
  let S := Matrix.SpecialLinearGroup (Fin 2) F
  let P := pResidual 2 N
  let K := fieldLocalResidual L U
  let Q := pResidual 2 S
  have hS : Nat.card S = 6 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    decide
  have hQ : Nat.card Q = 3 := card_twoResidual_of_card_six hS
  have hmap : P.map p = Q := map_pResidual_of_surjective 2 p hp
  let e : P ≃* K := P.equivMapOfInjective N.subtype N.subtype_injective
  let r : K →* N := P.subtype.comp e.symm.toMonoidHom
  have hr (k : K) : (r k : G) = k := by
    have he := congrArg (fun x : K => (x : G)) (e.apply_symm_apply k)
    exact he
  let q0 : K →* S := p.comp r
  have hq0range : q0.range = Q := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,
      e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
      ← MonoidHom.range_eq_map,P.range_subtype]
    exact hmap
  let q : K →* Q := q0.codRestrict Q (fun k => hq0range ▸ (show q0 k ∈ q0.range from ⟨k,rfl⟩))
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : S) ∈ q0.range := hq0range.symm ▸ y.property
    obtain ⟨k,hk⟩ := hy
    exact ⟨k,Subtype.ext hk⟩
  have hqker : q.ker = p.ker.comap r := by
    ext k
    change q k = 1 ↔ p (r k) = 1
    exact Subtype.ext_iff
  have hrinj : Function.Injective r := P.subtype_injective.comp e.symm.injective
  have hqk : IsPGroup 2 q.ker := by
    rw [hqker]
    exact hk.comap_of_injective r hrinj
  have hQcore : pCore 2 Q = ⊥ := by
    have hthree : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by simpa using hQ)
    have hd := (pCore_isPGroup (p := 2) (G := Q)).disjoint_of_coprime
      (hthree.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa using hd
  have hcore : pCore 2 K = q.ker := by
    have he := q.comap_pCore_of_ker_isPGroup hq hqk
    rw [hQcore,MonoidHom.comap_bot] at he
    exact he.symm
  have hcentral : q.ker = (centralizer (U : Set G)).subgroupOf K := by
    rw [hqker,marking_kernel N p f hf]
    ext k
    change (r k : G) ∈ centralizer (U : Set G) ↔ (k : G) ∈ centralizer (U : Set G)
    rw [hr]
  refine ⟨?_,?_⟩
  · change (pCore 2 K).map K.subtype = _
    rw [hcore,hcentral,subgroupOf_map_subtype,inf_comm]
  · let eQ := (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    exact ⟨eQ.trans (mulEquivOfPrimeCardEq hQ (by
      change Nat.card (ZMod 3) = 3
      exact Nat.card_zmod _))⟩
/-- The actual cubic fully moves the original natural layer. -/
theorem field_plane_cubic_movement
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUc : Nat.card U = 4) :
    ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧
      ⁅B,zpowers d⁆ = B ∧ B ⊓ centralizer ({d} : Set G) = ⊥ := by
  obtain ⟨d,hd,ho,hfixed⟩ := exists_field_plane_cubic hnatural hfield hUc
  have hDL : zpowers d ≤ L := zpowers_le.mpr ((map_subtype_le _ hd).1)
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hsolv : Group.IsSolvable B := by
    obtain ⟨_, _, _, _, _, _, f, _⟩ := hnatural
    exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  have hcop : Nat.Coprime (Nat.card (zpowers d)) (Nat.card B) := by
    rw [Nat.card_zpowers,ho,hnatural.card]
    exact (by decide : Nat.Coprime 3 2).pow_right _
  have he := eq_commutator_sup_centralizer_of_solvable_coprime B (zpowers d)
    (hDL.trans hLB) hsolv hcop
  rw [zpowers_eq_closure, centralizer_closure,hfixed,sup_bot_eq] at he
  exact ⟨d,hd,ho,by simpa only [← zpowers_eq_closure] using he.symm,hfixed⟩


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
