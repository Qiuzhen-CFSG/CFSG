module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
public import Theory.GroupTheory.DihedralCentralProductThree
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# Assembly of the two-summand recognition branch

This file contains the source-theorem assembly after the two literal
constituent models have been obtained from G.6.4.  The actor map is the actual
conjugation map on the normal subgroup `K`, transported through its actual
isomorphism with `PSL₃(2)`.  Its inner subgroup is supplied by `K`, and one
specified summand interchange supplies the outer coset.  The final
extraspecial statement uses the intrinsic order-128 plus-type recognition.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.58,
printed pp.1148--1149.
-/

@[expose] public section

open Representation
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch

noncomputable def actorConjugation {A L : Type*} [Group A] [Group L]
    (N : Subgroup A) [N.Normal] (e : N ≃* L) : A →* MulAut L :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : A →* MulAut N)

theorem actorConjugation_on_normal {A L : Type*} [Group A] [Group L]
    (N : Subgroup A) [N.Normal] (e : N ≃* L) (n : N) :
    actorConjugation N e n = MulAut.conj (e n) := by
  apply MulEquiv.ext
  intro x
  simp [actorConjugation, MulAut.conjNormal_val, MulAut.congr_apply]

theorem inner_le_actorConjugation_range {A L : Type*} [Group A] [Group L]
    (N : Subgroup A) [N.Normal] (e : N ≃* L) :
    MulAut.innerSubgroup L ≤ (actorConjugation N e).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨n, rfl⟩ := e.surjective x
  exact ⟨n, actorConjugation_on_normal N e n⟩

theorem psl_inner_index :
    (MulAut.innerSubgroup Matrix.PSL3Two.PSL).index = 2 := by
  have hAut : Nat.card (MulAut Matrix.PSL3Two.PSL) = 336 :=
    Matrix.PSL3Two.Automorphisms.card_aut
  have hi : Function.Injective (MulAut.conj : Matrix.PSL3Two.PSL →*
      MulAut Matrix.PSL3Two.PSL) :=
    MulAut.conj_injective_of_center_eq_bot
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot
  have hInner : Nat.card (MulAut.innerSubgroup Matrix.PSL3Two.PSL) = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact Matrix.PSL3Two.card_PSL
  have h := (MulAut.innerSubgroup Matrix.PSL3Two.PSL).card_mul_index
  rw [hAut, hInner] at h
  omega

theorem actorConjugation_range_top_of_outer
    {A L : Type*} [Group A] [Group L]
    (N : Subgroup A) [N.Normal] (e : N ≃* L) (t : A)
    (hinner : MulAut.innerSubgroup L ≤ (actorConjugation N e).range)
    (houter : actorConjugation N e t ∉ MulAut.innerSubgroup L)
    (hindex : (MulAut.innerSubgroup L).index = 2) :
    (actorConjugation N e).range = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  by_cases hia : a ∈ MulAut.innerSubgroup L
  · exact hinner hia
  · have hprod : a * actorConjugation N e t ∈ MulAut.innerSubgroup L := by
      apply (MulAut.innerSubgroup L).mul_mem_iff_of_index_two hindex |>.mpr
      exact iff_of_false hia houter
    obtain ⟨y, hy⟩ := hinner hprod
    refine ⟨y * t⁻¹, ?_⟩
    rw [map_mul, map_inv, hy]
    group

theorem actorConjugation_injective
    {A L : Type*} [Group A] [Group L]
    (N : Subgroup A) [N.Normal] (e : N ≃* L)
    (hcent : Subgroup.centralizer (N : Set A) = ⊥) :
    Function.Injective (actorConjugation N e) := by
  intro a b hab
  have hconj : (MulAut.conjNormal : A →* MulAut N) a =
      (MulAut.conjNormal : A →* MulAut N) b := by
    apply (MulAut.congr e).injective
    exact hab
  have hk : a * b⁻¹ ∈ (MulAut.conjNormal : A →* MulAut N).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hconj]
    simp
  have hk' : a * b⁻¹ ∈ Subgroup.centralizer (N : Set A) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer N]
    exact hk
  have : a * b⁻¹ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hcent]
    exact hk'
  calc
    a = (a * b⁻¹) * b := by group
    _ = 1 * b := by rw [this]
    _ = b := by simp

theorem actorConjugation_outer_of_swap
    {A L V : Type*} [Group A] [Group L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (N : Subgroup A) [N.Normal]
    (e : N ≃* L) (t : A)
    (hcent : Subgroup.centralizer (N : Set A) = ⊥)
    (J₁ J₂ : Submodule (ZMod 2) V)
    (hstable : ∀ k : N, Submodule.map (ρ k) J₁ ≤ J₁)
    (hswap : Submodule.map (ρ t) J₁ = J₂)
    (hne : J₁ ≠ J₂)
    (hdim : Module.finrank (ZMod 2) J₁ = Module.finrank (ZMod 2) J₂) :
    actorConjugation N e t ∉ MulAut.innerSubgroup L := by
  intro hout
  obtain ⟨x, hx⟩ := hout
  obtain ⟨k, hk⟩ := e.surjective x
  have hφ : actorConjugation N e t = actorConjugation N e (k : A) := by
    calc
      actorConjugation N e t = MulAut.conj x := hx.symm
      _ = MulAut.conj (e k) := congrArg MulAut.conj hk.symm
      _ = actorConjugation N e (k : A) :=
        (actorConjugation_on_normal N e k).symm
  have hconj : (MulAut.conjNormal : A →* MulAut N) t =
      (MulAut.conjNormal : A →* MulAut N) (k : A) := by
    apply (MulAut.congr e).injective
    simpa [actorConjugation] using hφ
  have hker : t * (k : A)⁻¹ ∈
      (MulAut.conjNormal : A →* MulAut N).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hconj]
    simp
  have htc : t * (k : A)⁻¹ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hcent, ← MulAut.conjNormal_ker_eq_centralizer N]
    exact hker
  have ht : t = (k : A) := by
    apply mul_right_cancel (b := (k : A)⁻¹)
    simp [htc]
  have hle : J₂ ≤ J₁ := by
    rw [← hswap, Submodule.map_le_iff_le_comap]
    intro y hy
    rw [ht]
    exact hstable k (Submodule.mem_map_of_mem hy)
  have heq : J₂ = J₁ :=
    Submodule.eq_of_le_of_finrank_eq (S₁ := J₂) (S₂ := J₁) hle hdim.symm
  exact hne heq.symm

/-- The specified source element in clause (3).  Its ambient membership and
outside condition are retained literally; no involutivity is included or used.
The final field is the actual action on the chosen first summand. -/
structure SpecifiedTData {G : Type*} [Group G] [Finite G]
    (Z ZS T V : Subgroup G) (t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (J₁ J₂ : Submodule (ZMod 2) (Space Z ZS)) where
  t_mem : t ∈ T
  t_mem_H : t ∈ centralizerH Z
  t_outside : t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))
  actor : ActorQuotient Z
  actor_eq : actor = QuotientGroup.mk' _ ⟨t, t_mem_H⟩
  swap : Submodule.map (actorRepresentation Z ZS hkernel actor) J₁ = J₂

/-- Source data for the final two-summand assembly.  The two
`centralizer_*_fixed` fields are the concrete natural-module commutant
calculation (`End_K(U_i)=F₂`) on the two singular constituents.  They are
retained at the action level; the full actor centralizer is proved below. -/
structure SourceData {G : Type*} [Group G] [Finite G]
    (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) where
  K : Subgroup (ActorQuotient Z)
  K_normal : K.Normal
  v : ActorQuotient Z
  s : ℕ
  pair : SplitPair (actorRepresentation Z ZS hkernel) K v s
  first_model : BinaryLinearThree.NaturalModel pair.first.toRepresentation
  second_model : BinaryLinearThree.NaturalModel pair.second.toRepresentation
  q : QuadraticForm (ZMod 2) (Space Z ZS)
  q_invariant : ∀ a w, q (actorRepresentation Z ZS hkernel a w) = q w
  q_nondegenerate : q.polarBilin.Nondegenerate
  actor_irreducible : Representation.IsIrreducible
    (actorRepresentation Z ZS hkernel)
  block_permutation : ∀ a : ActorQuotient Z,
    Submodule.map (actorRepresentation Z ZS hkernel a) pair.first.toSubmodule =
        pair.first.toSubmodule ∨
      Submodule.map (actorRepresentation Z ZS hkernel a) pair.first.toSubmodule =
        pair.second.toSubmodule
  centralizer_first_fixed : ∀ c ∈ Subgroup.centralizer (K : Set (ActorQuotient Z)),
    ∀ w ∈ pair.first.toSubmodule,
      actorRepresentation Z ZS hkernel c w = w
  centralizer_second_fixed : ∀ c ∈ Subgroup.centralizer (K : Set (ActorQuotient Z)),
    ∀ w ∈ pair.second.toSubmodule,
      actorRepresentation Z ZS hkernel c w = w
  specified_T : Subgroup G
  specified_V : Subgroup G
  specified_t : G
  specified : SpecifiedTData Z ZS specified_T specified_V specified_t hkernel
    pair.first.toSubmodule pair.second.toSubmodule
  U_card : Nat.card (closureU Z ZS) = 128
  elementary_subgroup : Subgroup (closureU Z ZS)
  elementary_instance : IsElementaryAbelian 2 elementary_subgroup
  elementary_card : Nat.card elementary_subgroup = 16
  center_in_elementary : Subgroup.center (closureU Z ZS) ≤ elementary_subgroup
  extraspecial_instance : IsExtraspecial 2 (closureU Z ZS)

instance {G : Type*} [Group G] [Finite G] {Z ZS : Subgroup G}
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    {hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)}
    (d : SourceData Z ZS hkernel) : d.K.Normal := d.K_normal

variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))

/-- The complete source conclusion of the two-summand branch. -/
structure RecognitionConclusion {G : Type*} [Group G] [Finite G]
    (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (d : SourceData Z ZS hkernel) where
  s_eq_one : d.s = 1
  first_singular : ∀ w ∈ d.pair.first.toSubmodule, d.q w = 0
  second_singular : ∀ w ∈ d.pair.second.toSubmodule, d.q w = 0
  non_self_equivalent : ¬ Nonempty (Representation.Equiv
    d.pair.first.toRepresentation d.pair.second.toRepresentation)
  dual_pairing : Nonempty (Representation.Equiv d.pair.second.toRepresentation
    (BinaryLinearThree.W.dual.comp
      (d.first_model.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom))
  transitive : ∃ a : ActorQuotient Z,
    Submodule.map (actorRepresentation Z ZS hkernel a) d.pair.first.toSubmodule =
      d.pair.second.toSubmodule
  centralizer_trivial : Subgroup.centralizer (d.K : Set (ActorQuotient Z)) = ⊥
  actor_equiv : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.PSL
  actor_inner : d.K.map (actor_equiv.toMonoidHom) = MulAut.innerSubgroup Matrix.PSL3Two.PSL
  specified_t_mem : d.specified_t ∈ d.specified_T
  specified_t_outside : d.specified_t ∉
    closureU Z ZS ⊔ (d.specified_T ⊓ centralizer (d.specified_V : Set G))
  specified_actor_eq : d.specified.actor = QuotientGroup.mk' _
    ⟨d.specified_t, d.specified.t_mem_H⟩
  specified_interchange :
    Submodule.map (actorRepresentation Z ZS hkernel d.specified.actor)
      d.pair.first.toSubmodule = d.pair.second.toSubmodule
  specified_outer : actor_equiv d.specified.actor ∉
    MulAut.innerSubgroup Matrix.PSL3Two.PSL
  extraspecial_equiv : closureU Z ZS ≃* DihedralCentralProductThree.Model

/-- The two-summand source branch, including the actual `Aut(L₃(2))` actor,
the specified natural/dual interchange, and the plus-type extraspecial model. -/
noncomputable def recognize_two_summand (d : SourceData Z ZS hkernel) :
    RecognitionConclusion Z ZS hkernel d := by
  letI := d.K_normal
  obtain ⟨hs, hsing₁, hsing₂, hne, hdual⟩ := geometry_of_natural_models
    Z ZS hkernel d.K d.v d.s d.pair d.q d.q_invariant d.q_nondegenerate
    d.first_model d.second_model
  have hdim : Module.finrank (ZMod 2) d.pair.first.toSubmodule =
      Module.finrank (ZMod 2) d.pair.second.toSubmodule := by
    rw [d.first_model.finrank_eq_three, d.second_model.finrank_eq_three]
  have hsub_ne : d.pair.first.toSubmodule ≠ d.pair.second.toSubmodule := by
    intro heq
    have hb : d.pair.first.toSubmodule = ⊥ :=
      disjoint_self.mp (heq ▸ d.pair.complement.disjoint)
    have hz0 : Module.finrank (ZMod 2) d.pair.first.toSubmodule = 0 := by
      rw [hb]
      simp
    have hz3 := d.first_model.finrank_eq_three
    omega
  have hfirst_stable : ∀ k : d.K,
      Submodule.map (actorRepresentation Z ZS hkernel k) d.pair.first.toSubmodule ≤
        d.pair.first.toSubmodule := by
    intro k
    refine Submodule.map_le_iff_le_comap.mpr ?_
    intro w hw
    exact d.pair.first.apply_mem_toSubmodule k hw
  have htrans : ∃ a : ActorQuotient Z,
      Submodule.map (actorRepresentation Z ZS hkernel a) d.pair.first.toSubmodule =
        d.pair.second.toSubmodule := by
    by_contra hn
    push Not at hn
    have hall : ∀ a : ActorQuotient Z,
        Submodule.map (actorRepresentation Z ZS hkernel a) d.pair.first.toSubmodule =
          d.pair.first.toSubmodule := by
      intro a
      exact (d.block_permutation a).resolve_right (hn a)
    let J : Subrepresentation (actorRepresentation Z ZS hkernel) :=
      Subrepresentation.mk d.pair.first.toSubmodule (by
        intro a w hw
        have hm : actorRepresentation Z ZS hkernel a w ∈
            Submodule.map (actorRepresentation Z ZS hkernel a)
              d.pair.first.toSubmodule :=
          Submodule.mem_map_of_mem hw
        rw [hall a] at hm
        exact hm)
    have hirr := d.actor_irreducible
    rw [Representation.IsIrreducible, isSimpleOrder_iff] at hirr
    obtain hbot | htop := hirr.2 J
    · have hbotSub : d.pair.first.toSubmodule = ⊥ :=
        congrArg Subrepresentation.toSubmodule hbot
      have hz0 : Module.finrank (ZMod 2) d.pair.first.toSubmodule = 0 := by
        rw [hbotSub]
        simp
      have hz3 := d.first_model.finrank_eq_three
      omega
    · have htopSub : d.pair.first.toSubmodule = ⊤ :=
        congrArg Subrepresentation.toSubmodule htop
      have hsec : d.pair.second.toSubmodule = ⊥ := by
        apply bot_unique
        intro w hw
        have hfirst : w ∈ d.pair.first.toSubmodule := by
          rw [htopSub]
          trivial
        exact d.pair.complement.disjoint.le_bot ⟨hfirst, hw⟩
      have hz0 : Module.finrank (ZMod 2) d.pair.second.toSubmodule = 0 := by
        rw [hsec]
        simp
      have hz3 := d.second_model.finrank_eq_three
      omega
  have hcentral : Subgroup.centralizer (d.K : Set (ActorQuotient Z)) = ⊥ := by
    apply le_antisymm
    · intro c hc
      apply Subgroup.mem_bot.mpr
      apply (actorRepresentation_injective Z ZS hkernel)
      ext w
      obtain ⟨u, z, hw, _⟩ :=
        Submodule.existsUnique_add_of_isCompl d.pair.complement w
      have hu := d.centralizer_first_fixed c hc u.1 u.2
      have hz := d.centralizer_second_fixed c hc z.1 z.2
      have hsum : actorRepresentation Z ZS hkernel c (u.1 + z.1) = u.1 + z.1 := by
        rw [map_add, hu, hz]
      rw [← hw]
      simp only [map_one]
      exact congrArg Additive.toMul hsum
    · exact bot_le
  let eK : d.K ≃* Matrix.PSL3Two.PSL := d.first_model.actor
  let φ : ActorQuotient Z →* MulAut Matrix.PSL3Two.PSL :=
    actorConjugation d.K eK
  have houter : φ d.specified.actor ∉
      MulAut.innerSubgroup Matrix.PSL3Two.PSL := by
    exact actorConjugation_outer_of_swap
      (actorRepresentation Z ZS hkernel) d.K eK d.specified.actor hcentral
      d.pair.first.toSubmodule d.pair.second.toSubmodule
      hfirst_stable d.specified.swap hsub_ne hdim
  have htop : φ.range = ⊤ := actorConjugation_range_top_of_outer d.K eK
    d.specified.actor (inner_le_actorConjugation_range d.K eK) houter psl_inner_index
  have hφ_inj : Function.Injective φ := actorConjugation_injective d.K eK hcentral
  have hφ_surj : Function.Surjective φ := by
    intro x
    have hx : x ∈ φ.range := by rw [htop]; trivial
    exact hx
  let eActor : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.PSL :=
    MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have heActor_apply (a : ActorQuotient Z) : eActor a = φ a := rfl
  letI : IsElementaryAbelian 2 d.elementary_subgroup := d.elementary_instance
  letI : IsExtraspecial 2 (closureU Z ZS) := d.extraspecial_instance
  refine {
    s_eq_one := hs
    first_singular := hsing₁
    second_singular := hsing₂
    non_self_equivalent := hne
    dual_pairing := hdual
    transitive := htrans
    centralizer_trivial := hcentral
    actor_equiv := eActor
    actor_inner := ?_
    specified_t_mem := d.specified.t_mem
    specified_t_outside := d.specified.t_outside
    specified_actor_eq := d.specified.actor_eq
    specified_interchange := d.specified.swap
    specified_outer := by
      rw [heActor_apply]
      exact houter
    extraspecial_equiv :=
      DihedralCentralProductThree.equivOfElementarySixteen d.U_card
        d.elementary_subgroup d.elementary_card d.center_in_elementary }
  apply le_antisymm
  · rintro x ⟨k, hk, rfl⟩
    refine ⟨eK ⟨k, hk⟩, ?_⟩
    change MulAut.conj (eK ⟨k, hk⟩) = eActor (k : ActorQuotient Z)
    rw [heActor_apply]
    exact (actorConjugation_on_normal d.K eK ⟨k, hk⟩).symm
  · rintro x ⟨a, rfl⟩
    obtain ⟨k, rfl⟩ := eK.surjective a
    refine ⟨(k : ActorQuotient Z), k.property, ?_⟩
    change eActor (k : ActorQuotient Z) = MulAut.conj (eK k)
    rw [heActor_apply]
    exact actorConjugation_on_normal d.K eK k

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
