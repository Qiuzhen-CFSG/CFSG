module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.PGroup.ElementaryNormalizer
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Prime-23 placement of Sylow overgroups in the native J₄ model

Both actual involution centralizers have order prime to 23. Consequently an
element of order 23 acts without nonidentity fixed points on a normal
nontrivial elementary two-subgroup E. Its conjugation orbits give |E| ≡ 1
modulo 23, forcing |E| ≥ 2048. Aligning the given Sylow with one in max1,
the certified elementary-subgroup bound identifies E with the literal
Mathieu kernel. The certified ambient normalizer then places the entire
overgroup inside a conjugate of max1.

Every two-local has a nontrivial two-core, so this proves placement for the
actual two-local used by the M₂₃ consumer, with no classification premise.
For an arbitrary maximal Sylow overgroup the same proof gives the requested
isomorphism conditional on a nontrivial two-core. The final structural
contract below remains unproved; no arbitrary maximal-overgroup coverage
is asserted here.

Source context: Aschbacher–Smith A.3.12(17), printed pp.47–48, citing
Aschbacher, *Overgroups of Sylow subgroups in sporadic groups*, Memoirs AMS
60 (1986), no.343. GLS3 Table 5.3i describes the local groups. The normal
large-subgroup recognition is adapted at Theory level from the existing
`Max1Placement/Existence/SylowCover/Branches.lean` proof. All model facts
used here come from the checked native matrix, action and normalizer proofs;
no table entry supplies a proof premise.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Janko4.SylowOvergroups
open Janko4.Cardinality Janko4.LocalStructure
attribute [local irreducible] Janko4.modelGroup matrixA matrixB max1Subgroup localKernel

private theorem max1_ne_top : SylowCore.Local ≠ (⊤ : Subgroup Model) := by
  intro h
  have hd : 37 ∣ Nat.card SylowCore.Local := by
    have ha : Janko4.a * Janko4.b ∈ SylowCore.Local := h ▸ mem_top _
    have hd := orderOf_dvd_natCard (⟨Janko4.a * Janko4.b, ha⟩ : SylowCore.Local)
    rwa [← orderOf_coe, orderOf_a_mul_b] at hd
  rw [max1Subgroup_card] at hd
  norm_num at hd

/-- The literal local Sylow can be aligned with any supplied ambient Sylow. -/
private theorem max1_sylow_alignment (S : Sylow 2 Model) :
    ∃ (P : Sylow 2 SylowCore.Local) (g : Model),
      P.toSubgroup.map ((MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype) =
        S.toSubgroup := by
  let P : Sylow 2 SylowCore.Local := default
  have hi : ¬ 2 ∣ (P.toSubgroup.map SylowCore.Local.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index
      Janko4.OuterReduction.max1_odd_index_unconditional
  let T := (P.isPGroup'.map SylowCore.Local.subtype).toSylow hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T S
  refine ⟨P, g, ?_⟩
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

/-- A normal elementary subgroup of order at least 2048 places a Sylow overgroup
in a conjugate of the literal Mathieu subgroup. The uniqueness bound is used on the actual aligned Sylow subgroup. -/
theorem normal_large_placement (S : Sylow 2 Model) (M : Subgroup Model)
    (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : 2048 ≤ Nat.card E) :
    ∃ g : Model, M ≤ SylowCore.Local.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, g, hPS⟩ := max1_sylow_alignment S
  let j : SylowCore.Local →* Model :=
    (MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp Subtype.val_injective
  let f : P →* M := (j.comp P.toSubgroup.subtype).codRestrict M (by
    intro p
    apply hSM
    rw [← hPS]
    exact mem_map_of_mem _ p.property)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hj (congrArg Subtype.val hxy))
  have hEP : E ≤ (S.subtype hSM).toSubgroup :=
    (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal _
  have hErange : E ≤ f.range := by
    intro e he
    have heS : (e : Model) ∈ S.toSubgroup := hEP he
    rw [← hPS] at heS
    obtain ⟨p, hp, heq⟩ := heS
    exact ⟨⟨p, hp⟩, Subtype.ext heq⟩
  let A : Subgroup P := E.comap f
  let eA : A ≃* E := MulEquiv.ofBijective (f.subgroupComap E) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hf (congrArg Subtype.val hxy))
    · intro e
      obtain ⟨p, hp⟩ := hErange e.property
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      change f p ∈ E
      rw [hp]
      exact e.property)
  have hAelem : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y => eA.injective
      ((eA.map_mul x y).trans ((mul_comm _ _).trans (eA.map_mul y x).symm))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      eA.injective (by
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) (eA x))) }
  let := hAelem
  have hAcard : 2048 ≤ Nat.card A := hE.trans_eq (Nat.card_congr eA.toEquiv).symm
  have hA : A = SylowCore.core P :=
    localKernel_sylow_unique_of_quotientCentralizerBound
      (SylowCore.quotientCentralizerBound_of_fixedBound SylowCore.normalElementaryFixedBound)
      P A hAcard
  have hmaps : (E.map M.subtype) =
      (localKernel matrixA_mul_self matrixB_pow_four).map j := by
    have hAf : A.map f = E := by
      exact map_comap_eq_self hErange
    have heq := congrArg (fun K : Subgroup M => K.map M.subtype) hAf
    rw [map_map] at heq
    have hcomp : M.subtype.comp f = j.comp P.toSubgroup.subtype := rfl
    rw [hcomp, ← map_map, hA, map_subgroupOf_eq_of_le (localKernel_le_sylow P)] at heq
    exact heq.symm
  have hMN : M ≤ normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map j : Set Model) := by
    rw [← hmaps]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map M.subtype
  have hN : normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map j : Set Model) ≤
      SylowCore.Local.map (MulAut.conj g).toMonoidHom := by
    change normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map
      ((MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype) : Set Model) ≤ _
    rw [← map_map, ← map_equiv_normalizer_eq]
    exact map_mono normalizer_embedded_localKernel_le_max1
  exact ⟨g, hMN.trans hN⟩

/-- A normal elementary subgroup of order at least 2048 forces the literal Mathieu
branch. The uniqueness bound is used on the actual aligned Sylow subgroup. -/
theorem normal_large_recognition (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : 2048 ≤ Nat.card E) : Nonempty (M ≃* (max1Subgroup matrixA_mul_self matrixB_pow_four)) := by
  obtain ⟨g, hMg⟩ := normal_large_placement S M hSM E hE
  have hproper : SylowCore.Local.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro ht
    apply max1_ne_top
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [ht, map_top_of_surjective _ (MulAut.conj g).surjective]
  have heq : SylowCore.Local.map (MulAut.conj g).toMonoidHom = M :=
    (hM.le_iff_eq hproper).mp hMg
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans
    ((MulAut.conj g).subgroupMap SylowCore.Local).symm⟩

/-- Neither of the two actual involution centralizers has a factor 23. -/
theorem involution_centralizer_not_dvd_twentyThree
    (z : Model) (hz : orderOf z = 2) :
    ¬ 23 ∣ Nat.card (centralizer ({z} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, InvolutionCentralizers.Second.ambient_card]
    norm_num

/-- An element of order 23 fixes no nonidentity element of a normal elementary
two-subgroup. Orbit counting and the powers of two below 2048 give this bound. -/
theorem normal_elementary_card_ge_of_twentyThree
    (M : Subgroup Model) (h23 : 23 ∣ Nat.card M)
    (E : Subgroup M) [E.Normal] [IsElementaryAbelian 2 E] (hE : E ≠ ⊥) :
    2048 ≤ Nat.card E := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 23 h23
  have hp : IsPGroup 23 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)
  have hfixed : E ⊓ centralizer (zpowers x : Set M) = ⊥ := by
    apply bot_unique
    intro z hz
    apply mem_bot.mpr
    by_contra hzne
    have hzpow : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz.1
    have hzord : orderOf (z : Model) = 2 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨congrArg M.subtype hzpow, fun h => hzne (Subtype.ext h)⟩
    have hxC : (x : Model) ∈ centralizer ({(z : Model)} : Set Model) := by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg M.subtype (hz.2 x (mem_zpowers x))
    have hxc : orderOf (⟨(x : Model), hxC⟩ :
        centralizer ({(z : Model)} : Set Model)) = 23 := by
      exact (orderOf_coe _).symm.trans ((orderOf_coe x).trans hx)
    exact involution_centralizer_not_dvd_twentyThree z hzord
      (hxc ▸ orderOf_dvd_natCard (⟨(x : Model), hxC⟩ :
        centralizer ({(z : Model)} : Set Model)))
  have hmod := card_modEq_card_inf_centralizer (zpowers x) E hp
    (show zpowers x ≤ normalizer (E : Set M) by rw [normalizer_eq_top]; exact le_top)
  rw [hfixed, card_bot] at hmod
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 E))
  rw [hn] at hmod ⊢
  have hpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    exact hE (card_eq_one.mp (by simpa [he] using hn))
  by_contra hlarge
  have hlt : n < 11 := by
    by_contra h
    have hge : 11 ≤ n := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hge
    norm_num at hpow
    omega
  interval_cases n <;> norm_num [Nat.ModEq] at hmod

/-- A nontrivial two-core supplies the elementary subgroup needed by the
prime-23 orbit count and the native max1 recognition. -/
theorem maximal_equiv_max1_of_twentyThree_of_twoCore_ne_bot
    (T : Sylow 2 Model) (M : Subgroup Model) (hM : IsCoatom M)
    (hTM : T.toSubgroup ≤ M) (h23 : 23 ∣ Nat.card M)
    (hcore : pCore 2 M ≠ ⊥) :
    Nonempty (M ≃* Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) := by
  obtain ⟨E, hE, _, hElem, hnorm⟩ :=
    (pCore 2 M).exists_nontrivial_elementary_with_normalizer_le pCore_isPGroup hcore
  let := hElem
  have hEn : E.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    simpa only [normalizer_eq_top] using hnorm)
  let := hEn
  exact normal_large_recognition T M hM hTM E
    (normal_elementary_card_ge_of_twentyThree M h23 E hE)


/-- Prime-23 Sylow overgroups with a nontrivial two-core lie in a conjugate
of the literal Mathieu subgroup, without a maximality assumption. -/
theorem le_conjugate_max1_of_twentyThree_of_twoCore_ne_bot
    (T : Sylow 2 Model) (M : Subgroup Model)
    (hTM : T.toSubgroup ≤ M) (h23 : 23 ∣ Nat.card M)
    (hcore : pCore 2 M ≠ ⊥) :
    ∃ g : Model, M ≤ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).map
      (MulAut.conj g).toMonoidHom := by
  obtain ⟨E, hE, _, hElem, hnorm⟩ :=
    (pCore 2 M).exists_nontrivial_elementary_with_normalizer_le pCore_isPGroup hcore
  let := hElem
  have hEn : E.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    simpa only [normalizer_eq_top] using hnorm)
  let := hEn
  exact normal_large_placement T M hTM E
    (normal_elementary_card_ge_of_twentyThree M h23 E hE)

/-- A two-local already has the nontrivial two-core required for placement.
This applies directly to the local subgroup constructed in A.3.12's M₂₃ case. -/
theorem twoLocal_le_conjugate_max1_of_twentyThree
    (T : Sylow 2 Model) (M : Subgroup Model)
    (hlocal : IsTwoLocal M)
    (hTM : T.toSubgroup ≤ M) (h23 : 23 ∣ Nat.card M) :
    ∃ g : Model, M ≤ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).map
      (MulAut.conj g).toMonoidHom := by
  apply le_conjugate_max1_of_twentyThree_of_twoCore_ne_bot T M hTM h23
  obtain ⟨Q, hQ, hQtwo, rfl⟩ := hlocal
  exact pCore_ne_bot_of_normalized_nontrivial (normalizer (Q : Set Model)) Q
    Q.le_normalizer hQtwo hQ le_rfl

/-- The remaining structural source input: a maximal Sylow overgroup with
order divisible by 23 has a nontrivial intrinsic two-core. This definition
asserts no existence or maximal-overgroup coverage. -/
@[expose] def PrimeTwentyThreeCoreNontrivial : Prop :=
  ∀ (T : Sylow 2 Model) (M : Subgroup Model),
    IsCoatom M → T.toSubgroup ≤ M → 23 ∣ Nat.card M → pCore 2 M ≠ ⊥

/-- The structural core input suffices for the requested native placement.
The unconditional source theorem still requires that input to be proved. -/
theorem maximal_equiv_max1_of_twentyThree_of_coreNontrivial
    (hcore : PrimeTwentyThreeCoreNontrivial)
    (T : Sylow 2 Model) (M : Subgroup Model) (hM : IsCoatom M)
    (hTM : T.toSubgroup ≤ M) (h23 : 23 ∣ Nat.card M) :
    Nonempty (M ≃* Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) :=
  maximal_equiv_max1_of_twentyThree_of_twoCore_ne_bot T M hM hTM h23
    (hcore T M hM hTM h23)

end Janko4.SylowOvergroups
