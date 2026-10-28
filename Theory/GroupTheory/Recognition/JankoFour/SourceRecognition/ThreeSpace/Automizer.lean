module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.SourceData
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The full three-space action and the first source quotient

The actual normalizer is transitive on the seven nonzero points. Its image
contains nontrivial two- and three-elements from the original core and cubic
Sylow. Thus its order is divisible by 42. Simplicity and the order 168 of
Aut(Z)=GL₃(2) exclude a proper image. The source join K is relatively normal
and has nontrivial image, so it also induces all Aut(Z). Its literal kernel
is R=K∩C_G(Z), proving K/R≅L₃(2) and the actual product N_G(Z)=KS.

Every three-space premise is constructed by `source_three_space_data` from
the genuine type-J₄ hypotheses. The final theorem makes this discharge
explicit, preserving the full cubic quotient and its Sylow. No ambient J₄
simplicity, PointData or recognition implication is assumed.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
This proves the normalizer product and K/R clause. The assertions
R=O₂(K)=O₂(S), specialness, S/R≅S₅ and the tensor module remain separate
obligations; they are not consequences claimed by this module.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

private theorem aut_eight_simple {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) : IsSimpleGroup (MulAut E) := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hE
  exact e.isSimpleGroup

private theorem aut_eight_full {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (A : Subgroup (MulAut E)) (h2 : 2 ∣ Nat.card A) (h3 : 3 ∣ Nat.card A)
    (h7 : 7 ∣ Nat.card A) : A = ⊤ := by
  let := aut_eight_simple hE
  have h42 : 42 ∣ Nat.card A := Nat.lcm_dvd (Nat.lcm_dvd h2 h3) h7
  have hge := Nat.le_of_dvd Nat.card_pos h42
  have hc := A.card_mul_index
  rw [card_mulAut_of_elementary_eight E hE] at hc
  have hi : A.index ≤ 4 := by nlinarith
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hf := Nat.factorial_le hi
  rw [card_mulAut_of_elementary_eight E hE]
  norm_num [Nat.factorial] at hf ⊢
  omega

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
namespace ThreeSpaceData
variable (d : ThreeSpaceData z e X)

def normalizerAction : normalizer (d.space : Set G) →* MulAut d.space :=
  d.space.normalizerMonoidHom

private theorem z_mem_space : z ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)

private theorem r_mem_space : d.r ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)

private theorem space_le_core : d.space ≤ ambientCore z := inf_le_left.trans inf_le_left

private theorem normalizerAction_seven (h : IsTypeJ4 z) :
    7 ∣ Nat.card d.normalizerAction.range := by
  classical
  let A := d.normalizerAction.range
  let z₀ : d.space := ⟨z,d.z_mem_space⟩
  have hz₀ : z₀ ≠ 1 := by
    intro he
    have hz1 := congrArg Subtype.val he
    have hi := h.involution
    simp [show z = 1 from hz1] at hi
  have horbit : MulAction.orbit A z₀ = {t : d.space | t ≠ 1} := by
    ext t
    constructor
    · rintro ⟨a,ha⟩ he
      apply hz₀
      apply a.val.injective
      exact ha.trans (he.trans a.val.map_one.symm)
    · intro ht
      obtain ⟨n,hn,he⟩ := d.normalizer_transitive t.val t.property
        (fun he => ht (Subtype.ext he))
      let n₀ : normalizer (d.space : Set G) := ⟨n,hn⟩
      exact ⟨⟨d.normalizerAction n₀,⟨n₀,rfl⟩⟩,Subtype.ext he⟩
  have hc : Nat.card (MulAction.orbit A z₀) = 7 := by
    rw [horbit]
    let : Fintype d.space := Fintype.ofFinite d.space
    change Nat.card {t : d.space // t ≠ 1} = 7
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,show Nat.card d.space=8 from d.card]
  have ho := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A z₀)
  rw [Nat.card_prod,hc] at ho
  exact ⟨_,ho.symm⟩

private theorem normalizerAction_cubic (h : IsTypeJ4 z) :
    3 ∣ Nat.card d.normalizerAction.range := by
  let U := (cubicSylowImage e X).map (centralizer z).subtype
  have hUN : U ≤ normalizer (d.space : Set G) := d.cubic_normalizes
  let f : U →* MulAut d.space := d.normalizerAction.comp (inclusion hUN)
  have hU : Nat.card U = 3 := by
    rw [card_map_of_injective (centralizer z).subtype_injective,cubicSylowImage,
      card_map_of_injective (LocalGeometry.CubicLift.subgroup e).subtype_injective]
    exact cubicSylow_card e h X
  have hne : f.range ≠ ⊥ := by
    intro he
    have hcomm : ⁅zpowers d.r,U⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply zpowers_le.mpr
      intro u hu
      have hfu : f ⟨u,hu⟩ = 1 := by
        apply mem_bot.mp
        rw [← he]
        exact ⟨_,rfl⟩
      have hh := congrArg (fun a : MulAut d.space => (a ⟨d.r,d.r_mem_space⟩ : G)) hfu
      change u*d.r*u⁻¹=d.r at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hz := d.cubic_commutator
    change d.space = zpowers z ⊔ ⁅zpowers d.r,U⁆ at hz
    rw [hcomm,sup_bot_eq] at hz
    have hc := d.card
    change Nat.card d.space=8 at hc
    rw [hz,Nat.card_zpowers,h.involution] at hc
    omega
  have hc : Nat.card f.range = 3 := by
    have hd : Nat.card f.range ∣ 3 := hU ▸ card_range_dvd f
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left
      (fun hc => hne ((eq_bot_iff_card _).mpr hc))
  have hle : f.range ≤ d.normalizerAction.range := by
    rintro _ ⟨u,rfl⟩
    exact ⟨inclusion hUN u,rfl⟩
  exact hc ▸ card_dvd_of_le hle

private theorem normalizerAction_even (h : IsTypeJ4 z) :
    2 ∣ Nat.card d.normalizerAction.range := by
  have hz1 : z ≠ 1 := fun he => by have hi := h.involution; simp [he] at hi
  have hQN : ambientCore z ≤ normalizer (d.space : Set G) :=
    d.cores_normalize z d.z_mem_space hz1
  let f : ambientCore z →* MulAut d.space := d.normalizerAction.comp (inclusion hQN)
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := isConj_iff.mp d.r_conj
    rw [he] at hg
    exact hz1 ((MulAut.conj g).injective (hg.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨q,hq,he⟩ := exists_core_flip h d.r_mem hr1 d.r_ne
  have hne : f.range ≠ ⊥ := by
    intro heq
    have hfq : f ⟨q,hq⟩ = 1 := mem_bot.mp (heq ▸ (show f ⟨q,hq⟩ ∈ f.range from ⟨_,rfl⟩))
    have hh := congrArg (fun a : MulAut d.space => (a ⟨d.r,d.r_mem_space⟩ : G)) hfq
    change q*d.r*q⁻¹=d.r at hh
    rw [he] at hh
    exact hz1 (mul_right_cancel (hh.trans (one_mul d.r).symm))
  let : IsExtraspecial 2 (ambientCore z) :=
    IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  have hp : IsPGroup 2 f.range := (IsExtraspecial.isPGroup 2 (ambientCore z)).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have h2 : 2 ∣ Nat.card f.range := hp.card_eq_or_dvd.resolve_left
    (fun hc => hne ((eq_bot_iff_card _).mpr hc))
  have hle : f.range ≤ d.normalizerAction.range := by
    rintro _ ⟨u,rfl⟩
    exact ⟨inclusion hQN u,rfl⟩
  exact h2.trans (card_dvd_of_le hle)

/-- The actual three-space normalizer induces every automorphism of Z. -/
theorem normalizerAction_surjective (h : IsTypeJ4 z) : Function.Surjective d.normalizerAction := by
  let : IsElementaryAbelian 2 d.space := d.elementary
  apply MonoidHom.range_eq_top.mp
  exact aut_eight_full (show Nat.card d.space=8 from d.card) d.normalizerAction.range
    (d.normalizerAction_even h) (d.normalizerAction_cubic h) (d.normalizerAction_seven h)

/-- Conjugation by the source join K on its common three-space. -/
def KAction : d.K →* MulAut d.space := d.normalizerAction.comp (inclusion d.K_le_normalizer)

private theorem core_le_K (h : IsTypeJ4 z) : ambientCore z ≤ d.K := by
  apply core_le_threeSpaceCores d.space d.z_mem_space
  intro he
  have hi := h.involution
  simp [he] at hi

/-- The source K induces the full linear three-group, not just a transitive subgroup. -/
theorem KAction_surjective (h : IsTypeJ4 z) : Function.Surjective d.KAction := by
  let : IsElementaryAbelian 2 d.space := d.elementary
  let := aut_eight_simple (show Nat.card d.space=8 from d.card)
  let H := d.K.subgroupOf (normalizer (d.space : Set G))
  have hmap : H.map d.normalizerAction = d.KAction.range := by
    ext a
    constructor
    · rintro ⟨n,hn,he⟩
      exact ⟨⟨n.val,hn⟩,he⟩
    · rintro ⟨k,hk⟩
      exact ⟨inclusion d.K_le_normalizer k,k.property,hk⟩
  have hn : d.KAction.range.Normal := hmap ▸
    (d.K_normal.map d.normalizerAction (d.normalizerAction_surjective h))
  apply MonoidHom.range_eq_top.mp
  apply hn.eq_bot_or_eq_top.resolve_left
  intro hb
  have hz1 : z ≠ 1 := fun he => by have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := isConj_iff.mp d.r_conj
    rw [he] at hg
    exact hz1 ((MulAut.conj g).injective (hg.trans (map_one (MulAut.conj g)).symm))
  obtain ⟨q,hq,he⟩ := exists_core_flip h d.r_mem hr1 d.r_ne
  let q₀ : d.K := ⟨q,d.core_le_K h hq⟩
  have hfq : d.KAction q₀ = 1 := mem_bot.mp (hb ▸ (show d.KAction q₀ ∈ d.KAction.range from ⟨_,rfl⟩))
  have hh := congrArg (fun a : MulAut d.space => (a ⟨d.r,d.r_mem_space⟩ : G)) hfq
  change q*d.r*q⁻¹=d.r at hh
  rw [he] at hh
  exact hz1 (mul_right_cancel (hh.trans (one_mul d.r).symm))

/-- The source centralizer S=C_G(Z). -/
def S : Subgroup G := Subgroup.centralizer (d.space : Set G)

/-- The literal intersection R=K∩S. -/
def R : Subgroup G := d.K ⊓ d.S

/-- The action retains exactly the centralizer kernel from the source. -/
theorem KAction_ker : d.KAction.ker = d.R.subgroupOf d.K := by
  ext k
  change d.KAction k = 1 ↔ (k : G) ∈ d.K ⊓ d.S
  rw [Subgroup.mem_inf,and_iff_right k.property]
  constructor
  · intro he y hy
    have hh := congrArg (fun a : MulAut d.space => (a ⟨y,hy⟩ : G)) he
    change (k : G)*y*(k : G)⁻¹=y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hk
    ext y
    change (k : G)*(y : G)*(k : G)⁻¹=(y : G)
    rw [← hk y y.property,mul_inv_cancel_right]

theorem R_normal_in_K : (d.R.subgroupOf d.K).Normal := by
  rw [← d.KAction_ker]
  infer_instance

/-- The concrete K/R identification is induced by the actual conjugation map. -/
noncomputable def KQuotientEquivAut (h : IsTypeJ4 z) :
    letI := d.R_normal_in_K
    (d.K ⧸ d.R.subgroupOf d.K) ≃* MulAut d.space := by
  letI := d.R_normal_in_K
  exact (QuotientGroup.quotientMulEquivOfEq d.KAction_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.KAction (d.KAction_surjective h))

/-- The quotient equivalence uses the original conjugation map on every representative. -/
@[simp] theorem KQuotientEquivAut_mk (h : IsTypeJ4 z) (k : d.K) :
    letI := d.R_normal_in_K
    d.KQuotientEquivAut h (QuotientGroup.mk' (d.R.subgroupOf d.K) k) = d.KAction k := by
  rfl

/-- The first quotient in AS91 (4.4), on the literal source K and R. -/
theorem K_quotient_PSL3 (h : IsTypeJ4 z) :
    letI := d.R_normal_in_K
    Nonempty ((d.K ⧸ d.R.subgroupOf d.K) ≃* Matrix.PSL3Two.PSL) := by
  let : IsElementaryAbelian 2 d.space := d.elementary
  let := d.R_normal_in_K
  obtain ⟨e₀⟩ := MulAut.elementaryEight_equiv_PSL3 (show Nat.card d.space=8 from d.card)
  exact ⟨(d.KQuotientEquivAut h).trans e₀⟩

/-- Each member of N_G(Z) is an actual product of a member of K and a
member of S=C_G(Z), in the source order. -/
theorem normalizer_product (h : IsTypeJ4 z) (n : G) (hn : n ∈ normalizer (d.space : Set G)) :
    ∃ k ∈ d.K, ∃ s ∈ d.S, k*s=n := by
  let n₀ : normalizer (d.space : Set G) := ⟨n,hn⟩
  obtain ⟨k,hk⟩ := d.KAction_surjective h (d.normalizerAction n₀)
  let k₀ : normalizer (d.space : Set G) := inclusion d.K_le_normalizer k
  have he : d.normalizerAction k₀ = d.normalizerAction n₀ := hk
  have hm : k₀⁻¹*n₀ ∈ d.normalizerAction.ker := by
    change d.normalizerAction (k₀⁻¹*n₀)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  change k₀⁻¹*n₀ ∈ d.space.normalizerMonoidHom.ker at hm
  rw [normalizerMonoidHom_ker] at hm
  refine ⟨k,k.property,(k:G)⁻¹*n,hm,?_⟩
  group

/-- The source product equality also gives the corresponding subgroup join. -/
theorem normalizer_eq_K_sup_S (h : IsTypeJ4 z) :
    normalizer (d.space : Set G) = d.K ⊔ d.S := by
  apply le_antisymm
  · intro n hn
    obtain ⟨k,hk,s,hs,rfl⟩ := d.normalizer_product h n hn
    exact (d.K ⊔ d.S).mul_mem ((le_sup_left : d.K ≤ d.K ⊔ d.S) hk)
      ((le_sup_right : d.S ≤ d.K ⊔ d.S) hs)
  · exact sup_le d.K_le_normalizer (Subgroup.centralizer_le_normalizer _)

end ThreeSpaceData

/-- Construct the literal source local groups and their proved quotient/product
clauses with no extra geometric or recognition premise. -/
theorem source_three_space_local_groups (h : IsTypeJ4 z) :
    ∃ (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
      (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) (d : ThreeSpaceData z e X),
      Function.Surjective d.normalizerAction ∧ Function.Surjective d.KAction ∧
      normalizer (d.space : Set G) = d.K ⊔ d.S ∧
      (letI := d.R_normal_in_K
       Nonempty ((d.K ⧸ d.R.subgroupOf d.K) ≃* Matrix.PSL3Two.PSL)) := by
  obtain ⟨e,X,⟨d⟩⟩ := source_three_space_data_exists h
  exact ⟨e,X,d,d.normalizerAction_surjective h,d.KAction_surjective h,
    d.normalizer_eq_K_sup_S h,d.K_quotient_PSL3 h⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
