module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The initial centralizer structure in the proper PSL₂ branch

Let A be the original distinguished closure, L the proper marked PSL₂ subgroup,
D the pair stabilizer, J=C_G(L), and C₀=C_M(A). The pointwise Sylow automorphism
lemma gives C_{N_G(L)}(A)=AJ. Since A meets D trivially and J lies in D,
this identifies C₀∩D with J. Relative normality of C₀ in M and the original
coset degree q³+1 then give [C₀:J] dividing q³.

If J is a two-group, so is C₀; its normality puts it inside O₂(M). An
involution in the even group J therefore belongs to O₂(M) and lies outside A.
This completes the two-group J branch of the source Lemma 15.3 without
assuming the later conclusion |J|=2. The odd-order part of that lemma,
the nontrivial two-core of J, and the full TI/counting argument remain open.

All results use the original Context, subgroups and model parameter. The
normality assertion is inside M. This module imports the existing pointwise
root calculation directly and introduces no replacement local hypotheses.

Source: GLS, Volume 4, Chapter 2, Lemma 15.2(d,e), equation (15B), and the
first case of Lemma 15.3, in refs/KGroup/GLS4/Chapter2.tex, Section 15.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "J" => centralizer (L : Set G)
local notation "C₀" => M ⊓ centralizer (A : Set G)

private theorem centralizer_le_pair : J ≤ D :=
  centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M

private theorem distinguished_disjoint_pair : Disjoint A D := by
  apply disjoint_def.mpr
  intro a ha hd
  by_contra hne
  have hsq : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.distinguished_elementary_card.1.exponent_dvd_p ⟨a, ha⟩)
  have hi : PFAppendixIII.IsInvolution a := ⟨hne, hsq⟩
  have hzA := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp hi
  exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
    d.t_not_mem_M hd hzA

/-- The pointwise centralizer of the actual distinguished root in N_GL. -/
public theorem Context.normalizer_inf_centralizer_eq :
    normalizer (L : Set G) ⊓ centralizer (A : Set G) = A ⊔ J := by
  apply le_antisymm
  · exact linear_normalizer_inf_centralizer_le d.minimal.disconnected d.reduction
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.parameter d.model
      d.distinguished_le
  · have hAA : A ≤ centralizer (A : Set G) := by
      apply le_centralizer_iff_isMulCommutative.mpr
      let := d.distinguished_elementary_card.1
      infer_instance
    exact sup_le (le_inf (d.distinguished_le.trans (L).le_normalizer) hAA)
      (le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le d.distinguished_le))

/-- Lemma 15.2(e), with C₀=C_M(A) and the original pair stabilizer. -/
public theorem Context.centralizer_pair_eq : C₀ ⊓ D = J := by
  apply le_antisymm
  · intro x hx
    have hs : x ∈ A ⊔ J := d.normalizer_inf_centralizer_eq ▸
      (show x ∈ normalizer (L : Set G) ⊓ centralizer (A : Set G) from
        ⟨d.pair_normalizes hx.2, hx.1.2⟩)
    have hnorm : J ≤ normalizer (A : Set G) :=
      (centralizer_le d.distinguished_le).trans (Subgroup.centralizer_le_normalizer _)
    have hset := coe_mul_of_right_le_normalizer_left A J hnorm
    have hxprod : x ∈ (A : Set G) * (J : Set G) := (Set.ext_iff.mp hset x).mp hs
    obtain ⟨a, ha, j, hj, he⟩ := hxprod
    change a * j = x at he
    have haD : a ∈ D := by
      have hh := (D).mul_mem hx.2 ((D).inv_mem (centralizer_le_pair d hj))
      rw [← he, mul_inv_cancel_right] at hh
      exact hh
    have ha1 := disjoint_def.mp (distinguished_disjoint_pair d) ha haD
    rw [ha1, one_mul] at he
    exact he ▸ hj
  · exact le_inf
      (le_inf ((centralizer_le_pair d).trans inf_le_left)
        (centralizer_le d.distinguished_le))
      (centralizer_le_pair d)

omit [Finite G] d in
private theorem centralizer_subgroupOf :
    (C₀).subgroupOf M = centralizer ((A).subgroupOf M : Set M) := by
  ext x
  constructor
  · intro hx a ha
    exact Subtype.ext (mem_centralizer_iff.mp hx.2 a ha)
  · intro hx
    refine ⟨x.property, ?_⟩
    intro a ha
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx
      ⟨a, distinguishedClosure_le ha⟩ ha)

/-- The source C₀ is normal in M, with no ambient normality assertion. -/
public theorem Context.centralizer_normal : ((C₀).subgroupOf M).Normal := by
  rw [centralizer_subgroupOf (Z := Z) (M := M)]
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  infer_instance

private theorem pair_index : (D).relIndex M = (2 ^ n) ^ 3 := by
  have hm := linear_stabilizer_card_of_degree d.action d.t_not_mem_M
    d.degree_and_fixed.1
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) D M bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left] at hi
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card D)
  exact hi.trans (hm.trans (Nat.mul_comm _ _))

/-- The source index bound (15B), before either the two-core or order-two
centralizer conclusion. -/
public theorem Context.centralizer_index_dvd : (J).relIndex C₀ ∣ (2 ^ n) ^ 3 := by
  let C : Subgroup M := (C₀).subgroupOf M
  let E : Subgroup M := (D).subgroupOf M
  let : C.Normal := d.centralizer_normal
  have hnorm : E ≤ normalizer (C : Set M) := le_normalizer_of_normal
  have hs := relIndex_sup_of_normalizes C E hnorm
  have hd : E.relIndex C ∣ E.index := by
    rw [← hs]
    exact relIndex_dvd_index_of_le le_sup_right
  have he : E.relIndex C = (J).relIndex C₀ := by
    rw [relIndex_subgroupOf (show C₀ ≤ M from inf_le_left)]
    rw [← inf_relIndex_left, d.centralizer_pair_eq]
  have hi : E.index = (2 ^ n) ^ 3 := pair_index d
  rwa [he, hi] at hd

/-- The two-group branch of Lemma 15.3 starts with C₀ itself a two-group. -/
public theorem Context.centralizer_isPGroup_of_isPGroup
    (hJ : IsPGroup 2 J) : IsPGroup 2 (C₀ : Subgroup G) := by
  obtain ⟨k, hk⟩ := hJ.exists_card_eq
  have hJC : J ≤ C₀ := le_inf ((centralizer_le_pair d).trans inf_le_left)
    (centralizer_le d.distinguished_le)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) J C₀ bot_le hJC
  rw [relIndex_bot_left, relIndex_bot_left, hk] at hc
  apply IsPGroup.of_card_dvd_pow (n := k + n * 3)
  rw [← hc, pow_add, pow_mul]
  exact Nat.mul_dvd_mul_left _ d.centralizer_index_dvd

/-- Actual source application: if J is a two-group, O₂(M) has an involution
outside A. Thus Ω₁(O₂(M))=A is impossible in this branch of Lemma 15.3. -/
public theorem Context.twoCore_involution_outside_distinguished_of_isPGroup
    (hJ : IsPGroup 2 J) :
    ∃ v : M, v ∈ pCore 2 M ∧ PFAppendixIII.IsInvolution v ∧ (v : G) ∉ A := by
  let C : Subgroup M := (C₀).subgroupOf M
  let : C.Normal := d.centralizer_normal
  have hC : IsPGroup 2 C := (d.centralizer_isPGroup_of_isPGroup hJ).of_equiv
    (subgroupOfEquivOfLe (show C₀ ≤ M from inf_le_left)).symm
  have hcore : C ≤ pCore 2 M := le_sSup ⟨inferInstance, hC⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 d.centralizer_even.two_dvd
  have hvJ : PFAppendixIII.IsInvolution v := (orderOf_eq_prime_iff.mp hv).symm
  have hvG : PFAppendixIII.IsInvolution (v : G) :=
    BenderSuzuki.IsInvolution.map_of_injective hvJ (J).subtype Subtype.val_injective
  let w : M := ⟨v, ((centralizer_le_pair d).trans inf_le_left) v.property⟩
  refine ⟨w, hcore ?_, BenderSuzuki.IsInvolution.subtype hvG w.property, ?_⟩
  · exact ⟨w.property, (centralizer_le d.distinguished_le) v.property⟩
  · intro ha
    exact hvG.ne_one (disjoint_def.mp (distinguished_disjoint_pair d) ha
      (centralizer_le_pair d v.property))

end BenderSuzuki.ZD.LinearExclusion
