module
public import Stellmacher.SectionNine.NineFiveCanonicalPair
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove
public import Stellmacher.SectionOne.OneSevenSupportTransitivity
public import Theory.GroupAction.ActorSubtypeCommutator
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The selected displacement-point stabilizer in (9.9)

For the literal faithful Section One action on a module of order sixteen,
assume the acting group has order seventy-two. A selected canonical factor
contains an involution of the supplied Sylow two-subgroup whose displacement
has order two. The stabilizer of its nonidentity displacement point has
order twelve, meets that Sylow subgroup in order four, and therefore has
relative index three over the intersection. The supplied action is retained
throughout, so the result applies directly to the actual quotient module.

The Sylow subgroup has order eight and hence moves the selected factor
support to a complementary canonical support. Those two factors exhaust the
canonical family. Intrinsic factor-support transitivity makes the full
point orbit the six nonidentity points of their two order-four supports.
The Sylow intersection with the selected factor is precisely the actor's
order-two subgroup. Its factor-normalizer therefore preserves the selected
displacement line and fixes its unique nonidentity point. The Sylow point
orbit consists of that point and its exchanged image, so has order two.
The two orbit-stabilizer identities give the asserted cardinalities and
relative index.

This supplies the normalizer index calculation for X in Stellmacher (9.9),
printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`. The passage
from point stabilizer to the ambient graph-group normalizer is a separate
consumer, using the actual quotient map and order-two line.
-/

namespace Stellmacher.SectionNine
open SectionOne
universe u

private theorem factor_sylow_normalizer_fixes_displacement
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (D : Subgroup K) (hD : IsOneSevenFactor (V:=V) D) (S : Sylow 2 K)
    (a : K) (haD : a ∈ D) (haS : a ∈ S) (ha : _root_.IsInvolution a)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2)
    (r : V) (hr : r ∈ commutatorAction (Subgroup.zpowers a) V) (hrne : r ≠ 1)
    (g : K) (hgS : g ∈ S) (hgD : g ∈ Subgroup.normalizer D) : g • r = r := by
  let A := Subgroup.zpowers a
  let R := commutatorAction A V
  have hAc : Nat.card A = 2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime ha.2 ha.1]
  have hAle : A ≤ (S : Subgroup K) ⊓ D :=
    Subgroup.zpowers_le.mpr ⟨haS,haD⟩
  have hp : IsPGroup 2 (((S : Subgroup K) ⊓ D) : Subgroup K) := S.isPGroup'.to_le inf_le_left
  have hdiv : Nat.card ((S : Subgroup K) ⊓ D : Subgroup K) ∣ 6 :=
    (RankOneThreeGroupAssembly.isSL2Two_card hD.1) ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcard : Nat.card ((S : Subgroup K) ⊓ D : Subgroup K) = 2 := by
    have htwo : 2 ∣ Nat.card ((S : Subgroup K) ⊓ D : Subgroup K) := by
      have hh := Subgroup.card_dvd_of_le hAle
      rwa [hAc] at hh
    have hle := Nat.le_of_dvd (by decide : 0<6) hdiv
    have hno3 : ¬ 3 ∣ Nat.card ((S : Subgroup K) ⊓ D : Subgroup K) := by
      rw [hn]
      intro hh
      have hh' : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hh
      norm_num at hh'
    interval_cases hc : Nat.card ((S : Subgroup K) ⊓ D : Subgroup K) <;> norm_num at *
  have hAe : A = (S : Subgroup K) ⊓ D :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hAc,hcard])
  have hgA : g ∈ Subgroup.normalizer A := by
    rw [hAe]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(S : Subgroup K).le_normalizer hgS,hgD⟩
  let C := Subgroup.zpowers g
  let _ : IsInvariant C V R := commutatorAction_isInvariant_of_normalizing_actor C A
    (Subgroup.zpowers_le.mpr hgA)
  have hgr : g • r ∈ R :=
    (IsInvariant.invariant (A:=C) (H:=R) ⟨g,Subgroup.mem_zpowers g⟩ r).mp hr
  have hgrne : g • r ≠ 1 := by
    intro hh
    apply hrne
    have hh' := congrArg (fun x : V => g⁻¹ • x) hh
    simpa only [inv_smul_smul,smul_one] using hh'
  obtain ⟨z,_hz,huniq⟩ := (Nat.card_eq_two_iff' (1:R)).mp hrank
  have heq : (⟨g • r,hgr⟩ : R) = ⟨r,hr⟩ :=
    (huniq _ (fun hh => hgrne (congrArg Subtype.val hh))).trans
      (huniq _ (fun hh => hrne (congrArg Subtype.val hh))).symm
  exact congrArg Subtype.val heq

private theorem nonzero_subgroup_card
    {V : Type u} [Group V] [Finite V] (U : Subgroup V) :
    Nat.card {v : V // v ∈ U ∧ v ≠ 1} = Nat.card U - 1 := by
  classical
  let e : {v : V // v ∈ U ∧ v ≠ 1} ≃ {v : U // v ≠ 1} :=
    { toFun := fun v => ⟨⟨v,v.property.1⟩,fun h => v.property.2 (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v, v.val.property,fun h => v.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  let _ := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique,← Nat.card_eq_fintype_card]

public theorem nine_nine_factor_point_stabilizer_index
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (hK : Nat.card K = 72) (hV : Nat.card V = 16)
    (D : Subgroup K) (hD : IsOneSevenFactor (V:=V) D) (S : Sylow 2 K)
    (a : K) (haD : a ∈ D) (haS : a ∈ S) (ha : _root_.IsInvolution a)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2)
    (r : V) (hr : r ∈ commutatorAction (Subgroup.zpowers a) V) (hrne : r ≠ 1) :
    Nat.card (MulAction.stabilizer K r) = 12 ∧
      Nat.card ((S : Subgroup K) ⊓ MulAction.stabilizer K r : Subgroup K) = 4 ∧
      (S : Subgroup K).relIndex (MulAction.stabilizer K r) = 3 := by
  classical
  let U := commutatorAction D V
  have hS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,hK]
    decide +kernel
  obtain ⟨c,hmove,hspan⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D (S : Subgroup K) hD S.isPGroup' hV (by rw [hS]; decide)
  let E := D.conjBy (c:K)
  let U' := commutatorAction E V
  have hE : IsOneSevenFactor (V:=V) E := hD.conjBy D c
  have hmap : U.map (MulDistribMulAction.toMulAut K V (c:K)).toMonoidHom = U' :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D c
  have hDE : D ≠ E := by
    intro heq
    apply hmove
    rw [hmap,show U' = U from congrArg (fun X : Subgroup K => commutatorAction X V) heq.symm]
  have hspan' : U ⊔ U' = ⊤ := by rwa [hmap] at hspan
  have hpair := nine_five_canonical_pair_of_support_span hyp D E hD hE hDE hspan'
  have hdis : Disjoint U U' := oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE
  have hrU : r ∈ U := by
    have hle : commutatorAction (Subgroup.zpowers a) V ≤ U := by
      rw [commutatorAction_eq_closure,show U = commutatorAction D V from rfl,
        commutatorAction_eq_closure]
      apply Subgroup.closure_mono
      rintro point ⟨b,v,rfl⟩
      exact ⟨⟨b,(Subgroup.zpowers_le.mpr haD) b.property⟩,v,rfl⟩
    exact hle hr
  have hcrU' : (c:K) • r ∈ U' := by
    rw [← hmap]
    exact ⟨r,hrU,rfl⟩
  have hcrne : (c:K) • r ≠ 1 := by
    intro hh
    apply hrne
    have hh' := congrArg (fun v : V => (c:K)⁻¹ • v) hh
    simpa only [inv_smul_smul,smul_one] using hh'
  have hcrr : (c:K) • r ≠ r := by
    intro hh
    exact hrne (hdis.le_bot ⟨hrU,hh ▸ hcrU'⟩)
  have hsupport (g : K) : g • r ∈ U ∨ g • r ∈ U' := by
    have hm : g • r ∈ commutatorAction (D.conjBy g) V := by
      rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy]
      exact ⟨r,hrU,rfl⟩
    rcases (hpair.2.2.2.1 g) with ⟨hfirst,_⟩ | ⟨hfirst,_⟩
    · rw [hfirst] at hm
      exact Or.inl hm
    · rw [hfirst] at hm
      exact Or.inr hm
  let points : Set V := {v | v∈U ∧ v≠1} ∪ {v | v∈U' ∧ v≠1}
  have horbit : MulAction.orbit K r = points := by
    ext v
    constructor
    · rintro ⟨g,rfl⟩
      have hgne : g • r ≠ 1 := by
        intro hh
        apply hrne
        have hh' := congrArg (fun v : V => g⁻¹ • v) hh
        simpa only [inv_smul_smul,smul_one] using hh'
      rcases hsupport g with hh | hh
      · exact Or.inl ⟨hh,hgne⟩
      · exact Or.inr ⟨hh,hgne⟩
    · rintro (⟨hv,hne⟩ | ⟨hv,hne⟩)
      · obtain ⟨g,_,hgr⟩ := oneSevenFactor_support_transitive D hD r hrU hrne v hv hne
        exact ⟨g,hgr⟩
      · obtain ⟨g,_,hgr⟩ := oneSevenFactor_support_transitive E hE ((c:K)•r) hcrU' hcrne v hv hne
        exact ⟨g*(c:K),by simpa only [mul_smul] using hgr⟩
  have hpointsDis : Disjoint ({v : V | v∈U ∧ v≠1} : Set V) {v | v∈U' ∧ v≠1} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact hv.2 (hdis.le_bot ⟨hv.1,hw.1⟩)
  have horbitCard : Nat.card (MulAction.orbit K r) = 6 := by
    rw [horbit,Nat.card_congr (Equiv.Set.union hpointsDis),Nat.card_sum]
    change Nat.card {v : V // v∈U ∧ v≠1} + Nat.card {v : V // v∈U' ∧ v≠1} = 6
    rw [nonzero_subgroup_card U,nonzero_subgroup_card U',hD.2.2.1,hE.2.2.1]
  have hfix (g : K) (hgS : g∈S) (hgD : D.conjBy g = D) : g • r = r :=
    factor_sylow_normalizer_fixes_displacement D hD S a haD haS ha hrank r hr hrne
      g hgS (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgD)
  have hSylowOrbit : MulAction.orbit S r = ({r,(c:K)•r} : Set V) := by
    ext v
    constructor
    · rintro ⟨g,rfl⟩
      rcases (hpair.2.2.2.1 (g:K)) with ⟨hg,_⟩ | ⟨hg,_⟩
      · exact Or.inl (hfix g g.property hg)
      · have hback : D.conjBy ((c:K)⁻¹*(g:K)) = D := by
          rw [Subgroup.conjBy_mul,hg]
          change (D.conjBy (c:K)).conjBy (c:K)⁻¹ = D
          exact Subgroup.conjBy_inv D (c:K)
        have hfixed := hfix ((c:K)⁻¹*(g:K)) (S.mul_mem (S.inv_mem c.property) g.property) hback
        apply Or.inr
        change (g:K) • r = (c:K) • r
        have hh := congrArg (fun v : V => (c:K) • v) hfixed
        simpa only [mul_smul,smul_inv_smul] using hh
    · rintro (rfl | rfl)
      · exact ⟨1,one_smul _ _⟩
      · exact ⟨c,rfl⟩
  have hSylowOrbitCard : Nat.card (MulAction.orbit S r) = 2 := by
    rw [hSylowOrbit,Nat.card_eq_fintype_card]
    simp [hcrr.symm]
  have hstabCard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K r)
  rw [Nat.card_prod,horbitCard,hK] at hstabCard
  have hSylowStabCard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S r)
  rw [Nat.card_prod,hSylowOrbitCard,hS] at hSylowStabCard
  have hSstab : Nat.card ((S : Subgroup K) ⊓ MulAction.stabilizer K r : Subgroup K) = 4 := by
    have heq : MulAction.stabilizer S r = (MulAction.stabilizer K r).subgroupOf S := rfl
    rw [heq] at hSylowStabCard
    rw [show (MulAction.stabilizer K r).subgroupOf S =
      (MulAction.stabilizer K r ⊓ (S : Subgroup K)).subgroupOf S from by ext x; simp] at hSylowStabCard
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show MulAction.stabilizer K r ⊓ (S : Subgroup K) ≤ S from inf_le_right)).toEquiv] at hSylowStabCard
    rw [inf_comm] at hSylowStabCard
    omega
  have hX : Nat.card (MulAction.stabilizer K r) = 12 := by omega
  have hindex := ((S : Subgroup K).subgroupOf (MulAction.stabilizer K r)).index_mul_card
  rw [show (S : Subgroup K).subgroupOf (MulAction.stabilizer K r) =
    ((S : Subgroup K) ⊓ MulAction.stabilizer K r).subgroupOf (MulAction.stabilizer K r)
      from by ext x; simp] at hindex
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show (S : Subgroup K) ⊓ MulAction.stabilizer K r ≤ MulAction.stabilizer K r from inf_le_right)).toEquiv,
    hSstab,hX] at hindex
  refine ⟨hX,hSstab,?_⟩
  rw [Subgroup.inf_subgroupOf_right] at hindex
  change (S : Subgroup K).relIndex (MulAction.stabilizer K r) * 4 = 12 at hindex
  omega

end Stellmacher.SectionNine
