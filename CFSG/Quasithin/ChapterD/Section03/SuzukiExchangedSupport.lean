module
public import Theory.Representation.Suzuki.CommutingPrimeDisplacement
public import CFSG.Quasithin.ChapterD.Section03.SuzukiSupportRank
public import Theory.GroupTheory.ElementaryPairActionRank
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.Representation.NormalSimpleConstituent

/-!
# Exchanged support commuting with a Suzuki component

Pass to the fixed space of the starred actor's pointwise component-orbit
kernel. This space is nonzero, invariant under the full actor, and faithful
on either exchanged simple component. The actor image therefore pays only
the rank visible in the component-orbit automorphism group. An odd-prime
commutator of the exchanger stays nontrivial on this space. The commuting
Suzuki group triples its binary prime displacement, giving the prime bound.

For SL2(2^n), n at least four, a primitive prime of binary order 2n and
the automorphism-rank bound n+1 contradict that inequality. The original
Chapter 10 consumer already forces n at least five and supplies the exact
component and full actor, including every pointwise and quotient kernel.
Source: Aschbacher--Smith D.3.9, pp.200--201, and G.7.1, p.347.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD

private theorem exchanged_prime_image_order
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (J : Subgroup G) (hJ : IsComponent G J) (hZ : center J = ⊥)
    (hf : Function.Injective (f.comp J.subtype))
    (a : G) (han : a ∉ normalizer (J : Set G))
    {p : ℕ} (hp : p.Prime) (x : J) (hx : orderOf x = p) :
    orderOf (f (a * x * a⁻¹ * (x : G)⁻¹)) = p := by
  let Jt := J.map (MulAut.conj a).toMonoidHom
  have hne : Jt ≠ J := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : Jt ≤ centralizer (J : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    ((hJ.map_conj a).commutator_eq_bot_of_ne hJ hne)
  have hy : a * (x : G) * a⁻¹ ∈ Jt := mem_map_of_mem _ x.property
  have hxp : (x : G)^p=1 := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  have hyp : (a * (x : G) * a⁻¹)^p=1 := by
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj a) hxp
  have hcomm : Commute (a * (x : G) * a⁻¹) (x : G)⁻¹ :=
    (hc hy _ (J.inv_mem x.property)).symm
  have hpow : (f (a * (x : G) * a⁻¹ * (x : G)⁻¹))^p=1 := by
    rw [←map_pow,hcomm.mul_pow,hyp,inv_pow,hxp,inv_one,mul_one,map_one]
  have hn : f (a * (x : G) * a⁻¹ * (x : G)⁻¹) ≠ 1 := by
    intro he
    have heq : f (a * (x : G) * a⁻¹) = f x := by
      apply mul_inv_eq_one.mp
      simpa only [map_mul,map_inv] using he
    have hxZ : x ∈ center J := mem_center_iff.mpr fun j => by
      apply hf
      change f ((j : G) * x) = f ((x : G) * j)
      rw [map_mul,map_mul,←heq]
      simpa only [map_mul] using congrArg f (hc hy j j.property)
    have hx1 : x=1 := mem_bot.mp (hZ ▸ hxZ)
    rw [hx1,orderOf_one] at hx
    exact hp.ne_one hx.symm
  let : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hn

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Nontrivial V]

/-- A prime in an exchanged simple support pays three binary prime degrees
inside the same actor image; the pointwise support kernel is retained. -/
theorem suzuki_exchanged_support_prime_bound
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [IsSimpleGroup J]
    (hJ : IsComponent G J) (hA : A ∈ QhatStar ρ)
    (hKJ : K ≤ centralizer (J : Set G)) (hKA : K ≤ centralizer (A : Set G))
    (a : G) (ha : a ∈ A) (han : a ∉ normalizer (J : Set G))
    (he : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom)
    (hfixX : fixedSpace ρ (componentOrbit J A) = ⊥)
    {r : ℕ} (hr : rank ((componentOrbit J A).normalizerMonoidHom.comp
      (inclusion (le_normalizer_componentOrbit J A))).range ≤ r)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpJ : p ∣ Nat.card J) :
    3 * orderOf (2 : ZMod p) ≤ 4*r := by
  let : Fact p.Prime := ⟨hp⟩
  let X := componentOrbit J A
  let C := A ⊓ centralizer (X : Set G)
  let U := fixedSpace ρ C
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hpC : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (inclusion (show C ≤ A from inf_le_left)) (inclusion_injective _)
  have hAC : A ≤ centralizer (C : Set G) := by
    intro b hb c hc
    exact congrArg Subtype.val (mul_comm (⟨c,hc.1⟩ : A) (⟨b,hb⟩ : A))
  have hXC : X ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hKC : K ≤ centralizer (C : Set G) := hKA.trans (centralizer_le inf_le_left)
  have hAU : A ≤ subspaceStabilizer ρ U :=
    fixedSpace_invariant_normalizer ρ (hAC.trans (Subgroup.centralizer_le_normalizer _))
  have hXU : X ≤ subspaceStabilizer ρ U :=
    fixedSpace_invariant_normalizer ρ (hXC.trans (Subgroup.centralizer_le_normalizer _))
  have hKU : K ≤ subspaceStabilizer ρ U :=
    fixedSpace_invariant_normalizer ρ (hKC.trans (Subgroup.centralizer_le_normalizer _))
  have hJU : J ≤ subspaceStabilizer ρ U := (le_componentOrbit J A).trans hXU
  have hUn : U ≠ ⊥ := by
    let : MulAction C V := {
      smul c v := ρ c v
      one_smul v := by change ρ 1 v = v; simp
      mul_smul c d v := by
        change ρ ((c : G)*d) v = ρ c (ρ d v)
        simp only [map_mul,Module.End.mul_apply] }
    let : Finite V := Module.finite_of_finite (ZMod 2)
    have hd : 2 ∣ Nat.card V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact dvd_pow_self 2 Module.finrank_pos.ne'
    obtain ⟨v,hv,hv0⟩ := hpC.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hd
      (a := (0 : V)) (by intro c; exact map_zero (ρ c))
    intro hz
    have hvz : v = 0 := by simpa only [hz,Submodule.mem_bot] using (show v ∈ U from hv)
    exact hv0 hvz.symm
  let τ := (invariantSubspace ρ J U hJU).toRepresentation
  have hfJ : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases τ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · apply False.elim
      have hUJ : U ≤ fixedSpace ρ J := by
        intro v hv j
        have hj : j ∈ τ.ker := ht.symm ▸ mem_top j
        exact congrArg Subtype.val (LinearMap.congr_fun hj (⟨v,hv⟩ : U))
      have hUJt : U ≤ fixedSpace ρ (J.map (MulAut.conj a).toMonoidHom) := by
        rintro v hv ⟨j,hj⟩
        obtain ⟨x,hx,rfl⟩ := hj
        change ρ (a*x*a⁻¹) v = v
        have hxv : ρ x (ρ a⁻¹ v) = ρ a⁻¹ v := hUJ ((hAU (A.inv_mem ha) v).2 hv) ⟨x,hx⟩
        rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hxv]
        simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
      apply hUn
      apply bot_unique
      rw [←hfixX,he]
      rw [show fixedSpace ρ (J ⊔ J.map (MulAut.conj a).toMonoidHom) =
        fixedSpace ρ J ⊓ fixedSpace ρ (J.map (MulAut.conj a).toMonoidHom) from
        ρ.invariants_comp_sup _ _]
      exact le_inf hUJ hUJt
  let S := subspaceStabilizer ρ U
  let σ := stabilizerRepresentation ρ U
  let K' := K.subgroupOf S
  let J' := J.subgroupOf S
  let eK : K' ≃* K := subgroupOfEquivOfLe hKU
  let eJ : J' ≃* J := subgroupOfEquivOfLe hJU
  have hfix' : fixedSpace σ K' = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    apply hfix.le
    intro k
    exact congrArg Subtype.val (hv (eK.symm k))
  have hfaith : Function.Injective (σ.asGroupHom.comp J'.subtype) := by
    intro j k heq
    apply eJ.injective
    apply hfJ
    exact congrArg Units.val heq
  let : IsQuasisimple J := hJ.2
  have hZ : center J' = ⊥ := by
    let : IsSimpleGroup J' := eJ.isSimpleGroup
    let : IsQuasisimple J' := IsQuasisimple.of_mulEquiv eJ.symm
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hz => Group.IsPerfect.not_isMulCommutative J' (center_eq_top_iff.mp hz))
  let a' : S := ⟨a,hAU ha⟩
  have han' : a' ∉ normalizer (J' : Set S) := by
    intro hn
    apply han
    intro j
    constructor
    · intro hj
      exact (hn ⟨j,hJU hj⟩).mp hj
    · intro hj
      have hjs : j ∈ S := by
        have hh := S.mul_mem (S.mul_mem (S.inv_mem a'.property) (hJU hj)) a'.property
        simpa only [a',mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
      exact (hn ⟨j,hjs⟩).mpr hj
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  let x' : J' := eJ.symm x
  have hx' : orderOf x' = p := (eJ.symm.orderOf_eq x).trans hx
  let y : S := a' * x' * a'⁻¹ * (x' : S)⁻¹
  have hy : orderOf y = p := exchanged_prime_image_order (MonoidHom.id S) J'
    (hJ.subgroupOf hJU) hZ J'.subtype_injective a' han' hp x' hx'
  have hny : σ y ≠ 1 := by
    intro hz
    have hh := exchanged_prime_image_order σ.asGroupHom J' (hJ.subgroupOf hJU)
      hZ hfaith a' han' hp x' hx'
    have heq : σ.asGroupHom y = 1 := Units.ext hz
    rw [heq,orderOf_one] at hh
    exact hp.ne_one hh.symm
  have hKX : K ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    apply iSup_conjugates_le_of_le_normalizer J A (centralizer (K : Set G))
      (le_centralizer_iff.mp hKJ)
      ((le_centralizer_iff.mp hKA).trans (centralizer (K : Set G)).le_normalizer)
  have hyX : (y : G) ∈ X := by
    change a*(x:G)*a⁻¹*(x:G)⁻¹ ∈ X
    apply X.mul_mem
    · exact (le_iSup (fun b : A => J.map (MulAut.conj (b : G)).toMonoidHom)
        ⟨a,ha⟩) (mem_map_of_mem _ x.property)
    · exact X.inv_mem (le_componentOrbit J A x.property)
  have hKy : K' ≤ centralizer (zpowers y : Set S) := by
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    intro k hk
    exact Subtype.ext (hKX hk y.val hyX).symm
  have hl := Representation.Suzuki.commuting_prime_triple_displacement σ K' hfix'
    m hm (eK.trans e) hp hp2 y hy hny hKy
  have hu := fixedCodim_commutator_le_twice σ a' (x' : S)
  change fixedCodim σ (zpowers y) ≤ 2 * fixedCodim σ (zpowers a') at hu
  let A' := A.subgroupOf S
  have ham : zpowers a' ≤ A' := zpowers_le.mpr ha
  have hmono := NaturalTensor.fixedCodim_mono σ ham
  have hmove : ¬ U ≤ fixedSpace ρ A := by
    intro hh
    have ha0 : σ a' = 1 := by
      apply LinearMap.ext
      intro v
      exact Subtype.ext (hh v.property ⟨a,ha⟩)
    have hainv : σ a'⁻¹ = 1 := by
      calc
        σ a'⁻¹ = σ a'⁻¹ * σ a' := by rw [ha0,mul_one]
        _ = 1 := by rw [←map_mul,inv_mul_cancel,map_one]
    apply hny
    simp only [y,map_mul,ha0,hainv,one_mul,mul_one]
    rw [←map_mul,mul_inv_cancel,map_one]
  have hb := RPlusBound.restricted ρ
    (show A ∈ RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,QhatStar.mem_RPlus ρ hA⟩)
    U hAU hmove
  have hbudget := (actionRatio_le_nat_iff _ hb.1 2).mp hb.2
  have hcod : fixedCodim σ A' =
      fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) := by
    change fixedCodim ((subspaceImageRepresentation ρ U).comp (subspaceActionHom ρ U)) A' = _
    unfold fixedCodim
    rw [fixedSpace_comp_map]
    rfl
  let α := X.normalizerMonoidHom.comp (inclusion (le_normalizer_componentOrbit J A))
  let β := subgroupActionHom ρ U A hAU
  have hker : α.ker ≤ β.ker := by
    intro b hb
    have hc : (b : G) ∈ centralizer (X : Set G) := by
      intro x hx
      have hh := congrArg (fun f : MulAut X => (f ⟨x,hx⟩ : G)) hb
      change (b : G)*x*(b : G)⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply subspaceImageRepresentation_injective ρ U
    ext v
    exact v.property ⟨b,b.property,hc⟩
  have hcard : Nat.card (restrictedSubgroup ρ U A) ≤ Nat.card α.range := by
    rw [←subgroupActionHom_range ρ U A hAU]
    have hd := index_dvd_of_le hker
    rw [index_ker,index_ker] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hr' : rank (restrictedSubgroup ρ U A) ≤ r := (Nat.log_mono_right hcard).trans hr
  rw [hcod] at hmono
  omega


open scoped MatrixGroups
/-- An exchanged binary SL2 component of degree at least four cannot support
a starred actor commuting with a fixed-free Suzuki component. -/
theorem suzuki_no_exchanged_large_binary_support
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J A : Subgroup G) [IsSimpleGroup J]
    (hJ : IsComponent G J) (hA : A ∈ QhatStar ρ)
    (hKJ : K ≤ centralizer (J : Set G)) (hKA : K ≤ centralizer (A : Set G))
    (hlay : ∀ p : ℕ, p.Prime → Odd p → primeRank p (componentLayer G) ≤ 2)
    (hnot : ¬ A ≤ normalizer (J : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 4 ≤ n) (hF : Nat.card F = 2^n) (eJ : J ≃* SL(2,F)) : False := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hindex : (normalizer (J : Set G)).index = 2 :=
    (hJ.normal_or_index_two_of_layer_odd_rank_le_two hlay).resolve_left
      (fun hj => hnot (by let := hj; rw [normalizer_eq_top]; exact le_top))
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
  let N := normalizer (J : Set G)
  let : N.Normal := normal_of_index_eq_two hindex
  have hdiv : N.relIndex A ∣ 2 := by
    simpa only [show N.index = 2 from hindex] using N.relIndex_dvd_index_of_normal A
  have hirel : N.relIndex A = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun he => hnot (Subgroup.relIndex_eq_one.mp he))
  have horbit : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two J A N hirel inf_le_right ha han
  let X := componentOrbit J A
  let : X.Normal := by
    change (componentOrbit J A).Normal
    rw [horbit]
    exact sup_conjugate_normal_of_normalizer_index_two J hindex a han
  have hXn : X ≠ ⊥ := by
    intro hz
    have hJ0 : J = ⊥ := bot_unique ((le_componentOrbit J A).trans hz.le)
    exact (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance hJ0
  have hfixX := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi X hXn
  have hr := elementary_component_exchanged_orbit_action_rank J A hJ hlay hnot
  have hbound : rank (X.normalizerMonoidHom.comp
      (inclusion (le_normalizer_componentOrbit J A))).range ≤ n+1 := by
    apply hr.trans
    rw [primeRank_equiv 2 (MulAut.congr eJ)]
    exact Nat.add_le_add_right
      (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le (by omega) hF) 1
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two
    (m := 2*n) (by omega) (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [show (2 : ZMod 2)=0 from rfl,orderOf_zero] at ho
    omega
  have hpJ : p ∣ Nat.card J := by
    rw [Nat.card_congr eJ.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    apply dvd_mul_of_dvd_right
    rw [←pow_mul,show n*2=2*n by omega]
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
      ←ho,pow_orderOf_eq_one,sub_self]
  have hh := suzuki_exchanged_support_prime_bound ρ K hfix m hm e J A hJ hA hKJ hKA
    a ha han horbit hfixX hbound hp hp2 hpJ
  rw [ho] at hh
  omega
end CFSG.Quasithin.ChapterD
