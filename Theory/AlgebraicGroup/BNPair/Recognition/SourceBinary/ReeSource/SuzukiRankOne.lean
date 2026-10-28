module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelRadical
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# The full source Suzuki actor under its natural panel marking

The root-generated actor maps to the prescribed faithful endpoint quotient.
Its image is the image of the local prime-to-two residual, hence the entire
Suzuki group. This also holds at parameter zero: an odd-index residual of
Sz(2) cannot have index five, since the specified pair of involutions has
product of order five.

The kernel is the same central odd stem kernel as the original panel action.
Every odd Sylow subgroup of the model is cyclic (at m=0 its order divides
five). Central Sylow transfer kills this kernel. The resulting isomorphism
is the literal endpoint projection and agrees with the previously constructed
simple-root chart. No simplicity or perfectness is assumed at m=0.

Source: Fong--Seitz I (1973), (5C), pp.25--26, used for the effective modules
in (6H), p.52. This lifts an earlier natural Suzuki panel marking; it does
not select or pair the two rank-one families or synchronize their fields.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

private theorem binary_odd_sylow_cyclic {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (T : Sylow p (SuzukiMatrixGroup 0)) : IsCyclic T := by
  have hd : Nat.card T ∣ 4*5 := by
    simpa only [suzukiZero_card] using (T : Subgroup (SuzukiMatrixGroup 0)).card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card T) 4 := by
    obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
    rw [hn]
    exact ((hp.out.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.out.ne_one))).pow_left n).pow_right 2
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact isCyclic_of_card_dvd_prime (hc.dvd_of_dvd_mul_left hd)

private theorem odd_stem_suzuki_injective {E : Type*} [Group E] [Finite E]
    (m : ℕ) (f : E →* SuzukiMatrixGroup m)
    (hc : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (ho : Nat.Coprime 2 (Nat.card f.ker)) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpker
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact Nat.prime_two.not_dvd_one (ho.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpker)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' p hpker
  have horder : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  have hzp : IsPGroup p (zpowers (z : E)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,horder,pow_one])
  obtain ⟨S,hS⟩ := hzp.exists_le_sylow
  obtain ⟨T,hT⟩ := (S.isPGroup'.map f).exists_le_sylow
  let : IsCyclic T := by
    by_cases hm : m = 0
    · subst m; exact binary_odd_sylow_cyclic hp2 T
    · exact suzukiSylow_isCyclic_of_ne_two (by omega) hp2 T
  let g : S →* T := (f.comp (S : Subgroup E).subtype).codRestrict T
    (fun x => hT (mem_map_of_mem f x.property))
  have hgc : g.ker ≤ center S := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hc (congrArg Subtype.val hx)) y)
  let : IsMulCommutative S := g.isMulCommutative_of_isCyclic_of_ker_le_center hgc
  have hzcomm := center_inf_commutator_inf_sylow_le_commutator S
    ⟨⟨hc z.property, hd z.property⟩, hS (mem_zpowers _)⟩
  have hbot : ⁅(S : Subgroup E),(S : Subgroup E)⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr inferInstance
  have hzone : (z : E) = 1 := mem_bot.mp (hbot ▸ hzcomm)
  rw [hzone,orderOf_one] at horder
  exact hp.ne_one horder.symm

private theorem suzuki_primeToResidual (m : ℕ) :
    primeToResidual 2 (SuzukiMatrixGroup m) = ⊤ := by
  by_cases hm : m = 0
  · subst m
    let R := primeToResidual 2 (SuzukiMatrixGroup 0)
    have hc := primeToResidual_index_coprime (G := SuzukiMatrixGroup 0) 2
    have hd : R.index ∣ 20 := by simpa only [suzukiZero_card] using R.index_dvd_card
    have hi : R.index ∣ 5 := by
      apply (hc.symm.pow_right 2).dvd_of_dvd_mul_left
      exact hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hi with h1 | h5
    · exact index_eq_one.mp h1
    · have hcard : Nat.card R = 4 := by
        have he := R.card_mul_index
        rw [h5,suzukiZero_card] at he
        omega
      have hu : suzukiZeroInvolution ∈ R := mem_primeToResidual_of_pow
        (n := 1) (by simpa only [pow_one,suzukiZeroInvolution_order] using pow_orderOf_eq_one suzukiZeroInvolution)
      have hv : suzukiWeyl 0 ∈ R := mem_primeToResidual_of_pow
        (n := 1) (by simpa only [pow_one,suzukiWeyl_orderOf] using pow_orderOf_eq_one (suzukiWeyl 0))
      have hh := orderOf_dvd_natCard (⟨suzukiZeroInvolution*suzukiWeyl 0,R.mul_mem hu hv⟩ : R)
      rw [← Subgroup.orderOf_coe, suzukiZeroInvolution_mul_weyl_order, hcard] at hh
      norm_num at hh
  · let : IsSimpleGroup (SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    rcases (inferInstance : (primeToResidual 2 (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hb | ht
    · have hw : suzukiWeyl m ∈ primeToResidual 2 (SuzukiMatrixGroup m) :=
        mem_primeToResidual_of_pow (n := 1)
          (by simpa only [pow_one,suzukiWeyl_orderOf] using pow_orderOf_eq_one (suzukiWeyl m))
      rw [hb,mem_bot] at hw
      have ho := suzukiWeyl_orderOf m
      rw [hw,orderOf_one] at ho
      omega
    · exact ht

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The marking on the whole source rank-one group is the literal endpoint projection. -/
def suzukiActorMap : rankOne Q split i →* SuzukiMatrixGroup m :=
  μ.toMonoidHom.comp ((QuotientGroup.mk' (panelKernel Q i)).comp
    (inclusion (rankOne_le_parabolic Q split i)))

theorem suzukiActorMap_ker :
    (suzukiActorMap Q split i m μ).ker = (RootLocalCover.projection Q split i).ker := by
  rw [RootLocalCover.projection_ker]
  ext r
  change μ (QuotientGroup.mk' (panelKernel Q i)
    (inclusion (rankOne_le_parabolic Q split i) r)) = 1 ↔ _
  rw [← map_one μ, μ.injective.eq_iff]
  change inclusion (rankOne_le_parabolic Q split i) r ∈
    (QuotientGroup.mk' (panelKernel Q i)).ker ↔ _
  rw [QuotientGroup.ker_mk']
  change _ ↔ inclusion (rankOne_le_parabolic Q split i) r ∈
    (localKernel Q i).subgroupOf (Endpoint Q i)
  rw [localKernel_subgroupOf]
  rfl

include μ hB in
private theorem suzuki_remainder_le_kernel :
    simpleRemainder Q split i ≤ localKernel Q i :=
  remainder_le_panelKernel_of_marking Q split i μ (matrixRootSylow m)
    (hB.trans (by
      change normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) =
        normalizer ((matrixRootSylow m : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
      rw [matrixRootSylow_carrier]))
    (suzuki_normalizer_index m (matrixRootSylow m))

include hB in
theorem suzukiActorMap_injective : Function.Injective (suzukiActorMap Q split i m μ) := by
  obtain ⟨_,hc,ho,hd⟩ := RootLocalCover.central_odd_cover Q split i
    (suzuki_remainder_le_kernel Q split i m μ hB)
  have hk := suzukiActorMap_ker Q split i m μ
  exact odd_stem_suzuki_injective m _ (hk.symm ▸ hc) (hk.symm ▸ hd) (hk.symm ▸ ho)

include hB in
theorem suzukiActorMap_surjective : Function.Surjective (suzukiActorMap Q split i m μ) := by
  let f : Endpoint Q i →* SuzukiMatrixGroup m :=
    μ.toMonoidHom.comp (QuotientGroup.mk' (panelKernel Q i))
  have hf : Function.Surjective f := μ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrange : (suzukiActorMap Q split i m μ).range =
      ((localClosure Q split i).subgroupOf (Endpoint Q i)).map f := by
    apply le_antisymm
    · rintro y ⟨r,rfl⟩
      exact ⟨inclusion (rankOne_le_parabolic Q split i) r,
        rankOne_le_localClosure Q split i r.property,rfl⟩
    · rintro y ⟨c,hc,rfl⟩
      have hh := localClosure_le_rankOne_sup_kernel Q split i
        (suzuki_remainder_le_kernel Q split i m μ hB) hc
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
        ((rankOne_le_parabolic Q split i).trans (localKernel_parabolic_normalizes Q i))] at hh
      obtain ⟨r,hr,k,hk,he⟩ := hh
      let rE : Endpoint Q i := ⟨r,rankOne_le_parabolic Q split i hr⟩
      let kE : Endpoint Q i := ⟨k,Q.tits.B_le_standardParabolic _ (localKernel_le_borel Q i hk)⟩
      have hkE : kE ∈ panelKernel Q i := by
        change kE ∈ (endpointBorel Q i).normalCore
        rw [← localKernel_subgroupOf]
        exact hk
      have heE : c = rE*kE := Subtype.ext he.symm
      have hfk : f kE = 1 := by
        change μ (QuotientGroup.mk' (panelKernel Q i) kE) = 1
        exact (congrArg μ ((QuotientGroup.eq_one_iff (N := panelKernel Q i) kE).mpr hkE)).trans μ.map_one
      refine ⟨⟨r,hr⟩,?_⟩
      rw [heE,map_mul,hfk,mul_one]
      rfl
  apply MonoidHom.range_eq_top.mp
  rw [hrange, QuadrangleStructure.localClosure_eq_primeToResidual Q split i
    (UnitarySource.actorReflection Q split i), map_primeToResidual_of_surjective 2 f hf,
    suzuki_primeToResidual]

/-- The actual R_i is the full Suzuki group, also for m=0. -/
def suzukiActorEquiv : rankOne Q split i ≃* SuzukiMatrixGroup m :=
  MulEquiv.ofBijective (suzukiActorMap Q split i m μ)
    ⟨suzukiActorMap_injective Q split i m μ hB,suzukiActorMap_surjective Q split i m μ hB⟩

@[simp] theorem suzukiActorEquiv_apply (r : rankOne Q split i) :
    suzukiActorEquiv Q split i m μ hB r = μ (QuotientGroup.mk'
      (panelKernel Q i) (inclusion (rankOne_le_parabolic Q split i) r)) := rfl

@[simp] theorem suzukiActorEquiv_simpleRoot (r : simpleRoot Q split i) :
    suzukiActorEquiv Q split i m μ hB (inclusion le_sup_left r) =
      suzukiRootEquiv Q split i m μ hB r := rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
