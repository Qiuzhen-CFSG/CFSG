module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.ElementaryCase
public import Theory.GroupTheory.QuaternionCyclicQuotientCenter
/-!
# The source local two-group and its unique central involution

Choose a Sylow two-group of N_H(B₅) containing the proved noncentral inverter.
Its normal quaternion subgroup is C_Q(B₅), while the action on B₅ has cyclic
quotient. The quaternion-kernel theorem forces every central involution to be
z. All groups, elements and actions are the original source objects.

Source: Aschbacher--Smith J.3.6, printed p.439. The exact center assertion is
used to promote this order32 subgroup into N_G(P).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem inverter_order (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (v : Choices.FiveInverterData c B5) : orderOf v.i=2 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp v.z_class
  have he := (MulAut.conj g).orderOf_eq v.i
  change orderOf (g*v.i*g⁻¹)=orderOf v.i at he
  rw [hg,SourceCompletion.z_order c] at he
  exact he.symm

private theorem local_two_center_unique (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (q : FiveQuaternionData B5)
    (v : Choices.FiveInverterData c B5) (R : Subgroup G)
    (hR : R ≤ d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G))
    (hRc : Nat.card R=32) (hQR : CQ B5≤R) (hiR : v.i∈R) :
    ∀ j:R, j∈center R → orderOf j=2 → (j:G)=c.z := by
  let B := B5Image B5
  let φ : R →* MulAut B := B.normalizerMonoidHom.comp (inclusion (hR.trans inf_le_right))
  have hk : φ.ker=(G5 B5).subgroupOf R := by
    rw [← MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hQK : (CQ B5).subgroupOf R ≤ φ.ker := by
    rw [hk]
    exact comap_mono inf_le_right
  have hK40 : Nat.card φ.ker∣40 := by
    have hKG : φ.ker.map R.subtype ≤ d.toTypeRuSetup.H ⊓ G5 B5 := by
      rintro x ⟨a,ha,rfl⟩
      have ha' : a∈(G5 B5).subgroupOf R := hk ▸ ha
      exact ⟨(hR a.property).1,ha'⟩
    have hd := card_dvd_of_le hKG
    rw [card_map_of_injective R.subtype_injective,q.local_card] at hd
    exact hd
  have hK32 : Nat.card φ.ker∣32 := hRc ▸ φ.ker.card_subgroup_dvd_card
  have hK8 : Nat.card φ.ker≤8 := Nat.le_of_dvd (by decide)
    (show Nat.card φ.ker∣8 from Nat.dvd_gcd hK32 hK40)
  have hQ8 : Nat.card ((CQ B5).subgroupOf R)=8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv,CQ_card B5 q]
  have hker : φ.ker=(CQ B5).subgroupOf R :=
    (eq_of_le_of_card_ge hQK (by rw [hQ8]; exact hK8)).symm
  obtain ⟨eQ⟩ := q.quaternion
  let e : φ.ker ≃* QuaternionGroup 2 :=
    ((MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hQR)).trans eQ
  have hB : Nat.card B=5 := B5Image_card d.card_Z B5
  let : IsCyclic B := isCyclic_of_prime_card hB
  let : IsCyclic (ZMod (Nat.card B))ˣ := ZMod.isCyclic_units_prime (hB ▸ Fact.out)
  let : IsCyclic (MulAut B) := (IsCyclic.mulAutMulEquiv B).isCyclic.mpr inferInstance
  have hzQ : c.z∈CQ B5 := (q.inf_U.symm ▸ c.z_mem_Z).1
  let z : R := ⟨c.z,hQR hzQ⟩
  let i : R := ⟨v.i,hiR⟩
  have hzK : z∈φ.ker := hker.symm ▸ hzQ
  have hz2 : orderOf z=2 := by rw [← orderOf_coe]; exact SourceCompletion.z_order c
  have hi2 : orderOf i=2 := by rw [← orderOf_coe]; exact inverter_order c B5 v
  have hni : i∉centralizer (φ.ker : Set R) := by
    intro hn
    apply v.noncentral
    intro x hx
    have hxR : (⟨x,hQR hx⟩ : R)∈φ.ker := hker.symm ▸ hx
    exact congrArg Subtype.val (hn ⟨x,hQR hx⟩ hxR)
  intro j hj hj2
  exact congrArg Subtype.val (central_involution_eq_of_quaternion_kernel φ e z i hzK hz2 hi2 hni j hj hj2)

/-- A source two-subgroup of order32 with its unique central involution marked. -/
theorem exists_five_local_two (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ∃ R : Subgroup G,
      R ≤ d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G) ∧
      Nat.card R=32 ∧ CQ B5≤R ∧
      ∀ j:R, j∈center R → orderOf j=2 → (j:G)=c.z := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨v⟩ := c.fiveInverterData_source B5
  let N := d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G)
  have hiN : v.i∈N := ⟨v.mem_H,v.normalizes_B5Image c B5⟩
  let i : N := ⟨v.i,hiN⟩
  have hi2 : orderOf i=2 := by rw [← orderOf_coe]; exact inverter_order c B5 v
  have hip : IsPGroup 2 (zpowers i) := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hi2,pow_one])
  obtain ⟨S,hS⟩ := hip.exists_le_sylow
  have hQN : CQ B5≤N := le_inf (q.le_HC.trans inf_le_left)
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hNQ : N≤normalizer (CQ B5 : Set G) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (inf_le_left.trans d.ru2.six.normalized)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))
  let : ((CQ B5).subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hQN).mpr hNQ
  have hQp : IsPGroup 2 (CQ B5) := IsPGroup.of_card (n:=3) (CQ_card B5 q)
  have hQS : (CQ B5).subgroupOf N≤(S : Subgroup N) :=
    (hQp.comap_subtype (K:=N)).le_sylow_of_normal (N:=(CQ B5).subgroupOf N) S
  let R := (S : Subgroup N).map N.subtype
  have hQR : CQ B5≤R := by
    have hh := map_mono (f:=N.subtype) hQS
    rwa [map_subgroupOf_eq_of_le hQN] at hh
  have hiR : v.i∈R := mem_map_of_mem N.subtype (hS (mem_zpowers i))
  have hR : R≤N := map_subtype_le _
  have hRc : Nat.card R=32 := by
    rw [card_map_of_injective N.subtype_injective,S.card_eq_multiplicity,local_five_normalizer_card c B5]
    decide +kernel
  exact ⟨R,hR,hRc,hQR,local_two_center_unique c B5 q v R hR hRc hQR hiR⟩

end CFSG.Quasithin.ChapterJ.Section03
