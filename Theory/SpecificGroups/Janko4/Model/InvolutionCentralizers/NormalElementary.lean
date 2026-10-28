module
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CentralKernelElementCentralizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Large elementary subgroups in J₄ involution centralizers

An elementary subgroup of order 256 or 1024 containing the marked involution
cannot be normalized by its full centralizer. In the first native centralizer,
the extraspecial two-core bounds the order of abelian subgroups by 128.
In the second, the actual two-core is the self-centralizing elementary group
of order 2048. Orbit counting modulo eleven forces an eleven-element to fix
first the proposed subgroup and then the entire core, a contradiction.

The obstruction also holds when only a normal subgroup of two-power index
normalizes the elementary subgroup. Its two-core lies in the full centralizer's
two-core, and it retains an element of order eleven. This transports through
central two-kernels when the map is injective on the elementary subgroup,
as well as through arbitrary odd kernels. The doubled-natural consumer
retains the original orbit and the full component cover.
Source: GLS3 Table 5.3i and Aschbacher--Smith 4.4.3, 12.1.1 and 12.1.9,
printed pp.619--623,788,793. The native J₄ model and its imported certificates
retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem eleven_fixed_card {C : Type*} [Group C] [Finite C]
    (W : Subgroup C) [W.Normal] (hW : IsPGroup 2 W)
    (x : C) (hx : orderOf x = 11) :
    ∃ k : ℕ, Nat.card (W ⊓ centralizer (zpowers x : Set C) : Subgroup C) = 2 ^ k ∧
      2 ^ k ≤ Nat.card W ∧ Nat.card W % 11 = 2 ^ k % 11 := by
  have hp : IsPGroup 11 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨k,hk⟩ := (hW.to_le (show W ⊓ centralizer (zpowers x : Set C) ≤ W from inf_le_left)).exists_card_eq
  refine ⟨k,hk,?_,?_⟩
  · rw [← hk]; exact card_le_of_le inf_le_left
  · have hm := card_modEq_card_inf_centralizer (zpowers x) W hp
      (by rw [normalizer_eq_top]; exact le_top)
    change Nat.card W % 11 = _ at hm
    rwa [hk] at hm

private theorem eleven_centralizes_small {C : Type*} [Group C] [Finite C]
    (W : Subgroup C) [W.Normal] (hW : IsPGroup 2 W)
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : C) (hz : z ∈ W) (hzne : z ≠ 1) (hzc : z ∈ center C)
    (x : C) (hx : orderOf x = 11) : W ≤ centralizer (zpowers x : Set C) := by
  obtain ⟨k,hk,hkle,hm⟩ := eleven_fixed_card W hW x hx
  have hk10 : k ≤ 10 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hp
    rcases hcard with hc | hc <;> omega
  have hfixne : (W ⊓ centralizer (zpowers x : Set C) : Subgroup C) ≠ ⊥ := by
    intro hb
    apply hzne
    have hh : z ∈ W ⊓ centralizer (zpowers x : Set C) :=
      ⟨hz,fun y _ => mem_center_iff.mp hzc y⟩
    simpa only [hb,mem_bot] using hh
  have hk0 : k ≠ 0 := by
    intro h0
    apply hfixne
    apply Subgroup.card_eq_one.mp
    simpa only [h0,pow_zero] using hk
  have he : Nat.card (W ⊓ centralizer (zpowers x : Set C) : Subgroup C) = Nat.card W := by
    rw [hk]
    rcases hcard with hc | hc <;> rw [hc] at hm hkle ⊢ <;>
      interval_cases k <;> norm_num at *
  exact (eq_of_le_of_card_ge inf_le_left he.ge).ge.trans inf_le_right

private theorem second_core : pCore 2 Second.ambientCentralizer = Second.ambientKernel := by
  open Sporadic.Mathieu in
  have hbase : pCore 2 M22 = ⊥ := by
    let := m22_isSimpleGroup
    rcases (inferInstance : (pCore 2 M22).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 M22 := by
        have hh : IsPGroup 2 (⊤ : Subgroup M22) := ht ▸ pCore_isPGroup
        exact hh.of_surjective (Subgroup.topEquiv (G := M22)).toMonoidHom Subgroup.topEquiv.surjective
      have hc := hp.exists_card_eq
      obtain ⟨k,hk⟩ := hc
      have hd : 11 ∣ Nat.card M22 := by rw [m22_order]; decide
      rw [hk] at hd
      have hh := (show Nat.Prime 11 by decide).dvd_of_dvd_pow hd
      norm_num at hh
  exact core_eq_kernel_of_action 2
    (conj_injective_of_center_eq_bot Sporadic.Mathieu.m22_center_eq_bot) hbase
    Second.ambientExtension.rightHom
    (fun x => Second.ambientExtension.rightHom_surjective (MulAut.conj x))
    (by let := Second.ambientKernel_elementary; exact IsElementaryAbelian.isPGroup 2 _)

/-- Orbit counting modulo eleven excludes both large normal elementary
subgroups containing a nonidentity central element in the second centralizer. -/
theorem second_no_normal_elementary_large
    (W : Subgroup Second.ambientCentralizer) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : Second.ambientCentralizer) (hz : z ∈ W) (hzne : z ≠ 1)
    (hzc : z ∈ center Second.ambientCentralizer) : False := by
  have hWE : W ≤ Second.ambientKernel := by
    rw [← second_core]
    exact le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 W⟩
  have hd : 11 ∣ Nat.card Second.ambientCentralizer := by rw [Second.ambient_card]; decide
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Second.ambientCentralizer) 11 hd
  have hc := eleven_centralizes_small W (IsElementaryAbelian.isPGroup 2 W) hcard z hz hzne hzc x hx
  let := Second.ambientKernel_elementary
  obtain ⟨k,hk,hkle,hm⟩ := eleven_fixed_card Second.ambientKernel
    (IsElementaryAbelian.isPGroup 2 _) x hx
  rw [Second.ambientKernel_card] at hkle hm
  have hk11 : k ≤ 11 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hp
    omega
  have hlow : 256 ≤ 2 ^ k := by
    have hh := card_le_of_le (le_inf hWE hc)
    rw [hk] at hh
    rcases hcard with hc | hc <;> omega
  have he : 2 ^ k = 2048 := by interval_cases k <;> norm_num at *
  have hEC : Second.ambientKernel ≤ centralizer (zpowers x : Set Second.ambientCentralizer) := by
    have hh : Second.ambientKernel ⊓ centralizer (zpowers x : Set Second.ambientCentralizer) =
        Second.ambientKernel := eq_of_le_of_card_ge inf_le_left (by
          rw [hk,he,Second.ambientKernel_card])
    exact hh.ge.trans inf_le_right
  have hxE : x ∈ Second.ambientKernel := by
    rw [← Second.ambientKernel_selfCentralizing]
    exact le_centralizer_iff.mp hEC (mem_zpowers x)
  have hd' : 11 ∣ 2048 := by
    rw [← Second.ambientKernel_card,← hx,Subgroup.orderOf_coe (⟨x,hxE⟩ : Second.ambientKernel)]
    exact orderOf_dvd_natCard _
  norm_num at hd'

/-- The extraspecial core excludes both large normal elementary subgroups
in the first native involution centralizer. -/
theorem first_no_normal_elementary_large
    (W : Subgroup First.centralizer) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024) : False := by
  have hWQ : W ≤ pCore 2 First.centralizer :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 W⟩
  let := First.centralizer_twoCore_extraspecial
  let E := W.subgroupOf (pCore 2 First.centralizer)
  let : IsMulCommutative E := ⟨⟨fun x y => (subgroupOfEquivOfLe hWQ).injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
  have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) E
  rw [Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv,First.centralizer_twoCore_card] at hb
  rcases hcard with hc | hc <;> rw [hc] at hb <;> norm_num at hb

private theorem elementary_le_core_of_normal_subgroup
    {C : Type*} [Group C] (E W : Subgroup C) [E.Normal] [IsElementaryAbelian 2 W]
    (hWE : W ≤ E) (hn : E ≤ normalizer (W : Set C)) : W ≤ pCore 2 C := by
  let : (W.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hWE).mpr hn
  let : IsElementaryAbelian 2 (W.subgroupOf E) := IsElementaryAbelian.subgroupOf hWE
  have hh : W.subgroupOf E ≤ pCore 2 E :=
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 _⟩
  rw [pCore_eq_comap_of_normal] at hh
  intro w hw
  exact hh (show (⟨w,hWE hw⟩ : E) ∈ W.subgroupOf E from hw)

/-- The first obstruction only needs normalization by a normal overgroup. -/
theorem first_no_elementary_large_normalized
    (E W : Subgroup First.centralizer) [E.Normal] [IsElementaryAbelian 2 W]
    (hWE : W ≤ E) (hn : E ≤ normalizer (W : Set First.centralizer))
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024) : False := by
  have hWQ := elementary_le_core_of_normal_subgroup E W hWE hn
  let := First.centralizer_twoCore_extraspecial
  let A := W.subgroupOf (pCore 2 First.centralizer)
  let : IsMulCommutative A := ⟨⟨fun x y => (subgroupOfEquivOfLe hWQ).injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) A
  rw [Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv,First.centralizer_twoCore_card] at hb
  rcases hcard with hc | hc <;> rw [hc] at hb <;> norm_num at hb

/-- A normal overgroup of two-power index retains the eleven-element obstruction. -/
theorem second_no_elementary_large_normalized
    (E W : Subgroup Second.ambientCentralizer) [E.Normal] [IsElementaryAbelian 2 W]
    (hE : IsPGroup 2 (Second.ambientCentralizer ⧸ E))
    (hWE : W ≤ E) (hn : E ≤ normalizer (W : Set Second.ambientCentralizer))
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : Second.ambientCentralizer) (hz : z ∈ W) (hzne : z ≠ 1)
    (hzc : z ∈ center Second.ambientCentralizer) : False := by
  have hWQ : W ≤ Second.ambientKernel := by
    rw [←second_core]
    exact elementary_le_core_of_normal_subgroup E W hWE hn
  have hd : 11 ∣ Nat.card Second.ambientCentralizer := by rw [Second.ambient_card]; decide
  have hcop : Nat.Coprime 11 E.index := by
    obtain ⟨k,hk⟩ := hE.exists_card_eq
    change Nat.Coprime 11 (Nat.card (Second.ambientCentralizer ⧸ E))
    rw [hk]
    exact (by decide : Nat.Coprime 11 2).pow_right k
  have hdE : 11 ∣ Nat.card E := hcop.dvd_of_dvd_mul_right (E.card_mul_index.symm ▸ hd)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 11 hdE
  let U := W.subgroupOf E
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hWE).mpr hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWE
  let t : E := ⟨z,hWE hz⟩
  have htC : t ∈ center E := mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hzc y))
  have hsize : Nat.card U = 256 ∨ Nat.card U = 1024 := by
    change Nat.card (W.subgroupOf E) = 256 ∨ Nat.card (W.subgroupOf E) = 1024
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWE).toEquiv]
  have hc := eleven_centralizes_small U (IsElementaryAbelian.isPGroup 2 U) hsize
    t hz (fun he => hzne (congrArg Subtype.val he)) htC x hx
  have hWx : W ≤ centralizer (zpowers (x : Second.ambientCentralizer) : Set Second.ambientCentralizer) := by
    intro w hw
    rw [zpowers_eq_closure,centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (hc (show (⟨w,hWE hw⟩ : E) ∈ U from hw) x (mem_zpowers x))).symm
  let := Second.ambientKernel_elementary
  have hx' : orderOf (x : Second.ambientCentralizer) = 11 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k,hk,hkle,hm⟩ := eleven_fixed_card Second.ambientKernel
    (IsElementaryAbelian.isPGroup 2 _) x hx'
  rw [Second.ambientKernel_card] at hkle hm
  have hk11 : k ≤ 11 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    norm_num at hp
    omega
  have hlow : 256 ≤ 2 ^ k := by
    have hh := card_le_of_le (le_inf hWQ hWx)
    rw [hk] at hh
    rcases hcard with hc | hc <;> omega
  have he : 2 ^ k = 2048 := by interval_cases k <;> norm_num at *
  have hEC : Second.ambientKernel ≤ centralizer (zpowers (x : Second.ambientCentralizer) : Set Second.ambientCentralizer) := by
    have hh : Second.ambientKernel ⊓ centralizer (zpowers (x : Second.ambientCentralizer) : Set Second.ambientCentralizer) =
        Second.ambientKernel := eq_of_le_of_card_ge inf_le_left (by rw [hk,he,Second.ambientKernel_card])
    exact hh.ge.trans inf_le_right
  have hxE : (x : Second.ambientCentralizer) ∈ Second.ambientKernel := by
    rw [←Second.ambientKernel_selfCentralizing]
    exact le_centralizer_iff.mp hEC (mem_zpowers (x : Second.ambientCentralizer))
  have hd' : 11 ∣ 2048 := by
    rw [←Second.ambientKernel_card,←hx',Subgroup.orderOf_coe (⟨x,hxE⟩ : Second.ambientKernel)]
    exact orderOf_dvd_natCard _
  norm_num at hd'

end Janko4.InvolutionCentralizers

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- A large elementary subgroup containing an involution cannot be normalized
by its full centralizer in the actual J₄ carrier. -/
theorem no_large_elementary_controlled_involution
    (W : Subgroup Model) [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : Model) (hz : z ∈ W) (hz2 : orderOf z = 2)
    (hn : centralizer ({z} : Set Model) ≤ normalizer (W : Set Model)) : False := by
  let C := centralizer ({z} : Set Model)
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hw hz)
  let U := W.subgroupOf C
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hWC).mpr hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWC
  have hc : Nat.card U = 256 ∨ Nat.card U = 1024 := by
    change Nat.card (W.subgroupOf C) = 256 ∨ Nat.card (W.subgroupOf C) = 1024
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
    exact hcard
  let t : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : t ≠ 1 := by
    intro he
    have hh : z = 1 := congrArg Subtype.val he
    rw [hh,orderOf_one] at hz2
    omega
  have htc : t ∈ center C := mem_center_iff.mpr (by
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp x.property)
  rcases centralizer_equiv_first_or_second z hz2 with he | he
  · obtain ⟨e⟩ := he
    let E := U.map e.toMonoidHom
    let : E.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
    apply first_no_normal_elementary_large E
    simpa only [E,card_map_of_injective (K := U) (f := e.toMonoidHom) e.injective] using hc
  · obtain ⟨e⟩ := he
    let E := U.map e.toMonoidHom
    let : E.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
    apply second_no_normal_elementary_large E
      (by simpa only [E,card_map_of_injective (K := U) (f := e.toMonoidHom) e.injective] using hc)
      (e t) (mem_map_of_mem e.toMonoidHom hz)
      (fun he => ht (e.injective (he.trans (map_one e).symm)))
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp htc x)

/-- The native obstruction holds with normal, two-power-index centralizer control. -/
theorem no_large_elementary_controlled_involution_normal_subgroup
    (W : Subgroup Model) [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : Model) (hz : z ∈ W) (hz2 : orderOf z = 2)
    (E : Subgroup (centralizer ({z} : Set Model))) [E.Normal]
    (hE : IsPGroup 2 (centralizer ({z} : Set Model) ⧸ E))
    (hWE : W.subgroupOf (centralizer ({z} : Set Model)) ≤ E)
    (hn : E ≤ normalizer (W.subgroupOf (centralizer ({z} : Set Model)) :
      Set (centralizer ({z} : Set Model)))) : False := by
  let C := centralizer ({z} : Set Model)
  have hWC : W ≤ C := fun w hw => mem_centralizer_singleton_iff.mpr (setLike_mul_comm hw hz)
  let U := W.subgroupOf C
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWC
  have hc : Nat.card U = 256 ∨ Nat.card U = 1024 := by
    change Nat.card (W.subgroupOf C) = 256 ∨ Nat.card (W.subgroupOf C) = 1024
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
    exact hcard
  let t : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : t ≠ 1 := by
    intro he
    have hh : z = 1 := congrArg Subtype.val he
    rw [hh,orderOf_one] at hz2
    omega
  have htc : t ∈ center C := mem_center_iff.mpr (by
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp x.property)
  rcases centralizer_equiv_first_or_second z hz2 with he | he
  · obtain ⟨e⟩ := he
    let E' := E.map e.toMonoidHom
    let U' := U.map e.toMonoidHom
    let : E'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let : IsElementaryAbelian 2 U' := IsElementaryAbelian.map e.toMonoidHom
    apply first_no_elementary_large_normalized E' U' (map_mono hWE)
      ((map_mono hn).trans (U.le_normalizer_map e.toMonoidHom))
    simpa only [U',card_map_of_injective (K := U) (f := e.toMonoidHom) e.injective] using hc
  · obtain ⟨e⟩ := he
    let E' := E.map e.toMonoidHom
    let U' := U.map e.toMonoidHom
    let : E'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let : IsElementaryAbelian 2 U' := IsElementaryAbelian.map e.toMonoidHom
    have hE' : IsPGroup 2 (Second.ambientCentralizer ⧸ E') :=
      hE.of_equiv (QuotientGroup.congr E E' e rfl)
    apply second_no_elementary_large_normalized E' U' hE' (map_mono hWE)
      ((map_mono hn).trans (U.le_normalizer_map e.toMonoidHom))
      (by simpa only [U',card_map_of_injective (K := U) (f := e.toMonoidHom) e.injective] using hc)
      (e t) (mem_map_of_mem e.toMonoidHom hz)
      (fun he => ht (e.injective (he.trans (map_one e).symm)))
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp htc x)

/-- The same obstruction retains an arbitrary odd kernel and the literal
involution-centralizer map of a cover of J₄. -/
theorem no_large_elementary_controlled_involution_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* Model) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker))
    (W : Subgroup K) [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : K) (hz : z ∈ W) (hz2 : orderOf z = 2)
    (hn : centralizer ({z} : Set K) ≤ normalizer (W : Set K)) : False := by
  let U := W.map f
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f
  have hi := injective_comp_subtype_of_coprime_ker f hk W (IsElementaryAbelian.isPGroup 2 W)
  have hcardU : Nat.card U = Nat.card W := by
    have he := MonoidHom.ofInjective hi
    have hr : (f.comp W.subtype).range = U := by rw [MonoidHom.range_comp,range_subtype]
    exact (Nat.card_congr (he.trans (MulEquiv.subgroupCongr hr)).toEquiv).symm
  have hz' : orderOf (f z) = 2 := by
    have hh := orderOf_injective (f.comp W.subtype) hi (⟨z,hz⟩ : W)
    exact hh.trans ((Subgroup.orderOf_coe (⟨z,hz⟩ : W)).symm.trans hz2)
  apply no_large_elementary_controlled_involution U (hcardU ▸ hcard)
    (f z) (mem_map_of_mem f hz) hz'
  intro y hy
  obtain ⟨x,hx⟩ := f.elementCentralizerMap_surjective_of_odd_kernel hf hk z hz2 ⟨y,hy⟩
  have he : f x = y := congrArg Subtype.val hx
  exact he ▸ W.le_normalizer_map f (mem_map_of_mem f (hn x.property))

/-- Central two-kernels are allowed when the original elementary subgroup embeds. -/
theorem no_large_elementary_controlled_involution_central_two_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center K) (hp : IsPGroup 2 f.ker)
    (W : Subgroup K) [IsElementaryAbelian 2 W]
    (hi : Function.Injective (f.comp W.subtype))
    (hcard : Nat.card W = 256 ∨ Nat.card W = 1024)
    (z : K) (hz : z ∈ W) (hz2 : orderOf z = 2)
    (hn : centralizer ({z} : Set K) ≤ normalizer (W : Set K)) : False := by
  let U := W.map f
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f
  have hcardU : Nat.card U = Nat.card W := by
    have he := MonoidHom.ofInjective hi
    have hr : (f.comp W.subtype).range = U := by rw [MonoidHom.range_comp,range_subtype]
    exact (Nat.card_congr (he.trans (MulEquiv.subgroupCongr hr)).toEquiv).symm
  have hz' : orderOf (f z) = 2 := by
    have hh := orderOf_injective (f.comp W.subtype) hi (⟨z,hz⟩ : W)
    exact hh.trans ((Subgroup.orderOf_coe (⟨z,hz⟩ : W)).symm.trans hz2)
  obtain ⟨hE,hquot⟩ := f.elementCentralizerMap_normal_pGroup_cokernel hf hk hp z
  let := hE
  let E := (f.elementCentralizerMap z).range
  let C := centralizer ({f z} : Set Model)
  have hUE : U.subgroupOf C ≤ E := by
    intro u hu
    obtain ⟨w,hw,he⟩ := hu
    have hwz : w ∈ centralizer ({z} : Set K) :=
      mem_centralizer_singleton_iff.mpr (setLike_mul_comm hw hz)
    exact ⟨⟨w,hwz⟩,Subtype.ext he⟩
  have hEn : E ≤ normalizer (U.subgroupOf C : Set C) := by
    rintro x ⟨a,rfl⟩ y
    have ha := W.le_normalizer_map f (mem_map_of_mem f (hn a.property))
    exact ha (y : Model)
  exact no_large_elementary_controlled_involution_normal_subgroup U (hcardU ▸ hcard)
    (f z) (mem_map_of_mem f hz) hz' E hquot hUE hEn

end Janko4.InvolutionCentralizers
