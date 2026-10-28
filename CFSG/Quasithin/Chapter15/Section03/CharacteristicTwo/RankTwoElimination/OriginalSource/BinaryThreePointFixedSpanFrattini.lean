module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCoordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSynchronizedCubic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanMiddleIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanSmallRows
public import Theory.Representation.BinaryFifteenPoint.SingerCoordinates
public import Theory.Representation.BinaryFifteenPoint.SingerQuotientRanks
public import Theory.Representation.BinarySingerCubic

public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation Polynomial
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryEndpointInduction
set_option linter.style.haveILetI false
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [Group G]

private def actor (L U : Subgroup G) (hLU : L ≤ normalizer U) : L →* MulAut U :=
  U.normalizerMonoidHom.comp (inclusion hLU)

private theorem cubic_surjective_of_inverse_reciprocal_injective
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) G E) (s : G)
    (hi : Function.Injective ((σ s⁻¹)^3+(σ s⁻¹)^2+1 : Module.End (ZMod 2) E)) :
    Function.Surjective ((σ s)^3+σ s+1 : Module.End (ZMod 2) E) := by
  have h33 : (σ s)^3*(σ s⁻¹)^3=1 := by
    have hh : s^3*(s⁻¹)^3=1 := by group
    simpa only [map_mul,map_pow,map_one] using congrArg σ hh
  have h32 : (σ s)^3*(σ s⁻¹)^2=σ s := by
    have hh : s^3*(s⁻¹)^2=s := by group
    simpa only [map_mul,map_pow] using congrArg σ hh
  have he : (σ s)^3+σ s+1=(σ s)^3*((σ s⁻¹)^3+(σ s⁻¹)^2+1) := by
    rw [mul_add,mul_add,h33,h32,mul_one]
    abel
  have hpow : Function.Injective ((σ s)^3 : Module.End (ZMod 2) E) := by
    rw [←map_pow]
    exact (σ.apply_bijective _).injective
  rw [he]
  exact Finite.surjective_of_injective (hpow.comp hi)

private theorem hom_trivial_of_cubic_surjective
    {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    {U : Type*} [Group U] (A : G →* MulAut U)
    (p : U →* Multiplicative E) (hp : Function.Surjective p)
    (q : U →* Multiplicative F) (hk : p.ker ≤ q.ker)
    (σ : Representation (ZMod 2) G E) (τ : Representation (ZMod 2) G F)
    (hσ : ∀ g u, (p (A g u)).toAdd=σ g (p u).toAdd)
    (hτ : ∀ g u, (q (A g u)).toAdd=τ g (q u).toAdd)
    (s : G) (honto : Function.Surjective ((σ s)^3+σ s+1 : Module.End (ZMod 2) E))
    (hzero : (τ s)^3+τ s+1=0) : ∀ u : U, q u=1 := by
  intro u
  obtain ⟨x,hx⟩ := honto (p u).toAdd
  obtain ⟨v,hv⟩ := hp (Multiplicative.ofAdd x)
  let w := A (s^3) v * A s v * v
  have hpw : p w=p u := by
    dsimp [w]
    rw [map_mul p, map_mul p]
    change (p (A (s^3) v)).toAdd + (p (A s v)).toAdd + (p v).toAdd = (p u).toAdd
    rw [hσ, hσ, map_pow]
    have hv' : (p v).toAdd=x := congrArg Multiplicative.toAdd hv
    rw [hv']
    exact hx
  have hqw : q w=1 := by
    dsimp [w]
    rw [map_mul q, map_mul q]
    change (q (A (s^3) v)).toAdd + (q (A s v)).toAdd + (q v).toAdd = 0
    rw [hτ, hτ, map_pow]
    exact LinearMap.congr_fun hzero (q v).toAdd
  have hw : u/w ∈ p.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [_root_.map_div,hpw,div_self']
  have hq := MonoidHom.mem_ker.mp (hk hw)
  rw [_root_.map_div,hqw,div_one] at hq
  simpa using hq

private theorem reciprocal_kernel_zero
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (F : (Fin 15 → ZMod 2) →ₗ[ZMod 2] E) (hF : Function.Surjective F)
    (r : Fin 8) (hk : F.ker=BinaryFifteenPoint.invariantSubspace r)
    (A : Module.End (ZMod 2) E)
    (hA : ∀ x, F (x ᵥ* BinaryFifteenPoint.singerMatrix)=A (F x))
    (hdim : Module.finrank (ZMod 2) E=1 ∨ Module.finrank (ZMod 2) E=4 ∨ Module.finrank (ZMod 2) E=5)
    (hdimrow : Module.finrank (ZMod 2) E + BinaryFifteenPoint.rowDimension r=15) :
    Function.Injective (A^3+A^2+1 : Module.End (ZMod 2) E) := by
  have hr := BinaryFifteenPoint.quotient_singer_cubic_kernel_finrank r F hF hk A hA true
  have hpoly : (A^3+A^2+1 : Module.End (ZMod 2) E) =
      aeval A (Polynomial.X^3+Polynomial.X^2+1 : (ZMod 2)[X]) := by
    simp only [map_add,map_pow,map_one,Polynomial.aeval_X]
  rw [show BinaryFifteenPoint.singerCubic true = Polynomial.X^3+Polynomial.X^2+1 by rfl, ←hpoly] at hr
  have hrank : BinaryFifteenPoint.singerCubicKernelDimension true r=0 := by
    rcases hdim with hdim|hdim|hdim <;> fin_cases r <;>
      norm_num [BinaryFifteenPoint.rowDimension, BinaryFifteenPoint.singerCubicKernelDimension] at hdimrow ⊢ <;> omega
  have hzero : Module.finrank (ZMod 2) (LinearMap.ker
      (A^3+A^2+1 : Module.End (ZMod 2) E))=0 := hr.trans hrank
  exact (LinearMap.ker_eq_bot).mp ((Submodule.finrank_eq_zero).mp hzero)

private theorem q_section_coordinates
    {E : Type*} [Group E] {L Q D : Subgroup G}
    {a : L →* E} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) E W}
    (h : HasSectionModel L Q D a τ) :
    ∃ q : Q →* Multiplicative W, Function.Surjective q ∧
      q.ker=D.subgroupOf Q ∧
      ∀ (l : L) (u : Q),
        (q (Q.normalizerMonoidHom (inclusion h.2.1 l) u)).toAdd=
          τ (a l) (q u).toAdd := by
  obtain ⟨_,_,_,hn,e,he⟩ := h
  letI := hn
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (D.subgroupOf Q))
  refine ⟨q,e.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  · intro l u
    exact he l u _ rfl

variable [Finite G]

set_option maxHeartbeats 1000000 in
/-- The actual natural-four fixed span lies in the original doubled-natural
Frattini kernel after the synchronized Singer cubic and exact fifteen-row cut. -/
theorem binary_three_source_fixed_span_frattini
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let D := Q ⊓ centralizer (Phi : Set G)
    let U := conjugateSpanBy (intrinsicFour c.L) C
    U ≤ D ∧ U ≤ Phi := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H C
  let Z := zpowers z
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hLU : c.L ≤ normalizer U := hLC.trans (le_normalizer_conjugateSpanBy _ _)
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz,orderOf_one] at hz2
    norm_num at hz2
  obtain ⟨f,β,hfs,hfq,hβ,hβk,eK,heK,s,k,hs7,hso,hk,hks,hseed,hphi,hmid,htop,hmatrix,hnatural,hdouble⟩ :=
    binary_three_source_endpoint_synchronized_cubic
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1
  obtain ⟨hZ,hel,ρ,hρ,h,hw,hfix,hspan,hcoords⟩ := binary_three_source_fixed_span_coordinates
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  let := hZ
  let := hel
  let w := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
    (inclusion (le_conjugateSpanBy H C) h))
  let E := Additive (U ⧸ Z.subgroupOf U)
  have hUQ : U ≤ Q := binary_three_source_fixed_span_le_core
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  obtain ⟨F,hF,hFi,hFa,r,hr,hdimrow⟩ := hcoords eK heK
  have hUcardle : Nat.card U ≤ 256 :=
    (binary_three_source_fixed_span_center_bound
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm).2.2.2
  have hEcard : Nat.card E ≤ 256 := (Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (Z.subgroupOf U)) (QuotientGroup.mk'_surjective _)).trans hUcardle
  have hdimle : Module.finrank (ZMod 2) E ≤ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hEcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hEcard
  have hpos : 0 < Module.finrank (ZMod 2) E :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_,hw⟩
  have hdimrow' := hdimrow
  change Module.finrank (ZMod 2) E + BinaryFifteenPoint.rowDimension r=15 at hdimrow'
  have hdim : Module.finrank (ZMod 2) E=1 ∨
      Module.finrank (ZMod 2) E=4 ∨ Module.finrank (ZMod 2) E=5 := by
    fin_cases r <;> norm_num [BinaryFifteenPoint.rowDimension] at hdimrow' <;> omega
  let τ := elementaryRepresentation (p := 2) (ρ.comp K.subtype)
  let τ' := τ.comp eK.symm.toMonoidHom
  have hfix' (p0 : BinaryEndpointInduction.endpointParabolic) : τ' p0.val w=w := by
    have hp0 : p0.val ∈ (B.subgroupOf K).map eK.toMonoidHom := heK.symm ▸ p0.property
    have hb0 : eK.symm p0.val ∈ B.subgroupOf K := (mem_map_equiv).mp hp0
    exact hfix ⟨eK.symm p0.val,hb0⟩
  have hSinger := BinaryFifteenPoint.singer_intertwining_of_seed τ' w hfix' F hFi
  let σ := elementaryRepresentation (p := 2) (ρ.comp (q.comp (inclusion hLC)))
  have hσs : τ' BinaryFifteenPoint.singerActor⁻¹ = σ s⁻¹ := by
    apply LinearMap.ext
    intro x
    change τ (eK.symm (BinaryFifteenPoint.singerActor⁻¹)) x = _
    have heq : eK.symm BinaryFifteenPoint.singerActor=k := by
      apply (eK.symm_apply_eq).2
      rw [show BinaryFifteenPoint.singerActor=BinarySingerPrimary.endpointSinger by decide +kernel, hks]
    have heqinv : eK.symm (BinaryFifteenPoint.singerActor⁻¹)=k⁻¹ := by
      rw [map_inv,heq]
    rw [heqinv]
    change elementaryRepresentation (ρ.comp K.subtype) (k⁻¹) x = _
    change elementaryRepresentation ρ ((k : C ⧸ pCore 2 C)⁻¹) x = _
    rw [hk]
    rfl
  have hA : ∀ x, F (x ᵥ* BinaryFifteenPoint.singerMatrix)=σ s⁻¹ (F x) := by
    intro x
    rw [←hσs]
    exact hSinger x
  have hinj : Function.Injective ((σ s⁻¹)^3+(σ s⁻¹)^2+1 : Module.End (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) :=
    reciprocal_kernel_zero F hF r hr _ hA hdim hdimrow
  have honto := cubic_surjective_of_inverse_reciprocal_injective σ s hinj
  obtain ⟨hDQ,hLQ,hLD,hn,eQ,heQ⟩ := htop
  letI := hn
  let q0 : Q →* Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (D.subgroupOf Q))
  let qU := q0.comp (inclusion hUQ)
  have hqker : q0.ker=D.subgroupOf Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ eQ.injective,QuotientGroup.ker_mk']
  have hqact (l : c.L) (u : U) :
      (qU (actor c.L U hLU l u)).toAdd =
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural 3) (β (f l))) (qU u).toAdd := by
    exact heQ l (inclusion hUQ u) (inclusion hUQ (actor c.L U hLU l u)) rfl
  let p : U →* Multiplicative (Additive (U ⧸ Z.subgroupOf U)) :=
    MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Z.subgroupOf U))
  have hp : Function.Surjective p := MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hpk : p.ker=Z.subgroupOf U := by
    ext x
    change p x=1 ↔ x ∈ Z.subgroupOf U
    change (QuotientGroup.mk' (Z.subgroupOf U) x)=1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hps (l : c.L) (u : U) : (p (actor c.L U hLU l u)).toAdd=σ l (p u).toAdd := by
    apply Additive.toMul.injective
    exact (hρ ⟨l,hLC l.property⟩ u (actor c.L U hLU l u) rfl).symm
  have hZcore : H ≤ coreCenter c.L := by
    obtain ⟨common⟩ := t.commonFacts hc
    have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
    have hHF := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hcoreQ : coreCenter c.L ≤ Q := map_subtype_le _
  have hcorePhi : coreCenter c.L ≤ Phi := by
    change (center Q).map Q.subtype ≤ (frattini Q).map Q.subtype
    exact map_mono (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.1
  have hcoreCent : coreCenter c.L ≤ centralizer (Phi : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    have hPhiQ : Phi ≤ Q := map_subtype_le _
    have hyQ : y ∈ Q := hPhiQ hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hyQ⟩)
  have hHD : H ≤ D := le_inf (hZcore.trans hcoreQ) (hZcore.trans hcoreCent)
  have hZD : Z ≤ D := (zpowers_le.mpr hzH).trans hHD
  have hpkq : p.ker ≤ qU.ker := by
    rw [hpk]
    intro u hu
    apply MonoidHom.mem_ker.mpr
    change q0 (inclusion hUQ ⟨(u : U),u.property⟩)=1
    have hmem : inclusion hUQ ⟨(u : U),u.property⟩ ∈ q0.ker := by
      rw [hqker]
      exact ⟨hUQ u.property, (hZD (show (u : G) ∈ Z from hu)).2⟩
    exact MonoidHom.mem_ker.mp hmem
  let a := β.comp f
  let τ0 := (Representation.specialLinearNatural (k := ZMod 2) 3).prod
      (Representation.specialLinearNatural 3)
  have hqtau (l : c.L) (u : U) : (qU (actor c.L U hLU l u)).toAdd =
      (τ0.comp a) l (qU u).toAdd := by exact hqact l u
  have hzero : (τ0.comp a) s ^ 3 + (τ0.comp a) s + 1=0 := by
    simpa [τ0, a, BinarySingerPrimary.cubic] using hdouble
  have htriv := hom_trivial_of_cubic_surjective (G:=c.L) (U:=U) (A:=actor c.L U hLU)
    p hp qU hpkq σ (τ0.comp a) hps hqtau s honto hzero
  have hUD : U ≤ D := by
    intro u hu
    have hq := htriv ⟨u,hu⟩
    have hq' : q0 (inclusion hUQ ⟨u,hu⟩)=1 := hq
    have hq'' : (inclusion hUQ ⟨u,hu⟩ : Q) ∈ D.subgroupOf Q := by
      rw [←hqker]
      exact hq'
    change (u : G) ∈ D at hq''
    exact hq''
  obtain ⟨hMD,_,_⟩ := binary_three_source_fixed_span_middle_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1
  have hUPhi : U ≤ Phi := by
    intro u hu
    have hh : u ∈ U ⊓ D := ⟨hu,hUD hu⟩
    have hh' : u ∈ U ⊓ Phi := hMD ▸ hh
    exact hh'.2
  exact ⟨hUD,hUPhi⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
