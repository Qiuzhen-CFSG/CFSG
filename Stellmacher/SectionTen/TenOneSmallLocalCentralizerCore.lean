module
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCard
public import Stellmacher.SectionTen.TenOneSmallPrimitiveCentralizer
public import Theory.GroupTheory.C4SquareInvolutionBound
public import Stellmacher.SL2TwoTranspositionNormalizer

/-!
# The local centralizer of a noncentral Wstar point has two-core Wstar

In the actual small Section Ten configuration, with first module of order
eight and its specified SL₂(2) quotient, let W₀ be the common middle-neighbor
core inside the generated neighborhood and W*=C_Qmiddle(W₀). For every
a∈W* outside Zmiddle, C_Qmiddle(a)=W* and the two-core of
Gmiddle∩C_G(a) is also W*. The ambient carrier, middle offset and original
subgroups are retained in both conclusions.

The square-one elements of D=O₂(Emiddle), which has model C₄×C₄, are
precisely Zmiddle. The primitive-point centralizer theorem then gives
C_D(a)=Zmiddle. Since Qmiddle=D W* and W* is elementary, factoring elements
through this product gives C_Qmiddle(a)=W*.

The commutator bound [W*,Emiddle]≤Zmiddle embeds the Emiddle orbit of a
into a coset of Zmiddle. Thus its centralizer has index at most four in
the residual of order48. Its quotient kernel has order4, so the local
centralizer image in the actual SL₂(2) quotient has order at least three.
Any nontrivial normal two-subgroup of that image would have order two;
its self-normalizing property in SL₂(2) would force the entire image to
have order at most two. This excludes any additional two-core image.
Normality and elementary structure of W* give the reverse containment.

Source: Stellmacher (10.1)(a3), Journal of Algebra190 (1997), printed p.62,
the local structure used after (9) and C_Qmiddle(a)=W* used before (11).
The global centralizer containment and source-(9) normalizer identification
are separate results; no full-stabilizer factorization is assumed here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative commutatorElement Pointwise
universe u

private theorem centralizer_index_le_displacement_card
    {R : Type*} [Group R] [Finite R] (E Z : Subgroup R) (a:R)
    (hcomm : ∀ e∈E,⁅e,a⁆∈Z) :
    (Subgroup.centralizer ({a}:Set R)).relIndex E ≤ Nat.card Z := by
  let action : E →* MulAut R := MulAut.conj.comp E.subtype
  let actionInstance : MulDistribMulAction E R := MulDistribMulAction.compHom R action
  let _ : SMul E R := actionInstance.toSMul
  let _ : MulAction E R := actionInstance.toMulAction
  have hstab : MulAction.stabilizer E a = (Subgroup.centralizer ({a}:Set R)).subgroupOf E := by
    ext e
    rw [MulAction.mem_stabilizer_iff,Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    change (e:R)*a*(e:R)⁻¹=a ↔ (e:R)*a=a*(e:R)
    exact mul_inv_eq_iff_eq_mul
  let f : MulAction.orbit E a → Z := fun y => ⟨(y:R)*a⁻¹,by
    obtain ⟨e,he⟩ := y.property
    rw [←he]
    exact hcomm e e.property⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective f hinj
  have heq := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer E a)
  rw [hstab] at heq
  change Nat.card (MulAction.orbit E a) = (Subgroup.centralizer ({a}:Set R)).relIndex E at heq
  exact heq ▸ hcard

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_core_point_centralizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    ∀ a:G, a∈Wstar → a∉ZAt ctx.Γ middle →
      QAt ctx.Γ middle ⊓ Subgroup.centralizer ({a}:Set G) = Wstar := by
  classical
  let M := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  let Z := ZAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  change ∀ a:G, a∈Wstar → a∉Z → Q⊓Subgroup.centralizer ({a}:Set G)=Wstar
  intro a ha haZ
  have hp := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  let _ : IsElementaryAbelian 2 Wstar := hp.2.1
  have hWD : Wstar⊓D=Z := hp.2.2.2.1
  have hZD : Z≤D := hWD ▸ inf_le_right
  have hZW : Z≤Wstar := hWD ▸ inf_le_left
  have hWc : Wstar≤Subgroup.centralizer ({a}:Set G) :=
    (Subgroup.le_centralizer Wstar).trans (Subgroup.centralizer_le (by simpa using ha))
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  obtain ⟨model⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
  let _ : CommGroup D := model.toMonoidHom.commGroupOfInjective model.injective
  let squares : D→*D := powMonoidHom 2
  have hZker : Z.subgroupOf D≤squares.ker := by
    intro z hz
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Wstar) z (hZW hz)
  have hkerCard : Nat.card squares.ker≤4 :=
    Subgroup.card_le_four_of_c4_square_square_one ⟨model⟩ squares.ker (fun _ h => h)
  have hZkerEq : Z.subgroupOf D=squares.ker := Subgroup.eq_of_le_of_card_ge hZker (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,hZcard]
    exact hkerCard)
  have hinvol (d:G) (hd:d∈D) (hs:d^2=1) : d∈Z := by
    have hh : (⟨d,hd⟩:D)∈squares.ker := Subtype.ext hs
    rwa [←hZkerEq] at hh
  have hDc : D⊓Subgroup.centralizer ({a}:Set G)=Z := by
    refine le_antisymm ?_ (le_inf hZD (hZW.trans hWc))
    intro d hd
    by_contra hdZ
    have hd2 : d^2≠1 := fun hh => hdZ (hinvol d hd.1 hh)
    have hac : a∈Subgroup.centralizer ({d}:Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro x (rfl : x=d)
      exact (Subgroup.mem_centralizer_iff.mp hd.2 a (Set.mem_singleton a)).symm
    exact haZ ((ten_one_small_primitive_wstar_centralizer ctx middle hpath hsmall hmodel
      d hd.1 hd2).le ⟨ha,hac⟩)
  have hQM : Q≤M := by
    change ctx.Γ.twoCoreAt middle≤_
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le M
  have hDQ : D≤Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle)≤ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hgen : Q=Wstar⊔D :=
    (ten_one_small_middle_core_residual_centralizer_product ctx middle hpath hsmall hmodel).trans
      (sup_comm D Wstar)
  have hnormal : D≤Subgroup.normalizer (Wstar:Set G) := (hDQ.trans hQM).trans hp.1
  refine le_antisymm ?_ (le_inf inf_le_left hWc)
  intro q hq
  have hm : q∈(Wstar:Set G)*(D:Set G) := by
    rw [←Subgroup.coe_mul_of_right_le_normalizer_left Wstar D hnormal,←hgen]
    exact hq.1
  obtain ⟨w,hw,d,hd,rfl⟩ := hm
  have hdc : d∈Subgroup.centralizer ({a}:Set G) := by
    have hh := (Subgroup.centralizer ({a}:Set G)).mul_mem
      ((Subgroup.centralizer ({a}:Set G)).inv_mem (hWc hw)) hq.2
    simpa only [inv_mul_cancel_left] using hh
  exact Wstar.mul_mem hw (hZW (hDc.le ⟨hd,hdc⟩))

public theorem ten_one_small_local_centralizer_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    ∀ a:G, a∈Wstar → a∉ZAt ctx.Γ middle →
      twoCoreIn (GAt ctx.Γ middle ⊓ Subgroup.centralizer ({a}:Set G)) = Wstar := by
  classical
  let M := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  let Z := ZAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  change ∀ a:G, a∈Wstar → a∉Z → twoCoreIn (M⊓Subgroup.centralizer ({a}:Set G))=Wstar
  intro a ha haZ
  let C := Subgroup.centralizer ({a}:Set G)
  let L := M⊓C
  let J := E⊓C
  have hp := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  let _ : IsElementaryAbelian 2 Wstar := hp.2.1
  have hWD : Wstar⊓D=Z := hp.2.2.2.1
  have hZD : Z≤D := hWD ▸ inf_le_right
  have hZW : Z≤Wstar := hWD ▸ inf_le_left
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hWc : Wstar≤C :=
    (Subgroup.le_centralizer Wstar).trans (Subgroup.centralizer_le (by simpa using ha))
  have hQc : Q⊓C=Wstar := ten_one_small_core_point_centralizer ctx middle hpath hsmall hmodel a ha haZ
  have hQM : Q≤M := by
    change ctx.Γ.twoCoreAt middle≤_
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le M
  have hEM : E≤M := by
    change ctx.Γ.twoResidualAt middle≤_
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le M
  have hDE : D≤E := twoCoreIn_le E
  have hDEQ : D=E⊓Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle)=ctx.Γ.twoResidualAt middle⊓ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
  have hDc : D⊓C=Z := by
    rw [hDEQ,inf_assoc, hQc]
    rw [←hWD,hDEQ]
    apply le_antisymm
    · exact le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
  have hJM : J≤M := inf_le_left.trans hEM
  have hJL : J≤L := le_inf hJM inf_le_right
  have hZJ : Z≤J := le_inf (hZD.trans hDE) (hZW.trans hWc)
  have hWL : Wstar≤L := le_inf (inf_le_left.trans hQM) hWc
  obtain ⟨f,hf,hker⟩ := (sectionTenOpeningData ctx middle hpath).quotient_model
  let Qm := pCore 2 M
  let Em := twoResidualAmbient (⊤:Subgroup M)
  let Dm := Em⊓Qm
  have hEmap : Em.map M.subtype=E := by
    have hh := map_twoResidualAmbient_of_subgroup_image (⊤:Subgroup M) M.subtype M
      (by rw [←MonoidHom.range_eq_map,Subgroup.range_subtype])
    exact hh.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Qm.map M.subtype=Q := (ctx.Γ.twoCoreAt_def middle).symm
  obtain ⟨_,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  have hDmcard : Nat.card Dm=16 := by
    obtain ⟨e⟩ := hc4
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  have hrel : Dm.relIndex Em=3 := by
    change (Em⊓Qm).relIndex Em=3
    rw [inf_comm,Subgroup.inf_relIndex_right]
    have hh := Subgroup.relIndex_ker (K:=Em) (QuotientGroup.mk' Qm)
    rw [QuotientGroup.ker_mk'] at hh
    exact hh.trans himage
  have hEcard : Nat.card E=48 := by
    have hh := (Dm.subgroupOf Em).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Dm≤Em from inf_le_left)).toEquiv,
      hDmcard] at hh
    change 16*Dm.relIndex Em=Nat.card Em at hh
    rw [hrel] at hh
    rw [←hEmap,Subgroup.card_map_of_injective M.subtype_injective]
    omega
  have hindex : C.relIndex E≤4 := by
    rw [←hZcard]
    apply centralizer_index_le_displacement_card E Z a
    intro e he
    rw [←commutatorElement_inv]
    exact Z.inv_mem (hp.2.2.2.2 (Subgroup.commutator_mem_commutator ha he))
  have hJlower : 12≤Nat.card J := by
    have hh := (J.subgroupOf E).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show J≤E from inf_le_left)).toEquiv] at hh
    change Nat.card J*J.relIndex E=Nat.card E at hh
    have hi : J.relIndex E=C.relIndex E := by
      change (E⊓C).relIndex E=C.relIndex E
      rw [inf_comm,Subgroup.inf_relIndex_right]
    rw [hi,hEcard] at hh
    nlinarith
  let fJ : J→*SL2Two := f.comp (Subgroup.inclusion hJM)
  let fL : L→*SL2Two := f.comp (Subgroup.inclusion (show L≤M from inf_le_left))
  have hJker : fJ.ker=Z.subgroupOf J := by
    ext j
    change f (⟨(j:G),hJM j.property⟩:M)=1 ↔ (j:G)∈Z
    rw [←MonoidHom.mem_ker,hker]
    change (j:G)∈Q ↔ (j:G)∈Z
    constructor
    · intro hjQ
      apply hDc.le
      exact ⟨hDEQ.ge ⟨j.property.1,hjQ⟩,j.property.2⟩
    · exact fun hz => (show Wstar≤Q from inf_le_left) (hZW hz)
  have hJkerCard : Nat.card fJ.ker=4 := by
    rw [hJker,Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv,hZcard]
  have hJimageLower : 3≤Nat.card fJ.range := by
    have hh := fJ.ker.index_mul_card
    rw [Subgroup.index_ker,hJkerCard] at hh
    nlinarith
  have himages : fJ.range≤fL.range := by
    rintro _ ⟨j,rfl⟩
    exact ⟨⟨j,hJL j.property⟩,rfl⟩
  have hLimageLower : 3≤Nat.card fL.range := hJimageLower.trans
    (Nat.card_le_card_of_injective (Subgroup.inclusion himages) (Subgroup.inclusion_injective himages))
  let N := (pCore 2 L).map fL
  have hNp : IsPGroup 2 N := pCore_isPGroup.map fL
  have hNdiv : Nat.card N∣6 := by
    have hh := N.card_subgroup_dvd_card
    rwa [SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hh
  have hNcop : Nat.Coprime (Nat.card N) 3 := by
    obtain ⟨n,hn⟩ := hNp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hNdivTwo : Nat.card N∣2 := hNcop.dvd_mul_right.mp hNdiv
  have hNbot : N=⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hNdivTwo with h | h
    · exact Subgroup.card_eq_one.mp h
    have hnorm : fL.range≤Subgroup.normalizer (N:Set SL2Two) := by
      have hh := (pCore 2 L).le_normalizer_map fL
      rw [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map] at hh
      exact hh
    rw [Stellmacher.sl2Two_normalizer_eq_of_card_two N h] at hnorm
    have hh := Nat.card_le_card_of_injective (Subgroup.inclusion hnorm) (Subgroup.inclusion_injective hnorm)
    rw [h] at hh
    omega
  refine le_antisymm ?_ ?_
  · rintro x ⟨l,hl,rfl⟩
    have hf0 : fL l=1 := by
      have hh : fL l∈N := Subgroup.mem_map_of_mem fL hl
      rw [hNbot] at hh
      exact hh
    have hlQ : (l:G)∈Q := by
      have hh : (⟨(l:G),l.property.1⟩:M)∈f.ker := hf0
      rw [hker] at hh
      exact hh
    exact hQc.le ⟨hlQ,l.property.2⟩
  · have hnormal : (Wstar.subgroupOf L).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer ((show L≤M from inf_le_left).trans hp.1)
    have htwo : IsPGroup 2 (Wstar.subgroupOf L) :=
      (IsElementaryAbelian.isPGroup 2 Wstar).of_equiv (Subgroup.subgroupOfEquivOfLe hWL).symm
    have hle : Wstar.subgroupOf L≤pCore 2 L := le_sSup ⟨hnormal,htwo⟩
    rw [←Subgroup.map_subgroupOf_eq_of_le hWL]
    exact Subgroup.map_mono hle

end Stellmacher.SectionTen
