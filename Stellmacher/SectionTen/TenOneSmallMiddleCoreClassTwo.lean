module
public import Stellmacher.SectionTen.TenOneSmallSylowUpper
public import Theory.GroupTheory.CenterFreeOddResidualClassTwo
public import Theory.GroupAction.ExponentFourFixedInvolutions

/-!
# The small middle core is abelian modulo its center

When the first neighboring module has order eight and its local quotient
is SL₂(2), the commutator subgroup of the actual middle two-core lies in
its middle center. The companion theorem gives a normality witness and
commutativity of the literal quotient of that core by the middle center.

Inside the middle stabilizer M, put E=O²(M), Q=O₂(M), and R=E∩Q.
The existing native packet gives Z(M)=1, R≃C₄×C₄, and an odd E-image
modulo Q. The middle center Z has order four and is exactly the square-one
subgroup of R. Since Q centralizes Z, its conjugation on R fixes every
involution. The exponent-four action lemma puts every displacement in Z.
The center-free odd-residual class-two theorem then gives [Q,Q]≤Z;
subtype transport returns the asserted ambient commutator containment.

Source: Stellmacher (10.1)(a3), printed p.61, just before the normalizer
identity (7), in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_middle_core_commutator_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ⁅QAt ctx.Γ middle,QAt ctx.Γ middle⁆ ≤ ZAt ctx.Γ middle := by
  classical
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let R := E ⊓ Q
  let Z := (ZAt ctx.Γ middle).subgroupOf M
  let D := twoCoreIn (EAt ctx.Γ middle)
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  have hEmap : E.map M.subtype = EAt ctx.Γ middle := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) M.subtype M
      (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    exact hm.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Q.map M.subtype = QAt ctx.Γ middle :=
    (ctx.Γ.twoCoreAt_def middle).symm
  have hRmap : R.map M.subtype = D := by
    rw [Subgroup.map_inf E Q M.subtype M.subtype_injective,hEmap,hQmap]
    change ctx.Γ.twoResidualAt middle ⊓ ctx.Γ.twoCoreAt middle =
      twoCoreIn (ctx.Γ.twoResidualAt middle)
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
  have hZmiddleQ : ZAt ctx.Γ middle ≤ QAt ctx.Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  have hQmiddleM : QAt ctx.Γ middle ≤ M := hQmap ▸ Subgroup.map_subtype_le Q
  have hZmiddleM : ZAt ctx.Γ middle ≤ M := hZmiddleQ.trans hQmiddleM
  have hZmap : Z.map M.subtype = ZAt ctx.Γ middle :=
    Subgroup.map_subgroupOf_eq_of_le hZmiddleM
  let _ : Z.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZmiddleM).mpr
      (stabilizer_le_normalizer_z ctx.Γ middle)
  have hZR : Z ≤ R := by
    intro z hz
    have hh := ten_one_middle_center_le_residual_core ctx middle hpath hz
    change (z:G) ∈ D at hh
    rw [← hRmap] at hh
    obtain ⟨r,hr,heq⟩ := hh
    exact (M.subtype_injective heq) ▸ hr
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set M) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hZcent : ZAt ctx.Γ middle ≤ Subgroup.centralizer (QAt ctx.Γ middle : Set G) := by
      rw [(sectionTenOpeningData ctx middle hpath).center_omega]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    exact Subgroup.mem_centralizer_iff.mp (hZcent hz) q
      (hQmap ▸ Subgroup.mem_map_of_mem M.subtype hq)
  have hZcard : Nat.card Z = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZmiddleM).toEquiv]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  let _ : IsElementaryAbelian 2 (ZAt ctx.Γ middle) := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZmiddleM
  obtain ⟨equiv⟩ := hc4
  let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
  let squares : R →* R := powMonoidHom 2
  have hZker : Z.subgroupOf R ≤ squares.ker := by
    intro z hz
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Z) z hz
  have hkerCard : Nat.card squares.ker ≤ 4 := by
    let f : squares.ker → {v : C4 × C4 // v^2=1} := fun x =>
      ⟨equiv x,by rw [← map_pow]; exact (congrArg equiv x.property).trans equiv.map_one⟩
    have hfinj : Function.Injective f := by
      intro x y hh
      exact Subtype.ext (equiv.injective (congrArg Subtype.val hh))
    have hcard : Nat.card {v : C4 × C4 // v^2=1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact hcard ▸ Nat.card_le_card_of_injective f hfinj
  have hZkerEq : Z.subgroupOf R = squares.ker := by
    apply Subgroup.eq_of_le_of_card_ge hZker
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv,hZcard]
    exact hkerCard
  have hfull (r : R) (hr : r^2=1) : (r:M) ∈ Z := by
    have hh : r ∈ squares.ker := hr
    rwa [← hZkerEq] at hh
  have hfour : ∀ r : R, r^4=1 := by
    intro r
    apply equiv.injective
    rw [map_pow,map_one]
    exact (show ∀ x : C4 × C4, x^4=1 by decide) (equiv r)
  let action : M →* MulAut R := MulAut.conjNormal
  have hfix : ∀ a ∈ Q.map action, ∀ r : R, r^2=1 → a r=r := by
    rintro _ ⟨q,hq,rfl⟩ r hr
    apply Subtype.ext
    change q * (r:M) * q⁻¹ = (r:M)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hZcentral (hfull r hr)) q hq
    rw [hcomm,mul_inv_cancel_right]
  have hdelta := (MulAut.elementaryTwo_of_fixed_involutions hfour (Q.map action) hfix).2
  have hRQ : ⁅R,Q⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro q hq r hr
    exact hfull ((action q) ⟨r,hr⟩ * (⟨r,hr⟩:R)⁻¹)
      (hdelta (action q) (Subgroup.mem_map_of_mem action hq) ⟨r,hr⟩)
  have hQQ : ⁅Q,Q⁆ ≤ Z :=
    Subgroup.commutator_le_of_centerfree_odd_residual_central_layer
      (default : Sylow 2 M) E Q Z (twoResidualAmbient_top_sup_sylow _)
      (pCore_isPGroup (p:=2) (G:=M)) hcenter (by rw [himage]; decide) hZcentral hRQ
  have hm := Subgroup.map_mono (f:=M.subtype) hQQ
  rw [Subgroup.map_commutator,hQmap,hZmap] at hm
  exact hm

public theorem ten_one_small_middle_core_quotient_commutative
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃ hN : ((ZAt ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)).Normal,
      let _ := hN
      IsMulCommutative (QAt ctx.Γ middle ⧸
        (ZAt ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)) := by
  let Q := QAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  have hQM : Q ≤ GAt ctx.Γ middle := by
    change ctx.Γ.twoCoreAt middle ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hN : (Z.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (hQM.trans (stabilizer_le_normalizer_z ctx.Γ middle))
  let _ := hN
  refine ⟨hN,Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_⟩
  intro q hq
  apply ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel
  rw [← Subgroup.map_subtype_commutator Q]
  exact Subgroup.mem_map_of_mem Q.subtype hq

end Stellmacher.SectionTen
