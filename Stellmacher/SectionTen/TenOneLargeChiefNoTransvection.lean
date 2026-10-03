module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure
public import Stellmacher.SectionTen.TenOneLargeNoncentralChiefFactor
public import Stellmacher.SectionThree.SmallResidualImageCard
public import Stellmacher.SectionOne.RankOneOddPGroupCyclicThree
public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupAction.CardTwoDisplacementInvolution

/-!
# No transvection on the actual noncentral chief quotient

Retain the selected source-(13) actor and the supplied terminal quotient
action. On any irreducible elementary-two action of the terminal stabilizer
whose residual acts nontrivially, that actor has displacement different from
two. The companion theorem applies this transfer to the intrinsic noncentral
chief quotient of O₂(E_terminal)/V_terminal, preserving its actual denominator,
normality instance, quotient-conjugation formula and action.

Irreducibility makes the chief action range core-free and puts the terminal
two-core in its kernel. Source (14) identifies the residual in the canonical
terminal core quotient as C₅ or C₃×C₃. The small residual-image theorem
preserves its order five or nine through the noncentral chief action. Factor
the source-(13) commutator generation through the original literal action
range into that same chief action; its canonical odd commutator equals this
preserved residual image. A rank-one involution displacement would make that
canonical odd p-group cyclic of order three by (1.3), a contradiction.

This proves the no-transvection implication between (14) and (15) of
Stellmacher (10.1), printed p.63 of `refs/files/stellmacher-n-group.pdf`.
It supplies no residual-core intersection index or W-containment; those are
subsequent consequences requiring the actual core/neighbor commutator step.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_chief_displacement_ne_two
    {Wc : Type u} [Group Wc] [Finite Wc] [IsElementaryAbelian 2 Wc] [Nontrivial Wc]
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))

    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hcard : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆)
    (hno : ∀ element : G, element ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      element ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers element⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (chief : GAt ctx.Γ ctx.criticalPath.a' →* MulAut Wc)
    (hirr : ∀ K : Subgroup Wc, (∀ g : GAt ctx.Γ ctx.criticalPath.a',
      ∀ w : Wc, w∈K → chief g w∈K) → K=⊥ ∨ K=⊤)
    (hres : ¬ (EAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a') ≤ chief.ker) :
    Nat.card (commutatorAction (Subgroup.zpowers (chief actor)) Wc) ≠ 2 := by
  intro hrank
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let q := QuotientGroup.mk' (pCore 2 P)
  let R0 := (twoResidualSubgroup P).map q
  let K := chief.range
  let f := chief.rangeRestrict
  let R := (twoResidualSubgroup P).map f
  have hnative : E.subgroupOf P=twoResidualSubgroup P := by
    dsimp only [E,P]
    rw [EAt,CosetGraphContext.e,ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hirrR : ∀ D : Subgroup Wc, (∀ g:K, ∀ w:Wc, w∈D → g • w∈D) → D=⊥ ∨ D=⊤ := by
    intro D hD
    exact hirr D (fun g w hw => hD (chief.rangeRestrict g) w hw)
  have hcore : pCore 2 P ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact irreducible_range_core_le_ker chief hirrR
  have hnot : ¬ twoResidualSubgroup P ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict,←hnative]
    exact hres
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  let edge := P ⊓ GAt ctx.Γ middle
  let sylow : Sylow 2 edge := default
  let Sedge := sylowTwoAmbient edge sylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) sylow
  have hmodels : Nonempty (R0 ≃* (C3×C3)) ∨ Nonempty (R0 ≃* C5) := by
    have hh := (ten_one_large_terminal_structure ctx middle hpath hno).1
    change Nonempty (((E.subgroupOf P).map q) ≃* (C3×C3)) ∨
      Nonempty (((E.subgroupOf P).map q) ≃* C5) at hh
    rwa [hnative] at hh
  have hthree : Nat.card C3=3 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num)
  have hfive : Nat.card C5=5 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5)).trans (by norm_num)
  have hnine : Nat.card (C3×C3)=9 := by rw [Nat.card_prod,hthree]
  have hsmall : Nat.card R0=5 ∨ IsElementaryAbelian 3 R0 := by
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · let e := e.some
      right
      refine { toIsMulCommutative := ⟨⟨fun a b => e.injective (by
        rw [map_mul,map_mul]; exact mul_comm _ _)⟩⟩, exponent_dvd_p := ?_ }
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      apply e.injective
      rw [map_pow,map_one]
      exact (show ∀ z:C3×C3,z^3=1 from by decide) (e a)
    · exact Or.inl ((Nat.card_congr e.some.toEquiv).trans hfive)
  have hR0three : Nat.card R0≠3 := by
    intro hh
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · have hc := (Nat.card_congr e.some.toEquiv).trans hnine; omega
    · have hc := (Nat.card_congr e.some.toEquiv).trans hfive; omega
  have hRcard : Nat.card R=Nat.card R0 :=
    SectionThree.pSet_small_residual_image_card_eq Sedge hlocal.1 P hlocal.2.1 hlocal.2.2.2.1
      q (QuotientGroup.mk'_surjective _) f (by rw [QuotientGroup.ker_mk']; exact hcore) hnot hsmall
  have hodd : R=SectionOne.oddCore K := by
    have hh := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' middle (ctx.Γ.adjacent_symm hterminal) f chief.rangeRestrict_surjective hcore
    change (E.subgroupOf P).map f = SectionOne.oddCore K at hh
    rwa [hnative] at hh
  have hkernelOld : action.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
    exact hcore
  let beta : action.range →* K := action.rangeRestrict.liftOfSurjective
    action.rangeRestrict_surjective ⟨f,hkernelOld⟩
  have hbeta (a:P) : beta (action.rangeRestrict a)=f a :=
    action.rangeRestrict.liftOfRightInverse_comp_apply (Function.surjInv action.rangeRestrict_surjective)
      (Function.rightInverse_surjInv action.rangeRestrict_surjective) ⟨f,hkernelOld⟩ a
  have hbetaHom : beta.comp action.rangeRestrict=f := MonoidHom.ext hbeta
  have hmapE : ((E.subgroupOf P).map action.rangeRestrict).map beta=R := by
    rw [Subgroup.map_map,hbetaHom,hnative]
  have hsource := (ten_one_large_residual_generation ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno).2.1
  have hgen : R=⁅R,Subgroup.zpowers (f actor)⁆ := by
    have hh := congrArg (Subgroup.map beta) hsource
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers,hmapE,hbeta] at hh
    exact hh
  have hcanonical : SectionOne.involutionCommutator K (f actor)=R := by
    change ⁅SectionOne.oddCore K,Subgroup.zpowers (f actor)⁆=R
    rw [←hodd]
    exact hgen.symm
  obtain ⟨prime,hprime,_,hpgroup⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    Sedge hlocal.1 P hlocal.2.1 hlocal.2.2.2.1 f hcore
  have hinvolution := isInvolution_of_card_two_displacement (chief actor) hrank
  have hinv : _root_.IsInvolution (f actor) :=
    ⟨fun hh => hinvolution.1 (congrArg Subtype.val hh),Subtype.ext hinvolution.2⟩
  have hCcard : Nat.card (Subgroup.zpowers (f actor))=2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hinv.2 hinv.1]
  have hfaith : fixingSubgroup K (Set.univ : Set Wc)=⊥ := by
    apply bot_unique
    intro g hg
    apply Subtype.ext
    ext w
    exact ((mem_fixingSubgroup_iff K).mp hg) w (Set.mem_univ w)
  let _ : Group.IsSolvable P := hlocal.2.2.2.1
  have hHyp : SectionOne.Hypotheses K Wc := {
    G_solvable := Group.isSolvable_of_surjective chief.rangeRestrict_surjective
    G_even := even_iff_two_dvd.mpr (by rw [←hCcard]; exact (Subgroup.zpowers (f actor)).card_subgroup_dvd_card)
    action_faithful := hfaith
    twoCore_eq_bot := irreducible_range_two_core_eq_bot chief.range hirrR }
  have hrankR : Nat.card (commutatorAction (Subgroup.zpowers (f actor)) Wc)=2 := by
    rw [←commutatorAction_map_actor_subtype K (Subgroup.zpowers (f actor)),MonoidHom.map_zpowers]
    exact hrank
  let _ : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨e⟩ := SectionOne.involutionCommutator_isCyclicThree_of_displacement_card_two
    hHyp (f actor) hinv prime (hcanonical.symm ▸ hpgroup) hrankR
  have hcanonicalCard : Nat.card (SectionOne.involutionCommutator K (f actor))=3 :=
    (Nat.card_congr e.toEquiv).trans hthree
  rw [hcanonical,hRcard] at hcanonicalCard
  exact hR0three hcanonicalCard


public theorem ten_one_large_nontransvection_chief_factor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))

    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hcard : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆)
    (hno : ∀ element : G, element ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      element ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers element⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let E := EAt ctx.Γ ctx.criticalPath.a'
    let U := twoCoreIn E
    let V := VAt ctx.Γ ctx.criticalPath.a'
    ∃ hPU : P ≤ Subgroup.normalizer (U : Set G),
      ∃ D : Subgroup G, V ≤ D ∧ D < U ∧
        ∃ _hPD : P ≤ Subgroup.normalizer (D : Set G),
          ∃ hDnormal : (D.subgroupOf U).Normal,
            let _ := hDnormal
            ∃ chief : P →* MulAut (U ⧸ D.subgroupOf U),
              (∀ mover : P, ∀ point : U,
                chief mover (QuotientGroup.mk' (D.subgroupOf U) point) =
                  QuotientGroup.mk' (D.subgroupOf U)
                    ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                      (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) ∧
              IsElementaryAbelian 2 (U ⧸ D.subgroupOf U) ∧
              Nontrivial (U ⧸ D.subgroupOf U) ∧
              (∀ K : Subgroup (U ⧸ D.subgroupOf U),
                (∀ mover : P, ∀ point, point ∈ K → chief mover point ∈ K) →
                  K = ⊥ ∨ K = ⊤) ∧
              commutatorAction ((E.subgroupOf P).map chief) (U ⧸ D.subgroupOf U) = ⊤ ∧
              ¬ E.subgroupOf P ≤ chief.ker ∧
              Nat.card (commutatorAction (Subgroup.zpowers (chief actor)) (U ⧸ D.subgroupOf U)) ≠ 2 := by
  obtain ⟨hPU,D,hVD,hDU,hPD,hDnormal,chief,hformulaChief,hWc,hne,hirr,hfull,hres⟩ :=
    ten_one_large_noncentral_chief_factor ctx middle hpath hno
  let _ := hDnormal
  let _ := hWc
  let _ := hne
  exact ⟨hPU,D,hVD,hDU,hPD,hDnormal,chief,hformulaChief,hWc,hne,hirr,hfull,hres,
    ten_one_large_chief_displacement_ne_two ctx middle hpath actor hactor action hformula
      hkernel hout hcard hselected hno chief hirr hres⟩

end Stellmacher.SectionTen
