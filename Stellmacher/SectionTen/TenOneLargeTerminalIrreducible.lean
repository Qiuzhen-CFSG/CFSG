module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure
public import Stellmacher.SectionThree.SmallResidualImageCard
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupAction.Invariant
public import Theory.GroupAction.CoprimeHall
public import Mathlib.Data.Finite.Perm

/-!
# Irreducibility of the large terminal quotient

In the actual Section Ten no-transvection case, every invariant subgroup of
V_terminal/Z_terminal is trivial or the whole quotient. The theorem keeps
the supplied normality instance, elementary quotient instance, conjugation
action, formula and exact two-core kernel. Neither irreducibility nor a
maximal Sylow subgroup is assumed.

Source (14) gives quotient order sixteen and residual image C₅ or C₃×C₃.
Full residual support and coprime decomposition make the odd core's fixed
subgroup trivial. Consequently the residual acts nontrivially on each
nonzero invariant subgroup. The small residual-image theorem preserves its
order five or nine in the restricted action. Orders two and four are excluded
by permutation-group divisibility, and order eight by |Aut(C₂³)|=168.
Lagrange's theorem leaves only the whole sixteen-element quotient.

This supplies the irreducibility used in the commutator-family argument
between (14) and (16) of Stellmacher (10.1), printed pp.63–64 of
`refs/files/stellmacher-n-group.pdf`. Both residual alternatives are retained.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

public theorem ten_one_large_terminal_irreducible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
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
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) :
    ∀ D : Subgroup (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')),
      (∀ mover : GAt ctx.Γ ctx.criticalPath.a', ∀ point,
        point ∈ D → action mover point ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let E := EAt Γ cp.a'
  let W := V ⧸ Z.subgroupOf V
  let O := SectionOne.oddCore action.range
  let q := QuotientGroup.mk' (pCore 2 P)
  let R0 := (twoResidualSubgroup P).map q
  have hnative : E.subgroupOf P = twoResidualSubgroup P := by
    dsimp only [E,P]
    rw [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  obtain ⟨hmodels,hVcard,_⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  have hmodels : Nonempty (R0 ≃* (C3 × C3)) ∨ Nonempty (R0 ≃* C5) := by
    change Nonempty (((E.subgroupOf P).map q) ≃* (C3 × C3)) ∨
      Nonempty (((E.subgroupOf P).map q) ≃* C5) at hmodels
    rwa [hnative] at hmodels
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hcenter := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  have hZcard : Nat.card Z = 2 := hcenter.1
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hZV : Z ≤ V := hcenter.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.a')))
  have hWcard : Nat.card W = 16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  have hcop : Nat.Coprime (Nat.card O) (Nat.card W) := by
    rw [hWcard]
    exact (pPrimeCore_coprime_card (p := 2) (G := action.range)).symm.pow_right 4
  have hfixed : FixedPoints.subgroup O W = ⊥ := by
    have hh := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := O) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance).disjoint
    have hfull := ten_one_large_terminal_oddCore_full_support ctx middle hpath hno action hformula hkernel
    change Disjoint (FixedPoints.subgroup O W) (commutatorAction O W) at hh
    rw [hfull,disjoint_top] at hh
    exact hh
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hcore : pCore 2 P ≤ action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  have hodd : (twoResidualSubgroup P).map action.rangeRestrict = O := by
    have hh := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      cp.a' middle (Γ.adjacent_symm hterminal) action.rangeRestrict
      action.rangeRestrict_surjective hcore
    change (E.subgroupOf P).map action.rangeRestrict = O at hh
    rwa [hnative] at hh
  let edge := P ⊓ GAt Γ middle
  let sylow : Sylow 2 edge := default
  let Sedge := sylowTwoAmbient edge sylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) sylow
  have hthree : Nat.card C3 = 3 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num)
  have hfive : Nat.card C5 = 5 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5)).trans (by norm_num)
  have hnine : Nat.card (C3 × C3) = 9 := by rw [Nat.card_prod,hthree]
  have hsmall : Nat.card R0 = 5 ∨ IsElementaryAbelian 3 R0 := by
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · let e := e.some
      right
      refine { toIsMulCommutative := ⟨⟨fun a b => e.injective (by
        rw [map_mul,map_mul]; exact mul_comm _ _)⟩⟩, exponent_dvd_p := ?_ }
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      apply e.injective
      rw [map_pow,map_one]
      exact (show ∀ z : C3 × C3, z ^ 3 = 1 from by decide) (e a)
    · exact Or.inl ((Nat.card_congr e.some.toEquiv).trans hfive)
  have hR0card : Nat.card R0 = 9 ∨ Nat.card R0 = 5 := by
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · exact Or.inl ((Nat.card_congr e.some.toEquiv).trans hnine)
    · exact Or.inr ((Nat.card_congr e.some.toEquiv).trans hfive)
  let _ : MulDistribMulAction P W := MulDistribMulAction.compHom W action
  intro D hD
  by_cases hDbot : D = ⊥
  · exact Or.inl hDbot
  right
  let _ : IsInvariant P W D := ⟨by
    intro mover point
    constructor
    · exact hD mover point
    · intro hp
      have hh := hD mover⁻¹ (action mover point) hp
      change mover⁻¹ • (mover • point) ∈ D at hh
      simpa only [inv_smul_smul] using hh⟩
  let restricted := MulDistribMulAction.toMulAut P D
  let R := (twoResidualSubgroup P).map restricted
  have hker : q.ker ≤ restricted.ker := by
    rw [QuotientGroup.ker_mk',←hkernel]
    intro mover hmover
    apply MonoidHom.mem_ker.mpr
    ext point
    have hh := MulEquiv.congr_fun (MonoidHom.mem_ker.mp hmover) (point : W)
    exact hh
  have hres : ¬ twoResidualSubgroup P ≤ restricted.ker := by
    intro htriv
    apply hDbot
    apply bot_unique
    intro point hp
    apply hfixed.le
    intro mover
    have hm : (mover : action.range) ∈ (twoResidualSubgroup P).map action.rangeRestrict :=
      hodd.symm ▸ mover.property
    obtain ⟨actor,hactor,himage⟩ := hm
    have heq := MulEquiv.congr_fun (MonoidHom.mem_ker.mp (htriv hactor)) (⟨point,hp⟩ : D)
    have hval := congrArg Subtype.val heq
    change action actor point = point at hval
    change (mover : action.range) • point = point
    rw [←himage]
    exact hval
  have hRcard : Nat.card R = Nat.card R0 :=
    SectionThree.pSet_small_residual_image_card_eq Sedge hlocal.1 P hlocal.2.1 hlocal.2.2.2.1
      q (QuotientGroup.mk'_surjective _) restricted hker hres hsmall
  have hdivAut : Nat.card R0 ∣ Nat.card (MulAut D) := by
    rw [←hRcard]
    exact R.card_subgroup_dvd_card
  let perm := MulAction.toPermHom R D
  have hinj : Function.Injective perm := by
    intro a b hab
    apply Subtype.ext
    ext point
    exact congrArg Subtype.val (Equiv.congr_fun hab point)
  have hdivPerm : Nat.card R0 ∣ (Nat.card D).factorial := by
    rw [←hRcard,←Nat.card_perm]
    exact Subgroup.card_dvd_of_injective perm hinj
  have hcardD : Nat.card D ∣ 2 ^ 4 := by
    have hh : Nat.card D ∣ Nat.card W := D.card_subgroup_dvd_card
    rwa [hWcard] at hh
  obtain ⟨n,hn,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcardD
  interval_cases n
  · exact (hDbot (Subgroup.card_eq_one.mp (by simpa using heq))).elim
  · rcases hR0card with hc | hc <;> norm_num [hc,heq,Nat.factorial] at hdivPerm
  · rcases hR0card with hc | hc <;> norm_num [hc,heq,Nat.factorial] at hdivPerm
  · let _ : IsElementaryAbelian 2 D := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) (point : W)) }
    rw [card_mulAut_of_elementary_eight D (by simpa using heq)] at hdivAut
    rcases hR0card with hc | hc <;> norm_num [hc] at hdivAut
  · apply Subgroup.eq_of_le_of_card_ge (le_top : D ≤ ⊤)
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    change Nat.card W ≤ Nat.card D
    rw [hWcard,heq]
    norm_num

end Stellmacher.SectionTen
