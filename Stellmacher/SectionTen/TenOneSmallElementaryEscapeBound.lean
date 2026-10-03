module
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCard
public import Theory.GroupTheory.C4SquareUniqueElementarySixteen

/-!
# Elementary subgroups escaping the middle centralizer

In the order-eight first-module case with local quotient SL₂(2), let W₀ be
its defined middle neighborhood-core intersection and W*=C_Qmiddle(W₀).
Every elementary abelian subgroup of the actual middle core that is not
contained in W* has order at most eight. No order for W* is assumed, so
this applies to both small-case branches.

Inside the middle stabilizer M, the residual intersection R=O²(M)∩O₂(M)
is C₄×C₄ and is self-centralizing in O₂(M). Its residual conjugation image
has order three: the relative index makes its order divide three, and
triviality would contradict C_R(O²(M))=1 in the center-free stabilizer.
The core's conjugation action commutes with this cubic image because its
commutators with the residual lie in the abelian R.

The canonical equivalence from the intrinsic two-core onto Qmiddle transports
X and W*. Restricting R to that intrinsic core transports the cubic action
by `MulAut.congr`; its compatibility with literal conjugation is checked
pointwise. The proved residual product and intersection give the cover and
central-four intersection required by the generic elementary-subgroup bound.
Transporting cardinality back proves the assertion for the supplied X.

Source: Stellmacher (10.1)(a3), printed p.61, the uniqueness step before (7)
in `refs/files/stellmacher-n-group.pdf`. The stronger escaping-subgroup form
also supplies the subsequent quotient-action kernel argument.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- Elementary subgroups outside the actual middle centralizer have order at most eight. -/
public theorem ten_one_small_elementary_escape_card_bound
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (X : Subgroup (QAt ctx.Γ middle)) [IsElementaryAbelian 2 X]
    (hnot : ¬ X ≤ (QAt ctx.Γ middle ⊓ Subgroup.centralizer
      ((NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
        GeneratedNeighborhoodV ctx.Γ middle : Subgroup G) : Set G)).subgroupOf
          (QAt ctx.Γ middle)) : Nat.card X ≤ 8 := by
  classical
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let R := E ⊓ Q
  let D := twoCoreIn (EAt ctx.Γ middle)
  let Qm := QAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Qm ⊓ Subgroup.centralizer (W0 : Set G)
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter, hc4, himage⟩ :=
    ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  obtain ⟨equiv⟩ := hc4
  let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
  have hRcard : Nat.card R = 16 := by
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card]
  have hEmap : E.map M.subtype = EAt ctx.Γ middle := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) M.subtype M
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
    exact hm.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Q.map M.subtype = Qm := (ctx.Γ.twoCoreAt_def middle).symm
  have hRmap : R.map M.subtype = D := by
    rw [Subgroup.map_inf E Q M.subtype M.subtype_injective, hEmap, hQmap]
    change ctx.Γ.twoResidualAt middle ⊓ ctx.Γ.twoCoreAt middle =
      twoCoreIn (ctx.Γ.twoResidualAt middle)
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
  let eQ : Q ≃* Qm := (Q.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hQmap)
  let f : Q →* G := M.subtype.comp Q.subtype
  have hf : Function.Injective f := M.subtype_injective.comp Q.subtype_injective
  have heQ (q : Q) : ((eQ q : Qm) : G) = f q := by
    simp only [eQ, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply Q M.subtype M.subtype_injective q
  let C := (Wstar.subgroupOf Qm).map eQ.symm.toMonoidHom
  let Xn := X.map eQ.symm.toMonoidHom
  let RQ := R.subgroupOf Q
  let eR : RQ ≃* R := Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ Q)
  obtain ⟨_, hCelementary, _, hCR, _⟩ :=
    ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  let _ : IsElementaryAbelian 2 Wstar := hCelementary
  let _ : IsElementaryAbelian 2 (Wstar.subgroupOf Qm) :=
    IsElementaryAbelian.subgroupOf (inf_le_left : Wstar ≤ Qm)
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 Xn := IsElementaryAbelian.map _
  have hfcomp : f.comp eQ.symm.toMonoidHom = Qm.subtype := by
    ext q
    change f (eQ.symm q) = (q : G)
    rw [← heQ, eQ.apply_symm_apply]
  have hCmap : C.map f = Wstar := by
    rw [show C = (Wstar.subgroupOf Qm).map eQ.symm.toMonoidHom from rfl,
      Subgroup.map_map, hfcomp, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hRQmap : RQ.map f = D := by
    change (R.subgroupOf Q).map (M.subtype.comp Q.subtype) = D
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right, hRmap]
  have hftop : (⊤ : Subgroup Q).map f = Qm := by
    change (⊤ : Subgroup Q).map (M.subtype.comp Q.subtype) = Qm
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQmap]
  have hZcard : Nat.card (RQ ⊓ C : Subgroup Q) = 4 := by
    rw [← Subgroup.card_map_of_injective hf,
      Subgroup.map_inf RQ C f hf, hRQmap, hCmap, inf_comm, hCR]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  have hcover : RQ ⊔ C = ⊤ := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_sup, hRQmap, hCmap, hftop]
    exact (ten_one_small_middle_core_residual_centralizer_product
      ctx middle hpath hsmall hmodel).symm
  have hselfM : Q ⊓ Subgroup.centralizer (R : Set M) = R :=
    inf_centralizer_inf_eq_of_centerfree_odd_image (default : Sylow 2 M) E Q
      (twoResidualAmbient_top_sup_sylow _) (pCore_isPGroup (p := 2) (G := M))
      hcenter (by rw [himage]; decide)
  have hself : Subgroup.centralizer (RQ : Set Q) = RQ := by
    apply le_antisymm
    · intro q hq
      have hqc : (q : M) ∈ Subgroup.centralizer (R : Set M) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hq
          ⟨r, (inf_le_right : R ≤ Q) hr⟩ hr)
      change (q : M) ∈ R
      exact hselfM ▸ (show (q : M) ∈ Q ⊓ Subgroup.centralizer (R : Set M) from
        ⟨q.property, hqc⟩)
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact Subtype.ext (setLike_mul_comm (s := R) hr hq)
  let action : M →* MulAut R := MulAut.conjNormal
  have hRker : R ≤ action.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change r * (s : M) * r⁻¹ = (s : M)
    rw [setLike_mul_comm (s := R) hr s.property, mul_inv_cancel_right]
  have hRcentralE : R ⊓ Subgroup.centralizer (E : Set M) = ⊥ :=
    Subgroup.inf_centralizer_eq_bot_of_centerfree_sylow_supplement
      (default : Sylow 2 M) E R (twoResidualAmbient_top_sup_sylow _)
      ((pCore_isPGroup (p := 2) (G := M)).to_le inf_le_right) hcenter
  have himageNe : E.map action ≠ ⊥ := by
    intro hbot
    have hEk : E ≤ action.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hRC : R ≤ Subgroup.centralizer (E : Set M) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hfix := congrArg (fun a : MulAut R => (a ⟨r, hr⟩ : M))
        (MonoidHom.mem_ker.mp (hEk he))
      change e * r * e⁻¹ = r at hfix
      exact mul_inv_eq_iff_eq_mul.mp hfix
    have hzero : R = ⊥ := by
      simpa only [inf_eq_left.mpr hRC] using hRcentralE
    rw [hzero, Subgroup.card_bot] at hRcard
    omega
  have hindex : R.relIndex E = 3 := by
    dsimp only [R]
    rw [Subgroup.inf_relIndex_left, ← QuotientGroup.ker_mk' Q, Subgroup.relIndex_ker]
    exact himage
  have himageDvd : Nat.card (E.map action) ∣ 3 := by
    rw [← Subgroup.relIndex_ker, ← hindex]
    exact Subgroup.relIndex_dvd_of_le_left E hRker
  have himageThree : Nat.card (E.map action) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp himageDvd with hone | hthree
    · exact False.elim (himageNe (Subgroup.card_eq_one.mp hone))
    · exact hthree
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := E.map action) 3
    (by rw [himageThree])
  have ha3 : (a : MulAut R) ^ 3 = 1 :=
    congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  have hane : (a : MulAut R) ≠ 1 := by
    intro heq
    have haa : a = 1 := Subtype.ext heq
    rw [haa, orderOf_one] at ha
    omega
  have hcentral : Q.map action ≤ Subgroup.centralizer (E.map action : Set (MulAut R)) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (Subgroup.commutator_le_inf Q E).trans ((inf_comm Q E).le.trans hRker)
  have hact (q : Q) : Commute (action (q : M)) (a : MulAut R) := by
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentral (Subgroup.mem_map_of_mem action q.property)) a a.property).symm
  let cubic : MulAut RQ := MulAut.congr eR.symm a
  have hcubic3 : cubic ^ 3 = 1 := by
    change (MulAut.congr eR.symm (a : MulAut R)) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hcubicNe : cubic ≠ 1 := by
    intro hone
    apply hane
    apply (MulAut.congr eR.symm).injective
    simpa only [map_one] using hone
  have hconj (q : Q) : MulAut.congr eR.symm (action (q : M)) =
      (MulAut.conjNormal q : MulAut RQ) := by
    ext r
    rfl
  have hactRQ (q : Q) : Commute (MulAut.conjNormal q : MulAut RQ) cubic := by
    have hh := (hact q).map (MulAut.congr eR.symm).toMonoidHom
    rw [show (MulAut.congr eR.symm).toMonoidHom (action (q : M)) =
      (MulAut.conjNormal q : MulAut RQ) from hconj q] at hh
    exact hh
  have hnotn : ¬ Xn ≤ C := by
    intro hle
    exact hnot ((Subgroup.map_le_map_iff_of_injective eQ.symm.injective).mp hle)
  have hbound := Subgroup.card_le_eight_of_elementary_not_le_of_c4_square_cubic_action
    RQ C ⟨eR.trans equiv⟩ hZcard hcover hself cubic hcubic3 hcubicNe hactRQ Xn hnotn
  rwa [Subgroup.card_map_of_injective eQ.symm.injective] at hbound

end Stellmacher.SectionTen
