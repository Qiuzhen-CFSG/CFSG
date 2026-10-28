module
public import Stellmacher.SectionNine.DistanceOneProductCenter
public import Stellmacher.SectionNine.DistanceOneProductCore
public import Stellmacher.SectionNine.DistanceOneNormalizedSubgroup
public import Stellmacher.SectionNine.DistanceOneResidualProductAction
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.ResidualSecondCenterSeed
public import Stellmacher.TwoResidualFixedModulo
public import Theory.ElementaryAbelian.Join

/-!
# The admissible seed before the maximal subgroup construction

For the actual length-one extraction, the product of the two cross factors
lies in the terminal core and has the terminal center as its center, of order
two. Its quotient is elementary abelian. The extracted residual acts
nontrivially on that quotient; the commuting fixed-space theorem detects this
nontrivial action on the elements fixed by the terminal core modulo its center.

Inside the actual terminal stabilizer, take the commutator of the preimage of
the core quotient center with the full terminal two-residual. Residual
idempotence gives the full residual equation. The terminal residual fixes
the core center by (3.5) and (7.5), so the core commutator of this subgroup is
the central involution. The generic second-center seed theorem gives an
intersection with the extracted product of order at least eight. Normality
and the extracted factor swap exclude containment in the starting core.
Mapping this subgroup through the actual stabilizer inclusion preserves both
commutator equations and the cardinal bound.

The exact extraction, coatom intersection, source (3), the relative-index
bound in (4), and the final intersection in (8) are explicit inputs. No seed,
core equality, maximal subgroup, or relation (9) is assumed. Source:
Stellmacher, Journal of Algebra 190 (1997), (9.1), journal pp.46–47,
`refs/files/stellmacher-n-group.pdf`, paragraph immediately before (9).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open Stellmacher.SectionThree
open scoped Pointwise commutatorElement
universe u

private theorem elementary_of_le {G : Type*} [Group G] (C A : Subgroup G)
    [IsElementaryAbelian 2 A] (h : C ≤ A) : IsElementaryAbelian 2 C := by
  let _ : IsMulCommutative C := IsMulCommutative.of_setLike_mul_comm
    (fun x hx y hy => setLike_mul_comm (s := A) (h hx) (h hy))
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) (h x.property))

public theorem distance_one_admissible_seed_of_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneExtractionData ctx)
    (hcoatom : data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a))
    (hfour :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V)
    (hthree :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      ⁅(Subgroup.center V).map V.subtype, twoResidualIn data.E⁆ = ⊥)
    (hintersection : z ctx.Γ ctx.criticalPath.a ⊓
        stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a') :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    ∃ U : Subgroup G,
      U ≤ q ctx.Γ ctx.criticalPath.a' ∧
      ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' ∧
      ⁅U, e ctx.Γ ctx.criticalPath.a'⁆ = U ∧
      8 ≤ Nat.card (U ⊓ V : Subgroup G) ∧ ¬ U ≤ q ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let P := stabilizer Γ cp.a'
  let Q := q Γ cp.a'
  let Z := z Γ cp.a'
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  obtain ⟨hcenter,hZcard,_,_,_⟩ :=
    distance_one_extracted_product_center_card ctx hb hfaith data hcoatom hfour hthree
  have hI : z Γ cp.a ⊓ z Γ next = Z :=
    distance_one_center_intersection_eq_of_extraction ctx hb hfaith data hfour
  have hgeom := distance_one_product_factors Γ cp.a next
  have hCD : C ⊓ D = Z := hgeom.2.2.2.2.trans hI
  have hVQ : V ≤ Q := distance_one_product_le_next_core ctx hb data hintersection
  have hQP : Q ≤ P := by
    change q Γ cp.a' ≤ stabilizer Γ cp.a'
    rw [q, Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVP : V ≤ P := hVQ.trans hQP
  have hZV : Z ≤ V := hCD ▸ inf_le_left.trans le_sup_left
  have hZP : Z ≤ P := hZV.trans hVP
  have hQnorm : P ≤ Subgroup.normalizer Q := stabilizer_le_normalizer_q Γ cp.a'
  have hZnorm : P ≤ Subgroup.normalizer Z := stabilizer_le_normalizer_z Γ cp.a'
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (q Γ cp.a')
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hEV : data.E ≤ Subgroup.normalizer V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans
        (distance_one_extracted_action ctx hb data hcoatom))
  have hQV : Q ≤ Subgroup.normalizer V := by
    have hback : cp.a ∈ neighborhood Γ cp.a' := by
      rw [neighborhood, Γ.neighbors_def]
      exact cp.endpoint_distance.trans hb
    have hQa : Q ≤ stabilizer Γ cp.a :=
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core _ _ hback default).2.2
    have hQmap : Q.map (MulAut.conj data.x).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnorm data.x_mem)
    have hQc : Q ≤ stabilizer Γ next := by
      change Q ≤ stabilizer Γ (Γ.act data.x⁻¹ cp.a)
      rw [stabilizer_act, inv_inv, ← hQmap]
      exact Subgroup.map_mono hQa
    have hQC : Q ≤ Subgroup.normalizer C :=
      (le_inf (hQa.trans (stabilizer_le_normalizer_z Γ _))
        (hQc.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hQD : Q ≤ Subgroup.normalizer D :=
      (le_inf (hQc.trans (stabilizer_le_normalizer_z Γ _))
        (hQa.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hQC hQD).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C D)
  let Qp := Q.subgroupOf P
  let Zp := Z.subgroupOf P
  let Vp := V.subgroupOf P
  let Lp := data.E.subgroupOf P
  let Cp := C.subgroupOf P
  let Dp := D.subgroupOf P
  have hQmap : Qp.map P.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQP
  have hZmap : Zp.map P.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZP
  have hVmap : Vp.map P.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVP
  have hLmap : Lp.map P.subtype = data.E := Subgroup.map_subgroupOf_eq_of_le data.E_le
  have hRmap : (twoResidualAmbient Lp).map P.subtype = twoResidualIn data.E :=
    map_twoResidualAmbient_of_subgroup_image Lp P.subtype data.E hLmap
  have hEmap : (twoResidualAmbient (⊤ : Subgroup P)).map P.subtype = e Γ cp.a' := by
    rw [map_twoResidualAmbient_of_subgroup_image ⊤ P.subtype P
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])]
    change twoResidualAmbient P = Γ.twoResidualAt cp.a'
    rw [Γ.twoResidualAt_def]
    rfl
  let _ : Qp.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hQnorm
  let _ : Zp.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr hZnorm
  have hQpp : IsPGroup 2 Qp := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hZpcard : Nat.card Zp = 2 := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hZmap]
    exact hZcard
  have hZpV : Zp ≤ Vp := fun x hx => hZV hx
  have hLpV : Lp ≤ Subgroup.normalizer Vp := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVP]
    exact fun x hx => hEV hx
  have hQpV : Qp ≤ Subgroup.normalizer Vp := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVP]
    exact fun x hx => hQV hx
  have hQE : ⁅Qp,Lp⁆ ≤ Vp := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, hQmap, hLmap, hVmap]
    exact (Subgroup.commutator_mono le_sup_right le_rfl).trans
      (distance_one_extracted_action ctx hb data hcoatom)
  have hforward : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hforward
  let _ : IsElementaryAbelian 2 C := elementary_of_le C (z Γ cp.a) inf_le_left
  let _ : IsElementaryAbelian 2 (z Γ next) := by
    change IsElementaryAbelian 2 (z Γ (Γ.act data.x⁻¹ cp.a))
    rw [z_act, inv_inv]
    exact IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 D := elementary_of_le D (z Γ next) inf_le_left
  let _ : IsElementaryAbelian 2 Cp := IsElementaryAbelian.subgroupOf
    ((le_sup_left : C ≤ V).trans hVP)
  let _ : IsElementaryAbelian 2 Dp := IsElementaryAbelian.subgroupOf
    ((le_sup_right : D ≤ V).trans hVP)
  let π := QuotientGroup.mk' Zp
  have hCpDp : ⁅Cp,Dp⁆ ≤ Zp := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    have hCmap : Cp.map P.subtype = C := Subgroup.map_subgroupOf_eq_of_le
      ((le_sup_left : C ≤ V).trans hVP)
    have hDmap : Dp.map P.subtype = D := Subgroup.map_subgroupOf_eq_of_le
      ((le_sup_right : D ≤ V).trans hVP)
    rw [Subgroup.map_commutator, hCmap, hDmap, hZmap]
    exact (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hgeom.2.1)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hgeom.1)).trans hCD.le
  let _ : IsElementaryAbelian 2 (Vp.map π) := by
    have hm : ⁅Cp.map π,Dp.map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
      simpa only [π, QuotientGroup.ker_mk'] using hCpDp
    let _ : IsElementaryAbelian 2 (Cp.map π) := IsElementaryAbelian.map π
    let _ : IsElementaryAbelian 2 (Dp.map π) := IsElementaryAbelian.map π
    have hv : Vp = Cp ⊔ Dp := Subgroup.subgroupOf_sup
      ((le_sup_left : C ≤ V).trans hVP) ((le_sup_right : D ≤ V).trans hVP)
    rw [hv, Subgroup.map_sup, sup_comm]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hm)
  have hnon : ¬ ⁅Vp,twoResidualAmbient Lp⁆ ≤ Zp := by
    intro hc
    apply distance_one_extracted_residual_commutator_not_le_intersection ctx hb data hcoatom hfour
    rw [hI]
    have hm := Subgroup.map_mono (f := P.subtype) hc
    rwa [Subgroup.map_commutator, hVmap, hRmap, hZmap] at hm
  have hnonfixed : ¬ ⁅(Qp ⊓ (Subgroup.centralizer
      ((Qp.map π : Subgroup (P ⧸ Zp)) : Set (P ⧸ Zp))).comap π) ⊓ Vp,
      twoResidualAmbient Lp⁆ ≤ Zp := by
    intro h
    apply hnon
    apply twoResidual_commutator_le_of_commuting_fixed_modulo Lp Qp Vp Zp hQpp hLpV hQpV hQE
    have hsame : (Qp ⊓ (Subgroup.centralizer
        ((Qp.map π : Subgroup (P ⧸ Zp)) : Set (P ⧸ Zp))).comap π) ⊓ Vp =
      Vp ⊓ (Subgroup.centralizer
        ((Qp.map π : Subgroup (P ⧸ Zp)) : Set (P ⧸ Zp))).comap π := by
      ext x
      change (x ∈ Qp ∧ _) ∧ x ∈ Vp ↔ x ∈ Vp ∧ _
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩, fun hx => ⟨⟨hVQ hx.1,hx.2⟩,hx.1⟩⟩
    exact hsame ▸ h
  have hfix : ⁅centerIn Qp,twoResidualAmbient (⊤ : Subgroup P)⁆ = ⊥ := by
    have hglobal : ⁅centerIn Q,twoResidualIn P⁆ = ⊥ := by
      have hs := congrArg (fun b => ⁅(Subgroup.center (q Γ b)).map (q Γ b).subtype,
        twoResidualIn (stabilizer Γ b)⁆ = ⊥) hstep
      simpa only [centerIn_eq_map_center] using
        hs.mp (next_core_center_residual ctx.sectionSeven Γ cp ctx.commutator_eq)
    have hmcenter : (centerIn Qp).map P.subtype ≤ centerIn Q := by
      rintro x ⟨a,ha,rfl⟩
      refine ⟨ha.1, ?_⟩
      intro b hb
      exact congrArg Subtype.val (ha.2 (⟨b,hQP hb⟩ : P) hb)
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_bot, hEmap]
    have hle := (Subgroup.commutator_mono hmcenter le_rfl).trans hglobal.le
    have he : e Γ cp.a' = twoResidualIn P := by
      rw [CosetGraphContext.e, Γ.twoResidualAt_def]
      rfl
    rw [he]
    exact le_antisymm hle bot_le
  have hRE : twoResidualAmbient Lp ≤ twoResidualAmbient (⊤ : Subgroup P) := by
    exact twoResidualIn_mono Lp ⊤ le_top
  obtain ⟨Up,hUQ,hUcomm,hUE,hUnormal,hUcard,hUnot⟩ :=
    exists_residual_second_center_seed Qp Zp Vp Lp hQpp hZpcard hZpV hfix hRE
      ((twoResidualIn_le Lp).trans hLpV) hnonfixed
  let U := Up.map P.subtype
  have hUQP : U ≤ Q := by
    exact (Subgroup.map_mono hUQ).trans hQmap.le
  have hUQcomm : ⁅U,Q⁆ = Z := by
    rw [← hQmap, ← Subgroup.map_commutator, hUcomm, hZmap]
  have hUEcomm : ⁅U,e Γ cp.a'⁆ = U := by
    rw [← hEmap, ← Subgroup.map_commutator, hUE]
  have hUmap : (Up ⊓ Vp).map P.subtype = U ⊓ V := by
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hVmap]
  have hcard : 8 ≤ Nat.card (U ⊓ V : Subgroup G) := by
    rw [← hUmap, Subgroup.card_map_of_injective P.subtype_injective]
    exact hUcard
  have hnormU : P ≤ Subgroup.normalizer U := by
    let _ : Up.Normal := hUnormal
    have hn := Up.le_normalizer_map P.subtype
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hn
    exact hn
  refine ⟨U,hUQP,hUQcomm,hUEcomm,hcard,?_⟩
  apply distance_one_normalized_subgroup_not_le_core ctx hb data U hnormU
  change ¬ U ⊓ V ≤ z Γ cp.a ⊓ z Γ next
  intro h
  apply hUnot
  apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
  rw [hUmap,hZmap]
  exact h.trans hI.le

end Stellmacher.SectionNine
