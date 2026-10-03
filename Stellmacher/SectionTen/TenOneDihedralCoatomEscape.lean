module
public import Stellmacher.SectionTen.TenOneDihedralConfiguration
public import Theory.GroupAction.InvertedOddFixedSubgroup
public import Theory.GroupAction.NormalizingActor

/-!
# Middle-core conjugates escape the prescribed dihedral coatom

In the actual Section Ten context, retain the prescribed dihedral extraction
of a first-neighbour actor whose terminal commutator contains the first
centre. Every `Qmiddle` conjugate of that actor lies outside the extracted
coatom. The displacement argument descends the literal `Vend/Zend` action to
the `pCore` quotient. The original actor fixes the commutator subgroup by
quadraticity, while the generic odd-inversion transfer makes the extracted
rotation fix it as well; lifting gives the required double commutator bound.
Conjugation by `Qmiddle` preserves both endpoint modules and the first centre.
If a conjugate remained in the coatom, the extracted residual would normalize
`Zmiddle`; the edge-generation equality would then contradict the source
non-normalization of the neighbouring centre. The selected containment is the
output of the source (10.1) actor selector, and is not a conclusion supplied
to the escape theorem.

Source: Stellmacher (10.1), printed p. 63, the paragraph preceding (13).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped Pointwise commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem coatom_displacement
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle actor hactor)
    (other : G) (hother : other ∈ data.raw.A₀) :
    ⁅⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers other⁆, data.raw.F₀⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.firstStep
  let E := data.raw.F₀
  let D := ⁅V, Subgroup.zpowers other⁆
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN, hW, action, haction, hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb ctx.criticalPath.a' ⟨mover, hmover⟩
  let _ := hN
  let W := V ⧸ Z.subgroupOf V
  let projection : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let barP := P ⧸ pCore 2 P
  let q : P →* barP := QuotientGroup.mk' (pCore 2 P)
  let barAction : barP →* MulAut W := QuotientGroup.lift (pCore 2 P) action hkernel.ge
  let _ : MulDistribMulAction barP W := MulDistribMulAction.compHom W barAction
  let rotation := (E.subgroupOf P).map q
  let t := q ⟨actor, data.module_le hactor⟩
  have hotherU : other ∈ U := data.raw.A₀_le hother
  have hotherP : other ∈ P := data.module_le hotherU
  let otherP : P := ⟨other, hotherP⟩
  let j := action otherP
  let J := Subgroup.zpowers j
  let N := commutatorAction J W
  let Uimage := (U.subgroupOf P).map action
  have hj : J ≤ Uimage := Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem action hotherU)
  have hquadratic : commutatorAction₂ Uimage W = ⊥ := by
    apply Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
      P V Z U (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a') data.module_le hN ?_
      action haction
    exact (((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).2.1).le.trans bot_le
  have hNimage : N ≤ commutatorAction Uimage W := by
    change commutatorAction J W ≤ commutatorAction Uimage W
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro point ⟨element, vector, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨element, hj element.property⟩, vector, rfl⟩
  have htfixed : ∀ point ∈ N, t • point = point := by
    intro point hpoint
    have hh := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquadratic
      (hNimage hpoint)
    exact hh ⟨action ⟨actor, data.module_le hactor⟩, Subgroup.mem_map_of_mem action hactor⟩
  let Rimage := rotation.map barAction
  have hcentral : Rimage ≤ Subgroup.centralizer (J : Set (MulAut W)) := by
    rintro element ⟨rotationP, hrotation, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro power hpower
    have hcomm : Commute (barAction rotationP) j := by
      have hh := data.raw.A₀_centralizes_rotation other hother rotationP hrotation
      have hm := congrArg barAction hh
      change barAction (q otherP * rotationP) = barAction (rotationP * q otherP) at hm
      rw [map_mul, map_mul] at hm
      have hcomp : barAction (q otherP) = j := rfl
      rw [hcomp] at hm
      change barAction rotationP * j = j * barAction rotationP
      exact hm.symm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpower
    exact (hcomm.zpow_right n).eq.symm
  have hstable := commutatorAction_isInvariant_of_normalizing_actor (V := W) Rimage J
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))
  have hRfixed : ∀ element ∈ rotation, ∀ point ∈ N, element • point = point := by
    apply inverted_odd_fixes_invariant_subgroup rotation ?_ t data.raw.reflected N ?_ htfixed
    · change Odd (Nat.card ((E.subgroupOf P).map q))
      rw [data.raw.rotation_card]
      exact data.raw.odd_p.pow
    · intro element helement point hpoint
      exact (hstable.invariant
        ⟨barAction element, Subgroup.mem_map_of_mem barAction helement⟩ point).mp hpoint
  have hnormal : Subgroup.zpowers other ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hotherP).trans (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
  have hDV : D ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hactorImage : ((Subgroup.zpowers other).subgroupOf P).map action = J := by
    have hsub : (Subgroup.zpowers other).subgroupOf P = Subgroup.zpowers otherP := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hotherP),
        MonoidHom.map_zpowers]
      rfl
    rw [hsub, MonoidHom.map_zpowers]
  have hNimageEq : N = (D.subgroupOf V).map projection := by
    rw [show N = commutatorAction J W from rfl, ← hactorImage]
    exact Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z
      (Subgroup.zpowers other) (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
        (Subgroup.zpowers_le.mpr hotherP) hN action haction
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro element helement point hpoint
  let eP : P := ⟨element, data.raw.F₀_le_P helement⟩
  let pointV : V := ⟨point, hDV hpoint⟩
  have hfix := hRfixed (q eP) (Subgroup.mem_map_of_mem q helement) (projection pointV)
    (hNimageEq.symm ▸ Subgroup.mem_map_of_mem projection hpoint)
  change action eP (projection pointV) = projection pointV at hfix
  rw [haction] at hfix
  have hh := QuotientGroup.eq_iff_div_mem.mp hfix
  change element * point * element⁻¹ / point ∈ Z at hh
  change ⁅element, point⁆ ∈ Z
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh

public theorem ten_one_dihedral_coatom_escape
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle actor hactor)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆)
    (mover : G) (hmover : mover ∈ QAt ctx.Γ middle) :
    mover * actor * mover⁻¹ ∉ data.raw.A₀ := by
  intro hcoatom
  let E := data.raw.F₀
  let Zfirst := ZAt ctx.Γ ctx.criticalPath.firstStep
  let Zend := ZAt ctx.Γ ctx.criticalPath.a'
  let Zmiddle := ZAt ctx.Γ middle
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hmfirst : mover ∈ GAt ctx.Γ ctx.criticalPath.firstStep :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
      ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2 hmover
  have hmterminal : mover ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
      ctx.criticalPath.a' ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2 hmover
  have hZmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.firstStep hmfirst)
  change (ZAt ctx.Γ ctx.criticalPath.firstStep).map (MulAut.conj mover).toMonoidHom =
    ZAt ctx.Γ ctx.criticalPath.firstStep at hZmap
  have hVmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' hmterminal)
  change (VAt ctx.Γ ctx.criticalPath.a').map (MulAut.conj mover).toMonoidHom =
    VAt ctx.Γ ctx.criticalPath.a' at hVmap
  have hselected' := Subgroup.map_mono (f := (MulAut.conj mover).toMonoidHom) hselected
  rw [hZmap, Subgroup.map_commutator, hVmap, MonoidHom.map_zpowers] at hselected'
  have hcomm : ⁅Zfirst, E⁆ ≤ Zend :=
    (Subgroup.commutator_mono hselected' le_rfl).trans
      (coatom_displacement ctx middle actor hactor data _ hcoatom)
  have hrev : ⁅E, Zfirst⁆ ≤ Zend := by rwa [Subgroup.commutator_comm]
  have hjoin : Zmiddle = Zfirst ⊔ Zend :=
    (sectionTenOpeningData ctx middle hpath).center_direct_product.1
  have hfirstZ : Zfirst ≤ Zmiddle := by rw [hjoin]; exact le_sup_left
  have hendZ : Zend ≤ Zmiddle := by rw [hjoin]; exact le_sup_right
  have hEN : E ≤ Subgroup.normalizer (Zmiddle : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro element point hpoint
    let c := (MulAut.conj (element : G)).toMonoidHom
    have hmapFirst : Zfirst.map c ≤ Zmiddle := by
      rintro value ⟨first, hfirst, rfl⟩
      have hc := hrev (Subgroup.commutator_mem_commutator element.property hfirst)
      have hh := Zmiddle.mul_mem (hendZ hc) (hfirstZ hfirst)
      change ((element : G) * first * (element : G)⁻¹ * first⁻¹) * first ∈ Zmiddle at hh
      change (element : G) * first * (element : G)⁻¹ ∈ Zmiddle
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    have hmapEnd : Zend.map c ≤ Zmiddle := by
      have hnormal := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a'
          (data.raw.F₀_le_P element.property))
      change Zend.map c = Zend at hnormal
      exact hnormal.le.trans hendZ
    have hmap : Zmiddle.map c ≤ Zmiddle := by
      rw [hjoin, Subgroup.map_sup]
      exact sup_le (hmapFirst.trans_eq hjoin) (hmapEnd.trans_eq hjoin)
    exact hmap (Subgroup.mem_map_of_mem c hpoint)
  apply neighbor_center_not_normalized ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal))
  change GAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (Zmiddle : Set G)
  calc
    GAt ctx.Γ ctx.criticalPath.a' = E ⊔
        (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a') := data.edge_generated.symm
    _ ≤ Subgroup.normalizer (Zmiddle : Set G) := sup_le hEN
      (inf_le_left.trans (stabilizer_le_normalizer_z ctx.Γ middle))

end Stellmacher.SectionTen
