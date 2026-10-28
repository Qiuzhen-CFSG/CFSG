module
public import Stellmacher.SectionTen.TenOneGeneratedQuotient
public import Stellmacher.SectionTen.TenOneGeneratedElementary
public import Stellmacher.SectionTen.TenOneLargeDerived
public import Stellmacher.SectionTen.TenOneSmallNeighborCore
public import Theory.GroupTheory.ThreeLineQuotientCommutator

/-!
# The large-branch neighborhood quotient has order eight

In the actual Section Ten geometry, use source (15)'s index two of
Vfirst∩O₂(Eend) in Vfirst, the source-(14) common-intersection order eight,
and the source-(12) absence of quotient transvections. Then the literal
conjugate closure W has index eight in the generated neighborhood Wnext.
These are source case inputs; no desired neighborhood index or generation
conclusion is assumed.

The residual-core intersection lies in the defining seed, so its index and
critical noncontainment force seed index two. Ordered-pair transport and
W's containment in all neighboring cores give three distinct order-two
images of the elementary neighbor modules in the proved elementary quotient
Wnext/W. Their join bounds its order by eight, while distinctness excludes
orders one and two. If the order were four, its three lines cover. The
finite-group square argument applied to the actual quotient map, using W
elementary and [W,Wnext]≤Zmiddle, puts Wnext' in Zmiddle. This contradicts
the proved large derived intersection of order eight and |Zmiddle|=4.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed pp.63–65,
source (12), (14), (15), and the quotient calculation after (19),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_neighbor_seed_le_generated
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) :
    VAt ctx.Γ left ⊓ QAt ctx.Γ right ≤ conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle) := by
  obtain ⟨actor, hactor, hfirst, hterminal⟩ :=
    ten_one_neighbor_pair_alignment ctx middle hpath hleft hright hne
  rw [← hfirst, ← hterminal, VAt, QAt, v_act, q_act,
    ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective]
  rintro element ⟨point, hpoint, rfl⟩
  exact Subgroup.subset_closure
    ⟨⟨actor⁻¹, (GAt ctx.Γ middle).inv_mem hactor⟩, ⟨point, hpoint⟩, rfl⟩

private theorem neighbor_generated_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hresidual : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) :
    (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle)).relIndex (VAt ctx.Γ left) = 2 := by
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  have hRindex : R.relIndex V = 2 := by
    have hh := ((V ⊓ R).subgroupOf V).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show V ⊓ R ≤ V from inf_le_left)).toEquiv] at hh
    change (V ⊓ R).relIndex V * Nat.card (V ⊓ R : Subgroup G) = Nat.card V at hh
    rw [Subgroup.inf_relIndex_left] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.trans hresidual)
  have hRQ : R ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hdiv : (QAt ctx.Γ ctx.criticalPath.a').relIndex V ∣ 2 := by
    rw [← hRindex]
    exact Subgroup.relIndex_dvd_of_le_left V hRQ
  have hseedIndex : (QAt ctx.Γ ctx.criticalPath.a').relIndex V = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact False.elim ((sectionTenOpeningData ctx middle hpath).first_noncontainment
        (Subgroup.relIndex_eq_one.mp hone))
    · exact htwo
  have hpairIndex : (QAt ctx.Γ right).relIndex (VAt ctx.Γ left) = 2 := by
    obtain ⟨actor, _, hfirst, hterminal⟩ :=
      ten_one_neighbor_pair_alignment ctx middle hpath hleft hright hne
    rw [← hfirst, ← hterminal, VAt, QAt, v_act, q_act,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj actor⁻¹).injective]
    exact hseedIndex
  have hWQ : W ≤ QAt ctx.Γ right :=
    (ten_one_generated_containment ctx middle hpath).trans
      (inf_le_left.trans (sInf_le
        ⟨right, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hright, rfl⟩))
  have hslice : W ⊓ VAt ctx.Γ left = QAt ctx.Γ right ⊓ VAt ctx.Γ left := by
    apply le_antisymm (inf_le_inf_right _ hWQ)
    intro element helement
    exact ⟨ten_one_neighbor_seed_le_generated ctx middle hpath hleft hright hne
      ⟨helement.2, helement.1⟩, helement.2⟩
  change W.relIndex (VAt ctx.Γ left) = 2
  rw [← Subgroup.inf_relIndex_right W (VAt ctx.Γ left), hslice,
    Subgroup.inf_relIndex_right]
  exact hpairIndex

public theorem ten_one_large_neighborhood_quotient
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hresidual : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) 2)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientCardEq (GeneratedNeighborhoodV ctx.Γ middle)
      (conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle)) 8 := by
  classical
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let W := conjugateClosure
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  have hWU : W ≤ U := (ten_one_generated_containment ctx middle hpath).trans inf_le_right
  obtain ⟨hN, hQelem⟩ := ten_one_generated_quotient_elementary ctx middle hpath
  let _ := hN
  let Q := U ⧸ W.subgroupOf U
  let _ : IsElementaryAbelian 2 Q := hQelem
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  let projection : U →* Q := QuotientGroup.mk' (W.subgroupOf U)
  have hsurjective : Function.Surjective projection := QuotientGroup.mk'_surjective _
  have hkernel : projection.ker = W.subgroupOf U := QuotientGroup.ker_mk' _
  let _ : Finite ctx.Γ.Vertex := ctx.Γ.finiteVertex
  let _ : Fintype {neighbor // ctx.Γ.adjacent middle neighbor} := Fintype.ofFinite _
  have hdegree : Fintype.card {neighbor // ctx.Γ.adjacent middle neighbor} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      (sectionTenOpeningData ctx middle hpath).quotient_model).degree
  let e : Fin 3 ≃ {neighbor // ctx.Γ.adjacent middle neighbor} :=
    (Fintype.equivFinOfCardEq hdegree).symm
  let vertex (i : Fin 3) := (e i).val
  let V (i : Fin 3) : Subgroup G := VAt ctx.Γ (vertex i)
  let A (i : Fin 3) : Subgroup U := (V i).subgroupOf U
  let L (i : Fin 3) : Subgroup Q := (A i).map projection
  have hadj (i : Fin 3) : ctx.Γ.adjacent middle (vertex i) := (e i).property
  have hdistinctVertex : Function.Injective vertex := fun i j h =>
    e.injective (Subtype.ext h)
  have hVU (i : Fin 3) : V i ≤ U :=
    le_sSup ⟨vertex i, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj i), rfl⟩
  have hAcard (i : Fin 3) : Nat.card (L i) = 2 := by
    rw [show Nat.card (L i) = Nat.card ((A i).map projection) from rfl,
      ← Subgroup.relIndex_ker, hkernel, Subgroup.relIndex_subgroupOf (hVU i)]
    apply neighbor_generated_index ctx middle hpath hresidual (hadj i)
      (hadj (if i = 0 then 1 else 0))
    intro heq
    have hh := hdistinctVertex heq
    split_ifs at hh <;> omega
  have hWQ (i : Fin 3) : W ≤ QAt ctx.Γ (vertex i) :=
    (ten_one_generated_containment ctx middle hpath).trans
      (inf_le_left.trans (sInf_le
        ⟨vertex i, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj i), rfl⟩))
  have hLdistinct : Function.Injective L := by
    intro i j heq
    by_contra hne
    apply ten_one_neighbor_module_not_le_core ctx middle hpath (hadj i) (hadj j)
      (fun h => hne (hdistinctVertex h))
    intro x hx
    have hxL : projection ⟨x, hVU i hx⟩ ∈ L j :=
      heq ▸ Subgroup.mem_map_of_mem projection (show (⟨x, hVU i hx⟩ : U) ∈ A i from hx)
    obtain ⟨y, hy, hyeq⟩ := hxL
    have hk : (⟨x, hVU i hx⟩ : U) / y ∈ W.subgroupOf U :=
      QuotientGroup.eq_iff_div_mem.mp hyeq.symm
    have hyQ : (y : G) ∈ QAt ctx.Γ (vertex j) :=
      (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
        (by rw [ctx.critical_length]; decide) _) hy
    have hprod := (QAt ctx.Γ (vertex j)).mul_mem (hWQ j hk) hyQ
    change (x / (y : G)) * (y : G) ∈ QAt ctx.Γ (vertex j) at hprod
    simpa only [div_mul_cancel] using hprod
  have hU : U = V 0 ⊔ V 1 ⊔ V 2 := by
    apply le_antisymm
    · apply sSup_le
      rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      obtain ⟨i, hi⟩ := e.surjective
        (⟨neighbor, (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor⟩ :
          {n // ctx.Γ.adjacent middle n})
      have heq : neighbor = vertex i := congrArg Subtype.val hi.symm
      rw [heq]
      fin_cases i
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (hVU 0) (hVU 1)) (hVU 2)
  have hAgeneration : A 0 ⊔ A 1 ⊔ A 2 = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le (hVU 0),
      Subgroup.map_subgroupOf_eq_of_le (hVU 1),
      Subgroup.map_subgroupOf_eq_of_le (hVU 2),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hU.symm
  have hLgen : L 0 ⊔ L 1 ⊔ L 2 = ⊤ := by
    dsimp only [L]
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, hAgeneration,
      Subgroup.map_top_of_surjective projection hsurjective]
  have hnormalizes (left right : Subgroup Q) :
      right ≤ Subgroup.normalizer (left : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hpairCount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (L 0) (L 1) (hnormalizes _ _)
  have hwholeCount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (L 0 ⊔ L 1) (L 2) (hnormalizes _ _)
  rw [hAcard 0, hAcard 1] at hpairCount
  rw [hAcard 2, hLgen, Nat.card_congr Subgroup.topEquiv.toEquiv] at hwholeCount
  have hposPair : 0 < Nat.card (L 0 ⊓ L 1 : Subgroup Q) := Nat.card_pos
  have hposWhole : 0 < Nat.card ((L 0 ⊔ L 1) ⊓ L 2 : Subgroup Q) := Nat.card_pos
  have hpairBound : Nat.card (L 0 ⊔ L 1 : Subgroup Q) ≤ 4 := by nlinarith
  have hupper : Nat.card Q ≤ 8 := by nlinarith
  have hlower : 2 < Nat.card Q := by
    by_contra hh
    have heq (i : Fin 3) : L i = ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_top (by
        rw [hAcard i, Nat.card_congr Subgroup.topEquiv.toEquiv]
        omega)
    have hh := hLdistinct ((heq 0).trans (heq 1).symm)
    omega
  have hfourImpossible : Nat.card Q ≠ 4 := by
    intro hfour
    let _ : IsElementaryAbelian 2 W := ten_one_generated_elementary ctx middle hpath
    have hKelem : IsElementaryAbelian 2 projection.ker := by
      rw [hkernel]
      exact IsElementaryAbelian.subgroupOf hWU
    have hKcomm : ⁅(⊤ : Subgroup U), projection.ker⁆ ≤ (ZAt ctx.Γ middle).subgroupOf U := by
      apply Subgroup.map_le_iff_le_comap.mp
      rw [Subgroup.map_commutator, hkernel,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hWU, Subgroup.commutator_comm]
      exact ten_one_generated_commutator_le_middle_center ctx middle hpath
    have hAelem (i : Fin 3) : IsElementaryAbelian 2 (A i) := by
      obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
      obtain ⟨mover, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
        middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hadj i))
      let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
        ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case
          (by rw [ctx.critical_length]; decide)).1
      have hVi : IsElementaryAbelian 2 (V i) := by
        change IsElementaryAbelian 2 (VAt ctx.Γ (vertex i))
        rw [← hmove, VAt, v_act]
        exact IsElementaryAbelian.map _
      let _ := hVi
      exact IsElementaryAbelian.subgroupOf (hVU i)
    have hcomm := Subgroup.commutator_le_of_elementary_kernel_three_lines
      projection hsurjective ((ZAt ctx.Γ middle).subgroupOf U)
      hKelem hKcomm A hAelem hfour hAcard hLdistinct
    have hDZ : DerivedAmbient U ≤ ZAt ctx.Γ middle := by
      rintro element ⟨x, hx, rfl⟩
      exact hcomm hx
    have hbound := Subgroup.card_le_of_le hDZ
    rw [show DerivedAmbient U = VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' from ten_one_large_derived ctx middle hpath hlarge hno,
      hlarge, (sectionTenOpeningData ctx middle hpath).center_card] at hbound
    omega
  obtain ⟨dimension, hdimension⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_card_eq
  have hdimensionUpper : dimension ≤ 3 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 4 ≤ dimension by omega)
    rw [hdimension] at hupper
    norm_num at hpow
    omega
  have hQcard : Nat.card Q = 8 := by
    interval_cases dimension <;> norm_num at hdimension <;> omega
  have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf U)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv] at hcount
  change Nat.card U = Nat.card Q * Nat.card W at hcount
  change Nat.card U = 8 * Nat.card W
  rwa [hQcard] at hcount

end Stellmacher.SectionTen
