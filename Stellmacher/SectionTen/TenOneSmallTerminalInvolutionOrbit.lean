module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientAction
public import Stellmacher.SectionTen.TenOneSmallCommonCorePointFixed
public import Theory.GroupAction.FourAutomorphismOrbit

/-!
# Terminal residual involutions meet the prescribed common-core coset

In the small case of (10.1), let a lie in the literal common-core subgroup W0
outside the middle center and in the actual terminal residual two-core. Every
involution u of that residual core outside the terminal module has a conjugate
a*z, with z in the middle center, under an element of the terminal stabilizer.
The explicit residual-core membership of a is supplied separately by the
point-centralizer reduction. No commutation or terminal-center conjugacy
hypothesis is added.

The fixed-plane theorem first shows a is outside the terminal module. One
actual middle-stabilizer neighbor mover pulls a and u back into the first
residual core, retaining the original critical context. Its proved elementary
four-quotient and exact supplied conjugation action have image of order greater
than two. The automorphism orbit theorem makes the two nonidentity cosets
conjugate. Inverting that actor and mapping back places u in a*Vend under an
actual terminal-stabilizer conjugation. Since conjugation preserves square
one, the common-core coset-square criterion puts its coefficient in Zmiddle.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1)(a3),
assertion (11), printed p.62 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}
public theorem ten_one_small_terminal_involution_conjugate_coset
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a u : G)
    (ha : a ∈ NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle)
    (haZ : a ∉ ZAt ctx.Γ middle)
    (haR : a ∈ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
    (huR : u ∈ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
    (huV : u ∉ VAt ctx.Γ ctx.criticalPath.a') (hu2 : u^2=1) :
    ∃ g : G, g ∈ GAt ctx.Γ ctx.criticalPath.a' ∧
      ∃ z : G, z ∈ ZAt ctx.Γ middle ∧ MulAut.conj g u = a*z := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := twoCoreIn (EAt Γ cp.firstStep)
  let V := VAt Γ cp.firstStep
  let Pt := GAt Γ cp.a'
  let Rt := twoCoreIn (EAt Γ cp.a')
  let Vt := VAt Γ cp.a'
  have haV : a ∉ Vt := by
    intro hh
    apply haZ
    exact (ten_one_small_common_core_point_terminal_fixed ctx middle hpath hsmall hmodel
      a ha haZ).le ⟨hh,mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  let f : MulAut G := MulAut.conj (mover:G)⁻¹
  have hRmap : R.map f.toMonoidHom=Rt := by
    change (twoCoreIn (Γ.twoResidualAt cp.firstStep)).map f.toMonoidHom =
      twoCoreIn (Γ.twoResidualAt cp.a')
    rw [←hmove,Γ.twoResidualAt_def,Γ.twoResidualAt_def]
    change _=twoCoreIn (twoResidualIn (stabilizer Γ (Γ.act (mover:G) cp.firstStep)))
    rw [stabilizer_act,conjugateBy,twoResidualIn_map_equiv,twoCoreIn_map_equiv]
    rfl
  have hVmap : V.map f.toMonoidHom=Vt := by
    change _=v Γ cp.a'
    rw [←hmove,v_act]
  have hPmap : P.map f.toMonoidHom=Pt := by
    change _=stabilizer Γ cp.a'
    rw [←hmove,stabilizer_act]
    rfl
  obtain ⟨a1,ha1,hea⟩ := mem_map.mp (show a∈R.map f.toMonoidHom from hRmap.symm ▸ haR)
  obtain ⟨u1,hu1,heu⟩ := mem_map.mp (show u∈R.map f.toMonoidHom from hRmap.symm ▸ huR)
  have ha1V : a1 ∉ V := by
    intro hh
    apply haV
    rw [←hea,←hVmap]
    exact mem_map_of_mem f.toMonoidHom hh
  have hu1V : u1 ∉ V := by
    intro hh
    apply huV
    change u ∈ Vt
    rw [←heu,←hVmap]
    exact mem_map_of_mem f.toMonoidHom hh
  obtain ⟨hN,hPR,hW,hWcard,action,hformula,_,hlarge⟩ :=
    ten_one_small_residual_quotient_action ctx middle hpath hsmall hmodel
  let _ := hN
  let _ := hW
  let W := R ⧸ V.subgroupOf R
  let π : R →* W := QuotientGroup.mk' (V.subgroupOf R)
  let abar : W := π ⟨a1,ha1⟩
  let ubar : W := π ⟨u1,hu1⟩
  have hane : abar ≠ 1 := by
    intro hh
    exact ha1V ((QuotientGroup.eq_one_iff (N := V.subgroupOf R) (⟨a1,ha1⟩ : R)).mp hh)
  have hune : ubar ≠ 1 := by
    intro hh
    exact hu1V ((QuotientGroup.eq_one_iff (N := V.subgroupOf R) (⟨u1,hu1⟩ : R)).mp hh)
  obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup hWcard action.range hlarge
      abar hane ubar hune)
  obtain ⟨g,hg⟩ := k.property
  have horbit : action g abar = ubar := by
    change (k:MulAut W) abar=ubar at hk
    rwa [←hg] at hk
  have hinv : action g⁻¹ ubar = abar := by
    rw [←horbit,map_inv]
    exact (action g).symm_apply_apply abar
  rw [hformula] at hinv
  have hv : a1⁻¹*((g⁻¹:G)*u1*(g⁻¹:G)⁻¹) ∈ V :=
    (QuotientGroup.eq (s := V.subgroupOf R)).mp hinv.symm
  let v := a1⁻¹*((g⁻¹:G)*u1*(g⁻¹:G)⁻¹)
  have hvt : f v ∈ Vt := by
    rw [←hVmap]
    exact mem_map_of_mem f.toMonoidHom hv
  have heq : MulAut.conj (f (g⁻¹:G)) u = a * f v := by
    rw [←heu,←hea]
    change f (g⁻¹:G)*f u1*(f (g⁻¹:G))⁻¹=f a1*f v
    rw [←map_inv,←map_mul,←map_mul,←map_mul]
    apply congrArg f
    dsimp [v]
    group
  have hsq : (a*f v)^2=1 := by
    rw [←heq,←map_pow,hu2,map_one]
  have hz : f v ∈ ZAt Γ middle :=
    (ten_one_small_common_core_coset_square_eq_one_iff ctx middle hpath hsmall hmodel
      a ha haZ (f v) hvt).mp hsq
  refine ⟨f (g⁻¹:G),?_,f v,hz,heq⟩
  change f (g⁻¹:G) ∈ Pt
  rw [←hPmap]
  exact mem_map_of_mem f.toMonoidHom (P.inv_mem g.property)
end Stellmacher.SectionTen
