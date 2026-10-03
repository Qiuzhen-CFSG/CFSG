module
public import Stellmacher.SectionTen.TenOneSmallResidualExtraspecial
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupAction.ElementaryCentralIndexTwoDisplacement

/-!
# The central line of the first residual displacement

In the small first-module case, any subgroup of the first stabilizer whose
commutator with its residual two-core lies in the middle central plane
actually has that commutator in the first central line. The subgroup is
the supplied actual subgroup; no two-group assumption is needed.

The first residual core is extraspecial with center the first central
line. The middle central plane is elementary of order four, contains that
line, and lies in the first module. Actual conjugation by the first
stabilizer fixes the central line and therefore every residual-core square.
The elementary displacement theorem for a central layer of index two
puts each conjugation displacement in the first central line. Restricting
and then mapping actual subgroup elements gives the ambient commutator
containment.

This is the commutator refinement preceding (8) in Stellmacher (10.1)(a3),
printed p.61 of `refs/files/stellmacher-n-group.pdf`. Square preservation
makes the source's intermediate two-core containment unnecessary for this
specific refinement.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_commutator_le_first_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (D : Subgroup G) (hDP : D ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hcomm : ⁅D,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤ ZAt ctx.Γ middle) :
    ⁅D,twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let U := ZAt ctx.Γ middle
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def vertex
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hcenter : CenterAmbient R = Z :=
    ten_one_small_residual_center ctx middle hpath hsmall hmodel
  have hZnative : Subgroup.center R = Z.subgroupOf R := by
    rw [← hcenter]
    exact (Subgroup.comap_map_eq_self_of_injective R.subtype_injective _).symm
  have hUR : U ≤ R := by
    obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
    exact (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)).trans
      (ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel)
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ vertex ≤ ZAt ctx.Γ middle
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_left
  have hZU' : Subgroup.center R ≤ U.subgroupOf R := by
    rw [hZnative]
    exact Subgroup.subgroupOf_mono R hZU
  have hUcard : Nat.card (U.subgroupOf R) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  let _ : IsExtraspecial 2 R :=
    (ten_one_small_residual_extraspecial ctx middle hpath hsmall hmodel).1
  have hindex : ((Subgroup.center R).subgroupOf (U.subgroupOf R)).index = 2 := by
    have hh := ((Subgroup.center R).subgroupOf (U.subgroupOf R)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU').toEquiv,
      IsExtraspecial.center_order_p 2 R,hUcard] at hh
    omega
  let _ : IsElementaryAbelian 2 U := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 (U.subgroupOf R) := IsElementaryAbelian.subgroupOf hUR
  have hPZ : P ≤ Subgroup.centralizer (Z : Set G) :=
    nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      vertex ⟨1,ctx.Γ.act_one _⟩
  have hsquare (r : R) : r^2 ∈ Subgroup.center R := by
    let _ : IsElementaryAbelian 2 (R ⧸ Subgroup.center R) :=
      IsExtraspecial.quotient_elementary_abelian 2 R
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Subgroup.center R) (r^2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ Subgroup.center R)) _
  change ⁅D,R⁆ ≤ Z
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro r hr d hd
  let f : MulAut R := R.normalizerMonoidHom ⟨d,hPR (hDP hd)⟩
  have hfixsquare (s : R) : (f s)^2 = s^2 := by
    rw [← map_pow]
    apply Subtype.ext
    change d * (s:G)^2 * d⁻¹ = (s:G)^2
    have hsZ : (s:G)^2 ∈ Z := by
      have hh := hsquare s
      rw [hZnative] at hh
      exact hh
    have hc := Subgroup.mem_centralizer_iff.mp (hPZ (hDP hd)) ((s:G)^2) hsZ
    rw [← hc,mul_inv_cancel_right]
  have hdisplace (s : R) : s⁻¹ * f s ∈ U.subgroupOf R := by
    change (s:G)⁻¹ * (d * (s:G) * d⁻¹) ∈ U
    have hh := hcomm (Subgroup.commutator_mem_commutator hd (R.inv_mem s.property))
    have hi := U.inv_mem hh
    convert hi using 1
    simp only [commutatorElement_def]
    group
  have hh := MulAut.displacement_mem_center_of_elementary_central_index_two
    (U.subgroupOf R) hindex f hfixsquare hdisplace (⟨r,hr⟩ : R)⁻¹
  rw [hZnative] at hh
  change (r⁻¹)⁻¹ * (d * r⁻¹ * d⁻¹) ∈ Z at hh
  simpa only [commutatorElement_def,inv_inv,mul_assoc] using hh

end Stellmacher.SectionTen
