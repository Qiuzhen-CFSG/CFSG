module
public import Stellmacher.SectionTen.TenOneSmallEdgeInvolutionCore
public import Stellmacher.SectionTen.TenOneSmallEdgeCommutingPoint
public import Stellmacher.SectionTen.TenOneSmallLocalCentralizerCore
public import Stellmacher.SectionTen.TenOneSmallCommonCorePointFixed
public import Stellmacher.SectionTen.TenOneSmallTerminalCoreCentralizer
public import Stellmacher.SectionTen.TenOneSmallInvolutionEdgeNormalization
public import Stellmacher.SectionTen.TenOneSmallTerminalInvolutionOrbit
/-!
# Native conjugacy reduction for small commuting involutions

In the actual small Section Ten context, every involution in the middle
stabilizer that commutes with a Wstar point outside the middle center,
and itself lies outside that center, has a native conjugate in Wstar
outside the center. No ambient terminal-center conjugacy or solvability
hypothesis is imposed.

The initial Sylow conjugation moves the pair together into the terminal
edge. Unless the moved involution already lies in Wstar, the exact local
point centralizer puts it outside the middle core. The edge commuting-point
and involution lemmas then place the other point in W0 and the involution
in the terminal core. The terminal point-centralizer theorem puts both
points in the residual core, while the fixed-plane identity excludes the
involution from its module. The residual quotient orbit theorem supplies
a second native conjugator placing it in a coset of the middle center.
This coset lies in Wstar and avoids the center. Composing the two actual
conjugators gives the conclusion over the original graph and group.

This proves the reusable involution reduction in Stellmacher (10.1)(a3),
assertion (11), Journal of Algebra 190 (1997), printed p.62 of
`refs/files/stellmacher-n-group.pdf`. The terminal-center fusion and final
path arguments consume it without changing the critical-path context.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}
public theorem ten_one_small_commuting_involution_conjugate_wstar
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ centralizer (W0:Set G)
    ∀a u:G,a∈Wstar→a∉ZAt ctx.Γ middle→ orderOf u=2→u∈GAt ctx.Γ middle→
      Commute a u→u∉ZAt ctx.Γ middle→
      ∃g:G,MulAut.conj g u∈Wstar ∧ MulAut.conj g u∉ZAt ctx.Γ middle := by
  intro W0 Wstar a u ha haZ hu2 huM hcomm huZ
  have hcore := ten_one_small_terminal_core_centralizer_le_residual ctx middle hpath hsmall hmodel
  have hmove := ten_one_small_involution_edge_normalization ctx middle hpath hsmall hmodel
  have horbit := ten_one_small_terminal_involution_conjugate_coset ctx middle hpath hsmall hmodel
  let Γ := ctx.Γ
  let Z := ZAt Γ middle
  let terminal := ctx.criticalPath.a'
  obtain ⟨g,_,huEdge,haW,haZ',huZ',_,hcomm'⟩ := hmove a u ha haZ hu2 huM hcomm huZ
  let a' := MulAut.conj g a
  let u' := MulAut.conj g u
  change a'∈Wstar at haW
  change a'∉Z at haZ'
  change u'∈GAt Γ middle ⊓ GAt Γ terminal at huEdge
  change u'∉Z at huZ'
  change Commute a' u' at hcomm'
  by_cases huW : u'∈Wstar
  · exact ⟨g,huW,huZ'⟩
  have huQ : u'∉QAt Γ middle := by
    intro hh
    apply huW
    exact (ten_one_small_core_point_centralizer ctx middle hpath hsmall hmodel a' haW haZ').le
      ⟨hh,mem_centralizer_singleton_iff.mpr hcomm'.symm.eq⟩
  have haW0 : a'∈W0 := ten_one_small_edge_commuting_point_mem_wzero ctx middle hpath hsmall hmodel
    a' u' haW huEdge huQ hcomm'.symm
  have huSquare : u'^2=1 := by
    change (MulAut.conj g u)^2=1
    rw [←map_pow,←hu2,pow_orderOf_eq_one,map_one]
  have huQt : u'∈QAt Γ terminal := ten_one_small_edge_involution_mem_terminal_core
    ctx middle hpath hsmall hmodel u' huEdge huSquare huQ
  have hterminal : terminal∈Neighborhood Γ middle :=
    (mem_neighborhood_iff_adjacent Γ).mpr (sectionTenOpeningGeometry ctx middle hpath).2.2.1
  have hW0Qt : W0≤QAt Γ terminal := by
    apply inf_le_left.trans
    exact sInf_le ⟨terminal,hterminal,rfl⟩
  have haR : a'∈twoCoreIn (EAt Γ terminal) := hcore a' haW0 haZ'
    ⟨hW0Qt haW0,mem_centralizer_singleton_iff.mpr rfl⟩
  have huR : u'∈twoCoreIn (EAt Γ terminal) := hcore a' haW0 haZ'
    ⟨huQt,mem_centralizer_singleton_iff.mpr hcomm'.symm.eq⟩
  have huV : u'∉VAt Γ terminal := by
    intro hh
    apply huZ'
    exact (ten_one_small_common_core_point_terminal_fixed ctx middle hpath hsmall hmodel
      a' haW0 haZ').le ⟨hh,mem_centralizer_singleton_iff.mpr hcomm'.symm.eq⟩
  obtain ⟨n,_,z,hz,hn⟩ := horbit a' u' haW0 haZ' haR huR huV huSquare
  have hZW : Z≤Wstar := by
    have he : Wstar⊓twoCoreIn (EAt Γ middle)=Z :=
      (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
    exact he.ge.trans inf_le_left
  have hproduct : a'*z∈Wstar := Wstar.mul_mem haW (hZW hz)
  have hproductZ : a'*z∉Z := by
    intro hh
    apply haZ'
    simpa using Z.mul_mem hh (Z.inv_mem hz)
  have hconj : MulAut.conj (n*g) u=a'*z := by
    rw [map_mul,MulAut.mul_apply]
    exact hn
  exact ⟨n*g,hconj ▸ hproduct,hconj ▸ hproductZ⟩
end Stellmacher.SectionTen
