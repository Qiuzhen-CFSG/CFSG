module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Source fixed-plane placement and involution action

An outside element of the original Sylow product fixes an order9 plane.
The plane lies in the canonical extraspecial subgroup. Since the original
involution inverts that subgroup modulo its central cubic line, it preserves
the plane and inverts its induced cubic conjugation action. All statements
retain the chosen source axes and literal ambient subgroups.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem line_le_kernel : c.toSourceData.W≤c.toSourceData.V := by
  have hWX:c.toSourceData.W≤c.toSourceData.X:=zpowers_le.mpr ((c.actors_eq).le c.actors.x.property)
  exact hWX.trans (CubicNormalizer.le_oddKernel c.toSourceData.X (h.cubic_sylow_image_card P)
    (h.toCentralizerHypothesis.cubic_centralizer c.toSourceData.X (h.cubic_sylow_image_card P) (map_subtype_le _)))

omit [Finite G] in
theorem line_le_fixed : c.toSourceData.W≤centralizer z:=
  (zpowers_le.mpr ((c.actors_eq).le c.actors.x.property)).trans (map_subtype_le _)

omit [Finite G] in
theorem involution_normalizes_kernel : z∈normalizer (c.toSourceData.V:Set G) := by
  apply CubicNormalizer.normalizer_normalizes_oddKernel c.toSourceData.X
  apply centralizer_le_normalizer _
  intro x hx
  exact mem_centralizer_singleton_iff.mp ((map_subtype_le _ :c.toSourceData.X≤centralizer z) hx)

theorem outside_fixed_data (x:G) (hx:x∈c.toSourceData.Q) (hxV:x∉c.toSourceData.V) :
    let L:=c.toSourceData.V⊓Subgroup.centralizer ({x}:Set G)
    Nat.card L=9 ∧ c.toSourceData.Q≤normalizer (L:Set G) ∧ c.toSourceData.W≤L ∧ L≤c.toSourceData.D := by
  obtain ⟨hQN,_,hfix⟩:=h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial
  obtain ⟨hc,hn,hw⟩:=hfix x hx hxV
  refine ⟨hc,hn,hw,?_⟩
  let :IsElementaryAbelian 3 c.toSourceData.V:=c.kernel_elementary
  have hDN:c.toSourceData.D≤normalizer (c.toSourceData.V:Set G):=le_sup_right.trans hQN
  have hm:x∈(c.toSourceData.V:Set G)*(c.toSourceData.D:Set G):=by
    rw [←coe_mul_of_right_le_normalizer_left c.toSourceData.V c.toSourceData.D hDN]
    exact hx
  obtain ⟨v,hv,a,ha,rfl⟩:=hm
  have haV:a∉c.toSourceData.V:=fun hh=>hxV (c.toSourceData.V.mul_mem hv hh)
  intro l hl
  apply h.cubic_line_marked_outside_fixed P c.actors c.actors_eq c.odd_split c.odd_card a ha haV
  refine ⟨hl.1,mem_centralizer_singleton_iff.mpr ?_⟩
  have he:=mem_centralizer_singleton_iff.mp hl.2
  have hvl:l*v=v*l:=c.toSourceData.V.le_centralizer hv l hl.1
  rw [←mul_assoc,hvl,mul_assoc,mul_assoc] at he
  exact mul_left_cancel he

theorem outside_fixed_involution (x:G) (hx:x∈c.toSourceData.Q) (hxV:x∉c.toSourceData.V) :
    z∈normalizer ((c.toSourceData.V⊓Subgroup.centralizer ({x}:Set G):Subgroup G):Set G) := by
  let L:=c.toSourceData.V⊓Subgroup.centralizer ({x}:Set G)
  obtain ⟨_,_,hWL,hLD⟩:=c.outside_fixed_data x hx hxV
  have he:L.map (MulAut.conj z).toMonoidHom≤L:=by
    rintro y ⟨l,hl,rfl⟩
    have hh:=L.mul_mem (hWL (c.odd_inversion l (hLD hl))) (L.inv_mem hl)
    change z*l*z⁻¹∈L
    simpa only [mul_inv_cancel_right] using hh
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge he
    (by rw [card_map_of_injective (MulAut.conj z).injective]))

theorem outside_fixed_action_inversion (x:G) (hx:x∈c.toSourceData.Q) (hxV:x∉c.toSourceData.V) :
    ∀a∈c.toSourceData.D,z*a*z⁻¹*a∈Subgroup.centralizer
      ((c.toSourceData.V⊓Subgroup.centralizer ({x}:Set G):Subgroup G):Set G) := by
  obtain ⟨_,_,_,hLD⟩:=c.outside_fixed_data x hx hxV
  intro a ha
  apply (Subgroup.centralizer_le hLD)
  rw [c.odd_centralizer]
  exact c.odd_inversion a ha
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
