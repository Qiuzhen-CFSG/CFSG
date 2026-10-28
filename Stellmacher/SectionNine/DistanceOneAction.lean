module

public import Stellmacher.SectionNine.DistanceOneCoatom

/-!
# The distance-one local action through relations (1)--(2)

In an ambient-retaining Section Nine context with critical length one, the
coatom transfer and elementary-actor extraction give a single conjugator x,
its generated group E, and the two product factors C and D. The right-action
vertex convention remains `next = Gamma.act x⁻¹ alpha`. This module proves
the remaining initial commutator relation and the action bound in (1), and
packages them with the unchanged extraction in `DistanceOneActionData`.
The extraction module already supplies the central intersection and the
centralizer/core-intersection calculations of (2). The coatom identification
converts its cardinality and actor conditions into the source's (ii) and (v).

The quotient two-core is central because the quotient is an odd-dihedral
product with an abelian factor. Mapping the coatom into that core gives
[C,E] ≤ Q_beta. Since x² belongs to Q_beta ≤ G_alpha, conjugation by x
interchanges C and D; this transfers the commutator bound to D. The cross
commutators [D,Z_alpha] and [C,Z_next] then lie in C and D respectively.
Thus the generators of E normalize V = C join D. Likewise Q_beta normalizes
both factors, and [Q_beta,Z_alpha] ≤ C and [Q_beta,Z_next] ≤ D. Commutator
induction over the two joins proves [V join Q_beta,E] ≤ V. The two factors
normalize each other by `distance_one_product_factors`, so this join is the
literal product in the source, not an enlarged substitute.

Source: Stellmacher (9.1), journal p.46, initial relations (i)--(v) and
(1)--(2). Hypothesis Two remains on the ambient group H. The residual
centralization and the cardinal inequalities in (3)--(4) are not fields
of this record and remain obligations for the local-geometry assembly.
-/

namespace Stellmacher.SectionNine

open Stellmacher.SectionsFiveToSeven CosetGraphContext Stellmacher.Later
open scoped Pointwise commutatorElement

universe u

attribute [local instance] QuotientDihedralProduct.barL_group
  QuotientDihedralProduct.barL_finite

public theorem distance_one_coatom_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx) :
    ⁅data.coatom, data.E⁆ ≤ q ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨model⟩ := data.quotient
  have hforward : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hforward
  let _ : IsMulCommutative data.coatom :=
    IsMulCommutative.of_setLike_mul_comm fun first hfirst second hsecond =>
      setLike_mul_comm (s := z ctx.Γ ctx.criticalPath.a)
        (data.coatom_eq ▸ hfirst).1 (data.coatom_eq ▸ hsecond).1
  let _ : IsMulCommutative model.barA0 := by
    rw [model.barA0_image]
    infer_instance
  have hcentral := dihedralProduct_twoCore_le_center model.barL model.barA0
    (model.p ^ model.n) model.p_odd.pow model.model
  have hmap : (pCore 2 data.E).map model.quotientMap ≤ pCore 2 model.barL :=
    le_sSup ⟨pCore_normal.map model.quotientMap model.quotient_surjective,
      pCore_isPGroup.map model.quotientMap⟩
  apply Subgroup.commutator_le.mpr
  intro actor hactor element helement
  obtain ⟨actorE, hactorE, heq⟩ := (data.coatom_eq ▸ hactor).2
  change (actorE : G) = actor at heq
  let elementE : data.E := ⟨element, helement⟩
  have hcomm := Subgroup.mem_center_iff.mp
    (hcentral (hmap (Subgroup.mem_map_of_mem model.quotientMap hactorE)))
      (model.quotientMap elementE)
  have hkernel : ⁅actorE, elementE⁆ ∈ model.quotientMap.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement, commutatorElement_def, ← hcomm]
    simp [mul_assoc]
  have hbound := (model.quotient_kernel ▸ hkernel).2
  change ⁅(actorE : G), element⁆ ∈ q ctx.Γ ctx.criticalPath.a' at hbound
  simpa only [heq] using hbound

public theorem distance_one_factor_transport
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    C.map (MulAut.conj data.x).toMonoidHom = D ∧
    D.map (MulAut.conj data.x).toMonoidHom = C := by
  have hbackward : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.a' := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact ctx.criticalPath.endpoint_distance.trans hb
  have hcore : q ctx.Γ ctx.criticalPath.a' ≤ stabilizer ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _ hbackward default).2.2
  have hsq := hcore data.x_sq_mem
  have hnextZ : z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      (z ctx.Γ ctx.criticalPath.a).conjBy data.x := by
    rw [z_act, inv_inv]
    rfl
  have hnextG : stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      (stabilizer ctx.Γ ctx.criticalPath.a).conjBy data.x := by
    rw [stabilizer_act, inv_inv]
    rfl
  have hswapZ : ((z ctx.Γ ctx.criticalPath.a).conjBy data.x).conjBy data.x =
      z ctx.Γ ctx.criticalPath.a := by
    rw [Subgroup.conjBy_conjBy, ← pow_two]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_z ctx.Γ _ hsq)
  have hswapG : ((stabilizer ctx.Γ ctx.criticalPath.a).conjBy data.x).conjBy data.x =
      stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [Subgroup.conjBy_conjBy, ← pow_two]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsq)
  dsimp only
  rw [Subgroup.map_inf _ _ _ (MulAut.conj data.x).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj data.x).injective]
  simp only [hnextZ, hnextG]
  change _ ∧ _
  constructor
  · exact congrArg (_ ⊓ ·) hswapG
  · exact congrArg (· ⊓ _) hswapZ

private theorem normalizes_join_of_commutator_le
    {G : Type*} [Group G] (actors first second : Subgroup G)
    (hfirst : ⁅actors, first⁆ ≤ first ⊔ second)
    (hsecond : ⁅actors, second⁆ ≤ first ⊔ second) :
    actors ≤ Subgroup.normalizer ((first ⊔ second : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hmap : (first ⊔ second).map (MulAut.conj actor).toMonoidHom ≤ first ⊔ second := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨original, horiginal, rfl⟩
      have hmul := (first ⊔ second).mul_mem
        (Subgroup.commutator_le.mp hfirst actor hactor original horiginal)
        ((show first ≤ first ⊔ second from le_sup_left) horiginal)
      simpa only [commutatorElement_def, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        mul_assoc, inv_mul_cancel, mul_one] using hmul
    · rintro _ ⟨original, horiginal, rfl⟩
      have hmul := (first ⊔ second).mul_mem
        (Subgroup.commutator_le.mp hsecond actor hactor original horiginal)
        ((show second ≤ first ⊔ second from le_sup_right) horiginal)
      simpa only [commutatorElement_def, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        mul_assoc, inv_mul_cancel, mul_one] using hmul
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom helement)

private theorem commutator_join_right_le
    {G : Type*} [Group G] (actors first second target : Subgroup G)
    (hnorm : first ⊔ second ≤ Subgroup.normalizer (target : Set G))
    (hfirst : ⁅actors, first⁆ ≤ target) (hsecond : ⁅actors, second⁆ ≤ target) :
    ⁅actors, first ⊔ second⁆ ≤ target := by
  apply Subgroup.commutator_le.mpr
  intro actor hactor element helement
  have hclosure : Subgroup.closure ((first : Set G) ∪ (second : Set G)) = first ⊔ second := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [← hclosure] at helement
  induction helement using Subgroup.closure_induction with
  | mem element helement =>
    rcases helement with hmem | hmem
    · exact Subgroup.commutator_le.mp hfirst actor hactor element hmem
    · exact Subgroup.commutator_le.mp hsecond actor hactor element hmem
  | one => simp
  | mul firstElement secondElement hfirstMem _ hfirstComm hsecondComm =>
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using target.mul_mem hfirstComm
      ((Subgroup.le_normalizer_iff.mp hnorm firstElement (hclosure ▸ hfirstMem))
        _ hsecondComm)
  | inv element helement hcomm =>
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa only [inv_inv] using Subgroup.le_normalizer_iff.mp hnorm element⁻¹
      ((first ⊔ second).inv_mem (hclosure ▸ helement)) _ (target.inv_mem hcomm)

public theorem distance_one_extracted_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (hcoatom : data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    ⁅(C ⊔ D) ⊔ q ctx.Γ ctx.criticalPath.a', data.E⁆ ≤ C ⊔ D := by
  let first := z ctx.Γ ctx.criticalPath.a
  let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
  let second := z ctx.Γ next
  let C := first ⊓ stabilizer ctx.Γ next
  let D := second ⊓ stabilizer ctx.Γ ctx.criticalPath.a
  let V := C ⊔ D
  let Q := q ctx.Γ ctx.criticalPath.a'
  have hfirstE : first ≤ data.E := by rw [data.generated]; exact le_sup_left
  have hsecondE : second ≤ data.E := by rw [data.generated]; exact le_sup_right
  have hfirstNeighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  have hbackward : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.a' := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact ctx.criticalPath.endpoint_distance.trans hb
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hfirstNeighbor
  have hsecond : second = first.map (MulAut.conj data.x).toMonoidHom := by
    simp only [second, next, first, z_act, inv_inv]
  let _ : IsMulCommutative second := by rw [hsecond]; infer_instance
  have hQE : data.E ≤ Subgroup.normalizer (Q : Set G) :=
    data.E_le.trans (SevenSix.stabilizer_le_normalizer_q ctx.Γ _)
  have hQmap : Q.map (MulAut.conj data.x).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQE data.x_mem_E)
  have hEmap : data.E.map (MulAut.conj data.x).toMonoidHom = data.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer data.x_mem_E)
  have hQfirst : Q ≤ stabilizer ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _ hbackward default).2.2
  have hQnext : Q ≤ stabilizer ctx.Γ next := by
    dsimp only [next]
    rw [stabilizer_act, inv_inv]
    change Q ≤ (stabilizer ctx.Γ ctx.criticalPath.a).map (MulAut.conj data.x).toMonoidHom
    rw [← hQmap]
    exact Subgroup.map_mono hQfirst
  have hCE : ⁅C, data.E⁆ ≤ Q := by
    have hcoatom' : data.coatom = C := hcoatom
    rw [← hcoatom']
    exact distance_one_coatom_commutator ctx hb data
  have hDE : ⁅D, data.E⁆ ≤ Q := by
    have hmapped := Subgroup.map_mono (f := (MulAut.conj data.x).toMonoidHom) hCE
    rw [Subgroup.map_commutator, (distance_one_factor_transport ctx hb data).1,
      hEmap, hQmap] at hmapped
    exact hmapped
  have hCsecond : C ≤ Subgroup.normalizer (second : Set G) :=
    inf_le_right.trans (stabilizer_le_normalizer_z ctx.Γ next)
  have hDfirst : D ≤ Subgroup.normalizer (first : Set G) :=
    inf_le_right.trans (stabilizer_le_normalizer_z ctx.Γ _)
  have hcrossFirst : ⁅D, first⁆ ≤ C := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hDfirst)
    (((Subgroup.commutator_mono le_rfl hfirstE).trans hDE).trans hQnext)
  have hcrossSecond : ⁅C, second⁆ ≤ D := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hCsecond)
    (((Subgroup.commutator_mono le_rfl hsecondE).trans hCE).trans hQfirst)
  have hfirstC : ⁅first, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((Subgroup.le_centralizer first).trans (Subgroup.centralizer_le inf_le_left))
  have hsecondD : ⁅second, D⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((Subgroup.le_centralizer second).trans (Subgroup.centralizer_le inf_le_left))
  have hEnorm : data.E ≤ Subgroup.normalizer (V : Set G) := by
    rw [data.generated]
    apply sup_le
    · apply normalizes_join_of_commutator_le _ C D
      · rw [hfirstC]; exact bot_le
      · rw [Subgroup.commutator_comm]; exact hcrossFirst.trans le_sup_left
    · apply normalizes_join_of_commutator_le _ C D
      · rw [Subgroup.commutator_comm]; exact hcrossSecond.trans le_sup_right
      · rw [hsecondD]; exact bot_le
  have hQfirstComm : ⁅Q, first⁆ ≤ C := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hQfirst.trans (stabilizer_le_normalizer_z ctx.Γ _)))
    (((Subgroup.le_normalizer_iff_commutator_le_left.mp hQE).trans'
      (Subgroup.commutator_mono le_rfl hfirstE)).trans hQnext)
  have hQsecondComm : ⁅Q, second⁆ ≤ D := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hQnext.trans (stabilizer_le_normalizer_z ctx.Γ _)))
    (((Subgroup.le_normalizer_iff_commutator_le_left.mp hQE).trans'
      (Subgroup.commutator_mono le_rfl hsecondE)).trans hQfirst)
  have hQnorm : Q ≤ Subgroup.normalizer (V : Set G) := by
    have hQC : Q ≤ Subgroup.normalizer (C : Set G) :=
      (le_inf (hQfirst.trans (stabilizer_le_normalizer_z ctx.Γ _))
        (hQnext.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
      (le_inf (hQnext.trans (stabilizer_le_normalizer_z ctx.Γ _))
        (hQfirst.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hQC hQD).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C D)
  have hQEcomm : ⁅Q, data.E⁆ ≤ V := by
    rw [data.generated]
    exact commutator_join_right_le Q first second V
      (data.generated ▸ hEnorm) (hQfirstComm.trans le_sup_left)
      (hQsecondComm.trans le_sup_right)
  change ⁅V ⊔ Q, data.E⁆ ≤ V
  rw [Subgroup.commutator_comm]
  exact commutator_join_right_le data.E V Q V (sup_le Subgroup.le_normalizer hQnorm)
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hEnorm)
    (by rw [Subgroup.commutator_comm]; exact hQEcomm)

public structure DistanceOneActionData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    extends DistanceOneExtractionData ctx where
  coatom_stabilizer : coatom = z ctx.Γ ctx.criticalPath.a ⊓
    stabilizer ctx.Γ (ctx.Γ.act x⁻¹ ctx.criticalPath.a)
  coatom_commutator : ⁅coatom, E⁆ ≤ q ctx.Γ ctx.criticalPath.a'
  product_action :
    let next := ctx.Γ.act x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    ⁅(C ⊔ D) ⊔ q ctx.Γ ctx.criticalPath.a', E⁆ ≤ C ⊔ D

public theorem distance_one_initial_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    Nonempty (DistanceOneActionData ctx) := by
  obtain ⟨data, hcoatom⟩ := distance_one_coatom_eq_stabilizer_intersection ctx hb
  exact ⟨{
    toDistanceOneExtractionData := data
    coatom_stabilizer := hcoatom
    coatom_commutator := distance_one_coatom_commutator ctx hb data
    product_action := distance_one_extracted_action ctx hb data hcoatom }⟩


end Stellmacher.SectionNine
