module
public import Stellmacher.SectionNine.DistanceOneAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.ElementaryTwoFactorInvolutions

/-!
# The small distance-one product quotient is commutative

For the same extracted distance-one action, let C and D be the crossed
intersections of the two vertex centers with the opposite stabilizers.
If their product has order at most four times the common center
intersection, then the product is commutative. No faithful-action or
numbered Section Nine conclusion is assumed.

Conjugation by the extracted x interchanges C and D, so their orders are
equal. If the product were noncommutative, the product-order formula and
the small bound would force their intersection to have index two in each.
The elementary index-two factor theorem then puts every involution of the
product in C or D. The second vertex center normalizes the product and
fixes D pointwise, so it must preserve C: an involution sent into D was
already fixed. The first vertex center centralizes C. Their join E
therefore normalizes C, whereas its element x interchanges C and D.
This forces C=D and contradicts noncommutativity.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (9.1), p.46,
the small-product-quotient step after relation (3). The actual E action is
essential; two elementary factors alone have a dihedral counterexample.
-/

namespace Stellmacher.SectionNine
open Stellmacher.SectionsFiveToSeven CosetGraphContext Stellmacher.Later
open scoped Pointwise
universe u

private theorem elementary_of_le {G : Type*} [Group G] (C A : Subgroup G)
    [IsElementaryAbelian 2 A] (hCA : C ≤ A) : IsElementaryAbelian 2 C where
  toIsMulCommutative := .of_setLike_mul_comm fun _x hx _y hy =>
    setLike_mul_comm (hCA hx) (hCA hy)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := A) x (hCA x.property))

private theorem fixes_factor_normalizes_other {G : Type*} [Group G]
    (C D actors : Subgroup G) [IsElementaryAbelian 2 D]
    (hn : actors ≤ Subgroup.normalizer ((C ⊔ D : Subgroup G) : Set G))
    (hfix : ∀ a ∈ actors, ∀ c ∈ C, (MulAut.conj a) c = c)
    (hunion : ∀ v ∈ C ⊔ D, v ^ 2 = 1 → v ∈ C ∨ v ∈ D) :
    actors ≤ Subgroup.normalizer (D : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro a ha d hd
  let f := MulAut.conj a
  have hfd : f d ∈ C ⊔ D := Subgroup.le_normalizer_iff.mp hn a ha d
    ((show D ≤ C ⊔ D from le_sup_right) hd)
  have hpow : (f d) ^ 2 = 1 := by rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian d hd, map_one]
  rcases hunion (f d) hfd hpow with hc | he
  · have hcfix := hfix a ha (f d) hc
    have heq : f d = d := f.injective hcfix
    change f d ∈ D
    rwa [heq]
  · exact he

private theorem factor_indices {G : Type*} [Group G] [Finite G]
    (C D : Subgroup G) [IsMulCommutative C]
    (hn : D ≤ Subgroup.normalizer (C : Set G))
    (heq : Nat.card C = Nat.card D)
    (hsmall : Nat.card ↥(C ⊔ D) ≤ 4 * Nat.card ↥(C ⊓ D))
    (hnot : ¬ IsMulCommutative ↥(C ⊔ D)) :
    (C ⊓ D).relIndex C = 2 ∧ (C ⊓ D).relIndex D = 2 := by
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hn
  have hiC := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (C ⊓ D) C bot_le inf_le_left
  have hiD := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (C ⊓ D) D bot_le inf_le_right
  simp only [Subgroup.relIndex_bot_left] at hiC hiD
  have hpos : 0 < Nat.card ↥(C ⊓ D) := Nat.card_pos
  have hindexeq : (C ⊓ D).relIndex C = (C ⊓ D).relIndex D := by nlinarith
  have hbound : (C ⊓ D).relIndex C ≤ 2 := by
    rw [← heq] at hprod
    have hcardbound : Nat.card C ≤ 2 * Nat.card ↥(C ⊓ D) := by nlinarith
    nlinarith
  have hpositive : 0 < (C ⊓ D).relIndex C :=
    Nat.pos_of_ne_zero ((C ⊓ D).subgroupOf C).index_ne_zero_of_finite
  have hne : (C ⊓ D).relIndex C ≠ 1 := by
    intro hone
    have hCD : C ≤ D := (Subgroup.relIndex_eq_one.mp hone).trans inf_le_right
    have hDC : D ≤ C := (Subgroup.eq_of_le_of_card_ge hCD heq.ge).ge
    have hjoin : C ⊔ D = C := sup_eq_left.mpr hDC
    apply hnot
    rw [hjoin]
    infer_instance
  constructor <;> omega

public theorem distance_one_product_abelian_of_small_quotient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (hsmall :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      Nat.card ↥((z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)) ≤
      4 * Nat.card ↥(z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    IsMulCommutative ↥((z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)) := by
  let first := z ctx.Γ ctx.criticalPath.a
  let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
  let second := z ctx.Γ next
  let C := first ⊓ stabilizer ctx.Γ next
  let D := second ⊓ stabilizer ctx.Γ ctx.criticalPath.a
  let V := C ⊔ D
  change IsMulCommutative V
  by_contra hnot
  have hneighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ : IsElementaryAbelian 2 first :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hsecond : second = first.map (MulAut.conj data.x).toMonoidHom := by
    simp only [second, next, first, z_act, inv_inv]
  let _ : IsElementaryAbelian 2 second := by
    rw [hsecond]
    exact IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 C := elementary_of_le C first inf_le_left
  let _ : IsElementaryAbelian 2 D := elementary_of_le D second inf_le_left
  have hgeometry := distance_one_product_factors ctx.Γ ctx.criticalPath.a next
  have hswap := distance_one_factor_transport ctx hb data.toDistanceOneExtractionData
  change C.map (MulAut.conj data.x).toMonoidHom = D ∧
    D.map (MulAut.conj data.x).toMonoidHom = C at hswap
  have hcard : Nat.card C = Nat.card D := by
    rw [← hswap.1, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hsmall' : Nat.card V ≤ 4 * Nat.card ↥(C ⊓ D) := by
    rw [hgeometry.2.2.2.2]
    exact hsmall
  obtain ⟨hidxC,hidxD⟩ := factor_indices C D hgeometry.2.1 hcard hsmall' hnot
  have hunion (v : G) (hv : v ∈ V) (hv2 : v ^ 2 = 1) : v ∈ C ∨ v ∈ D :=
    Subgroup.involution_mem_union_of_elementary_factors_index_two C D
      inferInstance inferInstance hgeometry.1 hgeometry.2.1 hidxC hidxD hnot hv hv2
  have hEnorm : data.E ≤ Subgroup.normalizer (V : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono le_sup_left le_rfl).trans data.product_action
  have hfirstE : first ≤ data.E := by rw [data.generated]; exact le_sup_left
  have hsecondE : second ≤ data.E := by rw [data.generated]; exact le_sup_right
  have hsecondNormC : second ≤ Subgroup.normalizer (C : Set G) := by
    apply fixes_factor_normalizes_other D C second
    · simpa only [sup_comm] using hsecondE.trans hEnorm
    · intro a ha d hd
      change a * d * a⁻¹ = d
      rw [setLike_mul_comm ha hd.1, mul_inv_cancel_right]
    · intro v hv hp
      exact (hunion v (by simpa only [sup_comm] using hv) hp).symm
  have hfirstNormC : first ≤ Subgroup.normalizer (C : Set G) :=
    ((Subgroup.le_centralizer first).trans (Subgroup.centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEC : data.E ≤ Subgroup.normalizer (C : Set G) := by
    rw [data.generated]
    exact sup_le hfirstNormC hsecondNormC
  have hCeqD : C = D :=
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEC data.x_mem_E)).symm.trans hswap.1
  have hVe : V = C := by dsimp only [V]; rw [← hCeqD, sup_idem]
  apply hnot
  rw [hVe]
  infer_instance
end Stellmacher.SectionNine
