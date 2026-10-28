module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Products
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Transport
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Dihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.LinearSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Unitary

/-!
# Assembly of the compatible Cartan argument in F.1.3(5)

Source: Aschbacher–Smith, printed p.260, final paragraph of the proof.
Hall theory supplies compatible individual abelian complements and proves
that their literal product is an odd Hall complement to S. Mutual
normalization makes conjugation by D₂ quadratic on D₁. Rigidity for the
actual rank-one quotient L₁/O₂(L₁), lifted through the two-core, then makes
D₁ and D₂ commute, hence their product is abelian.

All five quotient alternatives are discharged, including their small
parameters. The linear, Suzuki and unitary branches identify the actual
coefficient action and prove its rigidity; the projective unitary branch
accounts for the cubic scalar kernel. Thus `lemma_F_1_3_5` assumes only
F.1.1 and gives the literal products D₁D₂ and SD₁D₂. Its constructed
`CompatibleCartans` witness supplies the local and joint Hall complements;
`Products` gives their trivial intersections, coprime orders and exact
indices. No joint-commutativity conclusion is stored in the source input.
-/

public section
open Subgroup Subgroup.OddHall
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source

/-- Every concrete quotient alternative of F.1.1(c) has Cartan rigidity,
including PSL₂(2), Sz(2), SU₃(2), PSU₃(2) and D₁₀. No additional
semilinearity, simplicity or field-action premise remains. -/
theorem IsRankOneModel.cartanQuadraticRigidity {H : Type*} [Group H]
    (h : IsRankOneModel H) : CartanQuadraticRigidity H := by
  let : Finite H := h.finite
  cases h with
  | linear n hn h => exact cartanQuadraticRigidity_linear n hn h
  | suzuki m h =>
    obtain ⟨e⟩ := h
    exact cartanQuadraticRigidity_suzuki m e
  | projective_unitary n hn h => exact cartanQuadraticRigidity_projective_unitary hn h
  | special_unitary n hn h => exact cartanQuadraticRigidity_special_unitary hn h
  | dihedral h =>
    obtain ⟨e⟩ := h
    exact cartanQuadraticRigidity_of_dihedral_equiv e

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual quadratic conjugation action vanishes if the first local
rank-one quotient has Cartan rigidity. All Hall and normalization inputs
come from the constructed compatible complements. -/
theorem CompatibleCartans.abelian_of_quotient_rigidity
    (c : CompatibleCartans L S) (h : HypothesisF11 L S)
    (hr : CartanQuadraticRigidity ((L 0) ⧸ pCore 2 (L 0))) :
    IsMulCommutative (c.D 0 ⊔ c.D 1 : Subgroup G) := by
  let := h.finite_local 0
  let := h.finite_commonBorel
  let : Finite (c.D 1) := Finite.of_injective
    (inclusion ((c.le_borel 1).trans (borel_le_commonBorel 1))) (inclusion_injective _)
  let := c.abelian 0
  let := c.abelian 1
  obtain ⟨T,hT⟩ := h.sylow 0
  have hc : c.D 1 ≤ centralizer (c.D 0 : Set G) := by
    intro y hy x hx
    have hyodd : Odd (orderOf y) := by
      have he := (Nat.coprime_two_left.mp (c.odd 1)).of_dvd_nat
        (orderOf_dvd_natCard (⟨y,hy⟩ : c.D 1))
      rwa [← orderOf_injective (c.D 1).subtype (c.D 1).subtype_injective] at he
    have he := hr.of_twoCore_quotient.ambient T hT (c.le_borel 0) (c.odd 0)
      (c.local_disjoint 0) (c.local_sup 0) (h.cross 0 (c.le_borel 1 hy)) hyodd
      (h.cross_normalizes_localSylow 0 (c.le_borel 1 hy)) (c.normalizes 1 hy)
      (fun z hz => c.quadratic_conjugation hz hy) x hx
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  apply le_centralizer_iff_isMulCommutative.mp
  exact sup_le
    (le_centralizer_iff.mp (sup_le (c.D 0).le_centralizer hc))
    (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hc) (c.D 1).le_centralizer))

/-- Conditional F.1.3(5) assembly. The remaining premise is the concrete
rank-one quotient rigidity theorem, not joint commutativity itself.
The witness supplies Hall indices, disjointness, coprime orders and the
literal products via the theorems in `Products`. -/
theorem lemma_F_1_3_5_of_quotient_rigidity (h : HypothesisF11 L S)
    (hr : CartanQuadraticRigidity ((L 0) ⧸ pCore 2 (L 0))) :
    ∃ c : CompatibleCartans L S, IsMulCommutative (c.D 0 ⊔ c.D 1 : Subgroup G) := by
  obtain ⟨c⟩ := h.exists_compatibleCartans
  exact ⟨c, c.abelian_of_quotient_rigidity h hr⟩

/-- The compatible complements commute under F.1.1. Apply the concrete
rigidity theorem to the original quotient L₁/O₂(L₁) and lift its fixation
to the original conjugation action of D₂ on D₁. -/
theorem CompatibleCartans.joint_abelian (c : CompatibleCartans L S)
    (h : HypothesisF11 L S) : IsMulCommutative (c.D 0 ⊔ c.D 1 : Subgroup G) :=
  c.abelian_of_quotient_rigidity h (h.quotient 0).cartanQuadraticRigidity

/-- F.1.3(5): the local odd Hall complements can be chosen compatibly,
with abelian product D₁D₂ an odd Hall complement to S in B, and B = SD₁D₂.
The witness records both normalizations and the local and joint complement
conditions. The displayed set equalities identify the joins with the actual
source products; `local_disjoint`, `joint_disjoint`, `local_coprime`,
`joint_coprime`, `local_index` and `joint_index` give the corresponding
intersection, coprimality and index statements for this same witness. -/
theorem lemma_F_1_3_5 (h : HypothesisF11 L S) :
    ∃ c : CompatibleCartans L S,
      IsMulCommutative (c.D 0 ⊔ c.D 1 : Subgroup G) ∧
      ((c.D 0 ⊔ c.D 1 : Subgroup G) : Set G) = (c.D 0 : Set G) * (c.D 1 : Set G) ∧
      (commonBorel L S : Set G) = (S : Set G) * (c.D 0 : Set G) * (c.D 1 : Set G) := by
  obtain ⟨c⟩ := h.exists_compatibleCartans
  exact ⟨c, c.joint_abelian h, c.joint_coe_eq_mul, c.commonBorel_coe_eq_mul⟩

end CFSG.Quasithin.ChapterF.Source
