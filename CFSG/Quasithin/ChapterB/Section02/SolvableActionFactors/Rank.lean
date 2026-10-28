module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.SymmetricThree
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.QuasithinBasic

/-!
# The solvable FF factor count from the original source rank

Three distinct concrete factors would give a surjection onto S₃³: restrict
the original quotient map to the inverse image of the offender subgroup,
use its internal product coordinates, and project to three selected factors.
The source of this surjection remains a subgroup of the original group.
The A.1.31 section obstruction therefore bounds the number of factors by two.

No condition is imposed on the action kernel. In particular this is not
an application of prime-rank monotonicity across arbitrary quotients.
The positive factor count then leaves exactly one or two factors, as in
Aschbacher–Smith 14.1.7, printed p.977, using A.1.31(1), printed pp.27–28.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

/-- Any original rank-two group surjecting onto the actor bounds all concrete factors. -/
theorem count_le_two_of_surjective_threeRank
    {H : Type*} [Group H] [Finite H] (q : H →* G) (hq : Function.Surjective q)
    (hrank : primeRank 3 H ≤ 2) : d.count ≤ 2 := by
  classical
  by_contra hn
  have hthree : 3 ≤ d.count := by omega
  let i0 : Fin d.count := ⟨0, by omega⟩
  let i1 : Fin d.count := ⟨1, by omega⟩
  let i2 : Fin d.count := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0,i1]
  have h02 : i0 ≠ i2 := by simp [i0,i2]
  have h12 : i1 ≠ i2 := by simp [i1,i2]
  let es := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let models (i : Fin d.count) := (d.factorModel i).trans es
  let r : ((i : Fin d.count) → d.factor i) →*
      (Equiv.Perm (Fin 3) × (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := {
    toFun := fun g => (models i0 (g i0),models i1 (g i1),models i2 (g i2))
    map_one' := by simp
    map_mul' := fun a b => by simp }
  have hr : Function.Surjective r := by
    rintro ⟨a,b,c⟩
    refine ⟨Pi.mulSingle i0 ((models i0).symm a) *
      Pi.mulSingle i1 ((models i1).symm b) * Pi.mulSingle i2 ((models i2).symm c), ?_⟩
    simp [r,h01,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12]
  let K := (offenderSubgroup ρ).comap q
  let qK : K →* offenderSubgroup ρ := {
    toFun := fun x => ⟨q x,x.property⟩
    map_one' := Subtype.ext q.map_one
    map_mul' := fun a b => Subtype.ext (q.map_mul a b) }
  have hqK : Function.Surjective qK := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change q x ∈ offenderSubgroup ρ
    rw [hx]
    exact y.property
  exact not_surjective_symmetricThreeCube_of_threeRank_le_two
    ((Theory.GroupTheory.primeRank_le_of_injective 3 K.subtype K.subtype_injective).trans hrank)
    (r.comp (d.groupProduct.symm.toMonoidHom.comp qK))
    (hr.comp (d.groupProduct.symm.surjective.comp hqK))

/-- The actual positive factor family has exactly one or two members. -/
theorem count_eq_one_or_two_of_surjective_threeRank
    {H : Type*} [Group H] [Finite H] (q : H →* G) (hq : Function.Surjective q)
    (hrank : primeRank 3 H ≤ 2) : d.count = 1 ∨ d.count = 2 := by
  have h := d.count_le_two_of_surjective_threeRank q hq hrank
  have hp := d.count_pos
  omega

end CFSG.Quasithin.ChapterB.SolvableFFFactors
