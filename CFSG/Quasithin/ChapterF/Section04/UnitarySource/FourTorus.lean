module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourTorus
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry

/-!
# The split torus on the actual projective U₄ flag

The fixed-field diagonal torus lies in the literal whole overlap. Its
parameter group has odd order. Injectivity of SU₄ projectivization carries
the two-element centralizer calculation to this same projective carrier.
The q=4 case remains included.

Source: the splitting clause of Aschbacher–Smith F.4.29(2), printed p.289
of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourTorus
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer
variable (m : ℕ) (hm : 1 ≤ m)

/-- The fixed-field torus in the literal projective flag overlap. -/
def flagTorus : ((PointLocal.FixedField m)ˣ × (PointLocal.FixedField m)ˣ) →* overlap m hm :=
  ((projection m hm).comp (FourTorus.torusHom (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm))).codRestrict _ (by
      intro x
      exact mem_map_of_mem _ (FourTorus.torusElement_mem_borel
        (MatrixField m) (fieldConj m) (fieldConj_involutive m hm) x.1 x.2))

include hm in
/-- Its parameter group has odd order, also for the first nonbinary parameter q=4. -/
theorem flagTorus_parameter_odd :
    Odd (Nat.card ((PointLocal.FixedField m)ˣ × (PointLocal.FixedField m)ˣ)) := by
  rw [Nat.card_prod,Nat.card_units,PointLocal.fixedField_card m hm]
  have hq : 1 < 2^m := Nat.one_lt_pow (by omega) (by decide)
  apply Odd.mul
  all_goals
    apply Nat.Even.sub_odd (by omega) _ (by decide : Odd 1)
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))

/-- No nonidentity projective two-element centralizes this same torus. -/
theorem projective_two_element_centralizer (hm' : 1<m)
    (g : ProjectiveGroup m hm) (k : ℕ) (hg : g^(2^k)=1)
    (ht : ∀ a : (PointLocal.FixedField m)ˣ × (PointLocal.FixedField m)ˣ,
      Commute g (flagTorus m hm a).val) : g=1 := by
  obtain ⟨u,rfl⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective
    (MatrixField m) (standardForm m hm) g
  have hup : u^(2^k)=1 := projection_injective m hm (by
    change projection m hm u ^ (2^k)=1 at hg
    simpa only [map_pow,map_one] using hg)
  have hq : 2 < Nat.card (PointLocal.FixedField m) := by
    rw [PointLocal.fixedField_card m hm]
    exact lt_of_le_of_lt (by decide : 2 ≤ 2^1) (Nat.pow_lt_pow_right (by decide) hm')
  have hut (a b : (PointLocal.FixedField m)ˣ) :
      Commute u (FourTorus.torusElement (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm) a b) := by
    apply (projection_injective m hm)
    exact ((projection m hm).map_mul _ _).trans
      ((ht (a,b)).eq.trans ((projection m hm).map_mul _ _).symm)
  have hu := FourTorus.two_element_centralizer (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) hq u k hup hut
  change projection m hm u = 1
  exact (congrArg (projection m hm) hu).trans (projection m hm).map_one
end CFSG.Quasithin.ChapterF.UnitarySource.FourTorus
