module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.Splitting

/-!
# Cubic relations lift through the original centralizer quotient

The full original centralizer is the marked product of its literal cubic
subgroup and its S5 quotient. Thus a cube-one element in that same quotient
has cube one in the original group. In particular this step does not infer
a mixed endpoint relation solely from a quotient calculation or ignore a
possible central element of order nine.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- A cubic relation in the literal odd-core quotient lifts to the full
original cubic centralizer, using its proved marked splitting. -/
theorem TypeAt.cubic_centralizer_cube_lift (h : TypeAt z V) (t : G)
    (ht : t∈involutionCentralizer z) (ht3 : orderOf t=3)
    (x : centralizer ({t}:Set G))
    (hx : (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({t}:Set G))) x)^3=1) :
    x^3=1 := by
  obtain ⟨φ,s,_,_,e,_,heq,_⟩ := h.cubic_centralizer_split t ht ht3
  let y := e.symm x
  have hk : y.1^3=1 := by
    apply Subtype.ext
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp y.1.property
    change (y.1:G)^3=1
    rw [←hn,←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul]
    simp only [zpow_natCast,show t^3=1 from ht3 ▸ pow_orderOf_eq_one t,one_zpow]
  have hg : y.2^3=1 := by
    have hy := heq y.1 y.2
    change φ ((QuotientGroup.mk' _) (e (e.symm x)))=y.2 at hy
    rw [e.apply_symm_apply] at hy
    rw [←hy,←map_pow,hx,map_one]
  have hy : y^3=1 := Prod.ext hk hg
  have hh := congrArg e hy
  simpa only [map_pow,map_one,e.apply_symm_apply,y] using hh

end CFSG.Quasithin.HigmanSims
