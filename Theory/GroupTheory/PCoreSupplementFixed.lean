module
public import Theory.GroupTheory.PCoreAbelianQuotient
public import Theory.GroupTheory.PCoreRestriction

/-!
# Fixed elements modulo a prime core

Let a subgroup Y be normal in its join with S. If Y/Oₚ(Y) is abelian,
then a class in this quotient fixed by every element of S is central
in the quotient of YS by its prime core. When that quotient is center-free,
the class is trivial. The proof uses only the valid restriction
Y ∩ Oₚ(YS) ≤ Oₚ(Y), rather than any normality of Y in a larger component.

The source application is Aschbacher–Smith15.3.21, printed p.1127,
with the actual second-choice quotient S₃×S₃.
-/

public section
open Subgroup
open scoped commutatorElement

namespace Subgroup
variable {G : Type*} [Group G]

theorem mem_pCoreIn_of_supplement_fixed
    (p : ℕ) (Y S : Subgroup G)
    (hn : Y ⊔ S ≤ normalizer (Y : Set G))
    (hcomm : ⁅Y,Y⁆ ≤ Y.pCoreIn p)
    (hcenter : center ((Y ⊔ S : Subgroup G) ⧸ pCore p (Y ⊔ S : Subgroup G)) = ⊥)
    (y : G) (hy : y ∈ Y)
    (hfixed : ∀ s ∈ S, ⁅s,y⁆ ∈ Y.pCoreIn p) : y ∈ Y.pCoreIn p := by
  let H := Y ⊔ S
  let q := QuotientGroup.mk' (pCore p H)
  let yy : H := ⟨y, mem_sup_left hy⟩
  let D := (centralizer ({q yy} : Set (H ⧸ pCore p H))).comap q
  have hcore : Y.pCoreIn p ≤ H.pCoreIn p := pCoreIn_mono_of_normalizes le_sup_left hn
  have hzero (a : G) (ha : a ∈ H) (hc : ⁅a,y⁆ ∈ H.pCoreIn p) :
      q ⟨a,ha⟩ * q yy = q yy * q ⟨a,ha⟩ := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨t,ht,he⟩ := hc
    have he' : t = ⁅(⟨a,ha⟩ : H),yy⁆ := Subtype.ext he
    exact he' ▸ ht
  have hY : Y ≤ D.map H.subtype := by
    intro a ha
    refine ⟨⟨a, mem_sup_left ha⟩, ?_, rfl⟩
    change q ⟨a,mem_sup_left ha⟩ ∈ centralizer ({q yy} : Set (H ⧸ pCore p H))
    exact mem_centralizer_singleton_iff.mpr
      (hzero a (mem_sup_left ha) (hcore (hcomm (commutator_mem_commutator ha hy))))
  have hS : S ≤ D.map H.subtype := by
    intro a ha
    refine ⟨⟨a,mem_sup_right ha⟩, ?_, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (hzero a (mem_sup_right ha) (hcore (hfixed a ha)))
  have hz : q yy ∈ center (H ⧸ pCore p H) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore p H) a
    obtain ⟨t,ht,he⟩ := (sup_le hY hS) b.property
    have htb : t = b := Subtype.ext he
    subst t
    exact mem_centralizer_singleton_iff.mp ht
  change center (H ⧸ pCore p H) = ⊥ at hcenter
  have hyy : q yy = 1 := by
    rw [hcenter] at hz
    exact hz
  have hycore : y ∈ H.pCoreIn p :=
    ⟨yy, (QuotientGroup.eq_one_iff _).mp hyy,rfl⟩
  exact inf_pCoreIn_le_of_le p le_sup_left ⟨hy,hycore⟩

end Subgroup
