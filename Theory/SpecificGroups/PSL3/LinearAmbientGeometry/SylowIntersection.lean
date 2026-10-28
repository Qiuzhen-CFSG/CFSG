module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Common centralizers in an even unitriangular group

Noncommuting involutions in UT₃(F) have common centralizer equal to its
center, and their product has exponent dividing four. The two root-plane
centralizers prove the first assertion; the coordinate square proves the
second. Both assertions are transported through one actual equivalence
onto the specified ambient subgroup.

These intrinsic facts support the nontrivial Sylow-intersection cases in
Aschbacher–Smith F.4.48, printed p.298 (`refs/quasithin.pdf`). Ambient
centralizer cores and fusion are supplied by the Chapter6 consumer.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [CharP F 2]

theorem unipotent_pow_four (a : U F) : a^4=1 := by
  rw [show (4:ℕ)=2*2 from rfl,pow_mul]
  apply (square_eq_one_iff F _).mpr
  left
  simp [pow_two,CharTwo.add_self_eq_zero]

theorem unipotent_noncommuting_centralizers (a b : U F)
    (ha : a^2=1) (hb : b^2=1) (hab : ¬ Commute a b) :
    centralizer ({a} : Set (U F)) ⊓ centralizer ({b} : Set (U F)) = Z F := by
  have haz : a ∉ Z F := by
    intro hz
    exact hab ((mem_center_iff.mp ((Z_eq_center F) ▸ hz) b).symm)
  have hbz : b ∉ Z F := by
    intro hz
    exact hab (mem_center_iff.mp ((Z_eq_center F) ▸ hz) a)
  have hne : centralizer ({a} : Set (U F)) ≠ centralizer ({b} : Set (U F)) := by
    intro hh
    apply hab
    apply mem_centralizer_singleton_iff.mp
    rw [←hh]
    exact mem_centralizer_singleton_iff.mpr rfl
  rcases centralizer_involution F a ha haz with h₁ | h₁ <;>
    rcases centralizer_involution F b hb hbz with h₂ | h₂
  · exact (hne (h₁.trans h₂.symm)).elim
  · rw [h₁,h₂,root_planes_inter]
  · rw [h₁,h₂,inf_comm,root_planes_inter]
  · exact (hne (h₁.trans h₂.symm)).elim

variable {G : Type*} [Group G] (P : Subgroup G) (e : U F ≃* P)
include e

theorem marked_pow_four (a : G) (ha : a ∈ P) : a^4=1 := by
  let x := e.symm ⟨a,ha⟩
  have hx : markedHom F P e x=a := congrArg Subtype.val (e.apply_symm_apply _)
  rw [←hx,←map_pow,unipotent_pow_four,map_one]

theorem marked_noncommuting_centralizers (a b : G)
    (haP : a ∈ P) (hbP : b ∈ P) (ha : a^2=1) (hb : b^2=1)
    (hab : ¬ Commute a b) :
    (P ⊓ centralizer ({a} : Set G)) ⊓ (P ⊓ centralizer ({b} : Set G)) = centerIn P := by
  let f := markedHom F P e
  let x := e.symm ⟨a,haP⟩
  let y := e.symm ⟨b,hbP⟩
  have hx : f x=a := congrArg Subtype.val (e.apply_symm_apply _)
  have hy : f y=b := congrArg Subtype.val (e.apply_symm_apply _)
  have hx2 : x^2=1 := markedHom_injective F P e (by rw [map_pow,hx,ha,map_one])
  have hy2 : y^2=1 := markedHom_injective F P e (by rw [map_pow,hy,hb,map_one])
  have hxy : ¬ Commute x y := by
    intro hh
    apply hab
    change a*b=b*a
    simpa only [map_mul,hx,hy] using congrArg f hh.eq
  have hh := congrArg (fun Q : Subgroup (U F) => Q.map f)
    (unipotent_noncommuting_centralizers F x y hx2 hy2 hxy)
  rw [map_inf _ _ _ (markedHom_injective F P e),
    map_centralizer F f (markedHom_injective F P e),
    map_centralizer F f (markedHom_injective F P e),
    range_markedHom,hx,hy,←marked_center,←centerIn_eq_map_center] at hh
  exact hh

end Matrix.PSL3.LinearAmbientGeometry
