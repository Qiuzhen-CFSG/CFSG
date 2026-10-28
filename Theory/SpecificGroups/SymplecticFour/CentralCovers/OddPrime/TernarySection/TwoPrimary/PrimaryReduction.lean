module

public import Theory.GroupTheory.PerfectCentralCover
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Reducing a perfect central kernel to its two-primary part

A finite central kernel is abelian. Choose a Sylow two-subgroup and an
odd-order complement by Schur–Zassenhaus, and quotient the whole covering
group by that central complement. The quotient remains perfect and covers
the same base. Its literal kernel is isomorphic to the original Sylow
two-subgroup. Thus any two-divisibility obstruction already occurs in a
perfect cover whose kernel is a two-group.

The theorem below supplies the primary reduction for the actual Sp₄(3)
wreath-product calculation in `TwoPrimary`. It makes no assumption about
the three-primary part of the original kernel.

Source: the covering convention of Aschbacher–Smith I.1.1, printed p.407;
the ternary symplectic application is I.1.4(1), printed p.408, and GLS3 §6.1.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
universe u v

/-- An exclusion for two-group kernels excludes two in every finite perfect central kernel. -/
theorem not_two_dvd_kernel_of_twoGroup_case {G : Type v} [Group G]
    (hcase : ∀ {D : Type u} [Group D] [Finite D]
      (g : PerfectCentralCovering.Cover D G),
      IsPGroup 2 g.toMonoidHom.ker → ¬ 2 ∣ Nat.card g.toMonoidHom.ker)
    {E : Type u} [Group E] [Finite E] (f : PerfectCentralCovering.Cover E G) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  classical
  let K := f.toMonoidHom.ker
  let : CommGroup K := { (inferInstance : Group K) with
    mul_comm x y := Subtype.ext (mem_center_iff.mp (f.ker_le_center y.property) x) }
  let P : Sylow 2 K := Classical.choice inferInstance
  obtain ⟨Q,hQ⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let N : Subgroup E := Q.map K.subtype
  have hNK : N ≤ K := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  have hNc : N ≤ center E := hNK.trans f.ker_le_center
  let : N.Normal := ⟨by
    intro n hn e
    have hc := mem_center_iff.mp (hNc hn) e
    simpa only [hc, mul_inv_cancel_right] using hn⟩
  let q : E →* E ⧸ N := QuotientGroup.mk' N
  let g : E ⧸ N →* G := QuotientGroup.lift N f.toMonoidHom hNK
  have hgq (x : E) : g (q x) = f.toMonoidHom x := rfl
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨q x,rfl⟩
  have hgc : g.ker ≤ center (E ⧸ N) := by
    intro y hy
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ K := hy
    apply mem_center_iff.mpr
    intro z
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective N z
    change q w * q x = q x * q w
    rw [← map_mul, ← map_mul, mem_center_iff.mp (f.ker_le_center hx) w]
  let : Group.IsPerfect E := f.isPerfect
  let cover : PerfectCentralCovering.Cover (E ⧸ N) G := {
    toMonoidHom := g
    surjective := hg
    ker_le_center := hgc
    isPerfect := inferInstance }
  let r : K →* g.ker := (q.comp K.subtype).codRestrict g.ker (fun x => by
    change g (q x) = 1
    exact x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective N y.val
    have hxK : x ∈ K := by
      change f.toMonoidHom x = 1
      rw [← hgq,hx]
      exact y.property
    exact ⟨⟨x,hxK⟩,Subtype.ext hx⟩
  have hrk : r.ker = Q := by
    ext x
    change (⟨q x, _⟩ : g.ker) = 1 ↔ x ∈ Q
    rw [Subtype.ext_iff]
    change (x : E) ∈ (QuotientGroup.mk' N).ker ↔ x ∈ Q
    rw [QuotientGroup.ker_mk']
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact (Subtype.ext hxy : y = x) ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  let e : K ⧸ Q ≃* g.ker :=
    (QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  have hp : IsPGroup 2 g.ker :=
    P.isPGroup'.of_equiv (hQ.QuotientMulEquiv.symm.trans e)
  have hcard : Nat.card g.ker = Nat.card P :=
    (Nat.card_congr (hQ.QuotientMulEquiv.symm.trans e).toEquiv).symm
  intro hd
  have hdp := P.dvd_card_of_dvd_card hd
  rw [← hcard] at hdp
  exact hcase cover hp hdp

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary
