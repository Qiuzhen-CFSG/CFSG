module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.Model
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.TwoPrimary

/-!
# Lifting the SU₃(4) Levi through a central double extension

The natural SU₃(4) projection is injective because its scalar kernel has
order gcd(3,5)=1. The established defining-prime multiplier calculation for
PSU₃(4) therefore excludes two from every perfect central kernel over SU₃(4).
For an arbitrary finite central extension of SU₃(4) with kernel dividing
two, its derived subgroup is perfect and still surjects. Its restricted
projection has trivial kernel and its inverse is the required section.

Pulling back the literal middle-block homomorphism in SU₅ gives the local
Levi lift used in the defining-prime calculation for Aschbacher–Smith
I.1.4(4), printed p.408, citing GLS3 §6.1. No perfectness of the whole
preimage of the Levi is assumed.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory PerfectCentralCovering
open Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections

variable {F : Type*} [Field F] [Finite F]

private theorem not_two_dvd_su3_cover_kernel (K : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, K.conj x = x ^ 4)
    {E : Type*} [Group E] [Finite E] (c : Cover E K.specialSubgroup) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  let π := Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project K
  have hi : Function.Injective π := by
    apply π.ker_eq_bot_iff.mp
    apply Subgroup.eq_bot_of_card_eq
    simpa using Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.card_project_kernel
      K hconj (q := 4) (by simpa using hcard)
  let d : Cover E (ProjectiveSpecialUnitaryMatrixGroup K) :=
    { toMonoidHom := π.comp c.toMonoidHom
      surjective := (Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project_surjective K).comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ hi]
        exact c.ker_le_center }
  have h := HermitianForm.UniversalCover.EvenKernelBound.not_two_dvd_cover_kernel
    K (n := 2) (by decide) (by simpa using hcard) (by simpa using hconj) d
  rwa [show d.toMonoidHom.ker = c.toMonoidHom.ker from
    MonoidHom.ker_comp_of_injective _ _ hi] at h

/-- Every finite central extension of the actual SU₃(4) whose kernel order
divides two splits, even when the extension group is not perfect. -/
theorem exists_su3_section (K : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, K.conj x = x ^ 4)
    {E : Type*} [Group E] [Finite E] (f : E →* K.specialSubgroup)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hk : Nat.card f.ker ∣ 2) :
    ∃ s : K.specialSubgroup →* E, f.comp s = MonoidHom.id _ := by
  let := HermitianForm.UniversalCover.special_isQuasisimple K
    (q := 4) (by decide) (by simpa using hcard) hconj
  let D := commutator E
  let g : D →* K.specialSubgroup := f.comp D.subtype
  have hD : D.map f = ⊤ := by
    change (commutator E).map f = ⊤
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hg : Function.Surjective g := by
    intro b
    have hb : b ∈ D.map f := by rw [hD]; trivial
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨⟨d, hd⟩, hdb⟩
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
  let c : Cover D K.specialSubgroup :=
    { toMonoidHom := g
      surjective := hg
      isPerfect := inferInstance
      ker_le_center := by
        intro x hx
        exact mem_center_iff.mpr fun y =>
          Subtype.ext (mem_center_iff.mp (hc hx) y.val) }
  let k : g.ker →* f.ker :=
    (D.subtype.comp g.ker.subtype).codRestrict f.ker (fun x => x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) h
  have hdiv : Nat.card g.ker ∣ 2 := (card_dvd_of_injective k hki).trans hk
  have hone : Nat.card g.ker = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact h
    · exact (not_two_dvd_su3_cover_kernel K hcard hconj c (h ▸ dvd_rfl)).elim
  let e := MulEquiv.ofBijective g
    ⟨g.ker_eq_bot_iff.mp (Subgroup.eq_bot_of_card_eq _ hone), hg⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, MonoidHom.ext (fun b => ?_)⟩
  exact e.apply_symm_apply b

/-- Every homomorphism from SU₃(4) lifts through a finite central double
cover. This also applies to the coordinate SU₃ blocks containing individual
root factors of the line radical. -/
theorem exists_su3_lift (K : HermitianForm 3 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, K.conj x = x ^ 4)
    {G E : Type*} [Group G] [Group E] [Finite E] (d : Cover E G)
    (hd : Nat.card d.toMonoidHom.ker = 2) :
    ∀ i : K.specialSubgroup →* G,
      ∃ l : K.specialSubgroup →* E, d.toMonoidHom.comp l = i := by
  intro i
  let H : Subgroup (E × K.specialSubgroup) :=
    { carrier := {x | d.toMonoidHom x.1 = i x.2}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change d.toMonoidHom (x.1 * y.1) = i (x.2 * y.2)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change d.toMonoidHom x.1⁻¹ = i x.2⁻¹
        rw [map_inv, map_inv, hx] }
  let p : H →* K.specialSubgroup :=
    (MonoidHom.snd _ _).comp H.subtype
  let a : H →* E := (MonoidHom.fst _ _).comp H.subtype
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨e, he⟩ := d.surjective (i b)
    exact ⟨⟨(e, b), he⟩, rfl⟩
  have hpk (x : p.ker) : d.toMonoidHom (a x.val) = 1 := by
    have h : x.val.val.2 = 1 := x.property
    exact x.val.property.trans (by rw [h, map_one])
  have hc : p.ker ≤ center H := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.mp (d.ker_le_center (hpk ⟨x, hx⟩)) y.val.1
    · have hx' : x.val.2 = 1 := hx
      change y.val.2 * x.val.2 = x.val.2 * y.val.2
      simp [hx']
  let k : p.ker →* d.toMonoidHom.ker :=
    (a.comp p.ker.subtype).codRestrict _ hpk
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : d.toMonoidHom.ker => z.val) h
    · exact (show x.val.val.2 = 1 from x.property).trans
        (show y.val.val.2 = 1 from y.property).symm
  have hk : Nat.card p.ker ∣ 2 := hd ▸ card_dvd_of_injective k hki
  obtain ⟨s, hs⟩ := exists_su3_section K hcard hconj p hp hc hk
  refine ⟨a.comp s, MonoidHom.ext (fun b => ?_)⟩
  exact (s b).property.trans (congrArg i (DFunLike.congr_fun hs b))

/-- The literal middle SU₃ block lifts through every finite central double
cover of SU₅(4). The equation is in SU₅, before projectivization. -/
theorem exists_levi_lift [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    {E : Type*} [Group E] [Finite E] (d : Cover E J.specialSubgroup)
    (hd : Nat.card d.toMonoidHom.ker = 2) :
    ∃ l : (middleForm J).specialSubgroup →* E,
      d.toMonoidHom.comp l = leviSU J hJ :=
  exists_su3_lift (middleForm J) hcard hconj d hd (leviSU J hJ)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections
