module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.GroupTheory.CoveringKernelCard

/-!
# From central closure to the universal symplectic quotient cover

Lift the canonical universal cover of PSp₄(F) to the actual Sp₄(F) quotient
cover. If every perfect central cover of Sp₄(F) is injective, this lift is an
isomorphism. The commuting triangle identifies the two kernels and proves the
full universal property in every target universe. `CoveringKernelEquiv`
then transports the explicit C₂ calculation to the canonical projection.

The central-closure premise remains explicit. Its prime-field cases are the
missing upper bound in the source multiplier calculation (Aschbacher–Smith
I.1.4, printed p.408; GLS3 §6.1). This module does not assert that premise.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
open Theory.GroupTheory
universe u v w

private theorem injective_of_section {E : Type u} {G : Type v} [Group E] [Group G]
    (f : PerfectCentralCovering.Cover E G) (s : G →* E)
    (hs : f.toMonoidHom.comp s = MonoidHom.id G) : Function.Injective f.toMonoidHom := by
  let := f.isPerfect
  have hsurj : Function.Surjective s :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f.toMonoidHom s (by rw [hs]; exact Function.surjective_id) f.ker_le_center
  intro x y hxy
  obtain ⟨x, rfl⟩ := hsurj x
  obtain ⟨y, rfl⟩ := hsurj y
  apply congrArg s
  exact (DFunLike.congr_fun hs x).symm.trans (hxy.trans (DFunLike.congr_fun hs y))

variable {F : Type u} [Field F] [Finite F] [Fact (2 < Nat.card F)]

theorem isUniversal_of_perfect_central_covers_injective
    (hclosed : ∀ (E : Type u) [Group E] [Finite E]
      (f : PerfectCentralCovering.Cover E (Sp F)), Function.Injective f.toMonoidHom) :
    Covering.IsUniversal.{u, u, w} (quotientCover F) := by
  let c := PerfectCentralCovering.universalQuasisimpleCover (PSp F)
  have hc : Covering.IsUniversal.{u, u, u} c :=
    PerfectCentralCovering.universalQuasisimpleCover_isUniversal (PSp F)
  let a := hc.lift (quotientCover F)
  have ha := hc.lift_fac (quotientCover F)
  let e : PerfectCentralCovering.UniversalGroup (PSp F) ≃* Sp F :=
    MulEquiv.ofBijective a.toMonoidHom
      ⟨hclosed _ (PerfectCentralCovering.ofCovering a), a.surjective⟩
  let k := Covering.kerMulEquivOfSquare c.toMonoidHom
    (quotientCover F).toMonoidHom e (MulEquiv.refl (PSp F))
    (fun x => congrArg (fun f : Covering _ (PSp F) => f x) ha)
  apply Covering.isUniversal_of_kernel_card_le
  exact le_of_eq (Nat.card_congr k.toEquiv)

def universalKernelEquivC2 (hodd : (2 : F) ≠ 0)
    (hu : Covering.IsUniversal.{u, u, u} (quotientCover F)) :
    (PerfectCentralCovering.universalProjection (PSp F)).ker ≃*
      Multiplicative (ZMod 2) :=
  ((PerfectCentralCovering.universalQuasisimpleCover_isUniversal (PSp F)).kerMulEquiv
    hu (MulEquiv.refl (PSp F))).trans (kernelEquivC2 hodd)



/-- Splitting all perfect central covers of Sp₄(F) gives the universal property
of its literal central quotient map. -/
theorem isUniversal_of_sections
    (hsplit : ∀ (E : Type u) [Group E] [Finite E]
      (f : PerfectCentralCovering.Cover E (Sp F)),
      ∃ s : Sp F →* E, f.toMonoidHom.comp s = MonoidHom.id (Sp F)) :
    Covering.IsUniversal.{u, u, w} (quotientCover F) := by
  apply isUniversal_of_perfect_central_covers_injective
  intro E _ _ f
  obtain ⟨s, hs⟩ := hsplit E f
  exact injective_of_section f s hs

/-- A section theorem over the prime field applies over any field of the same
cardinality via an actual entrywise matrix-group isomorphism. -/
theorem isUniversal_of_prime_field_sections {p : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card F = p)
    (hsplit : ∀ (E : Type u) [Group E] [Finite E]
      (f : PerfectCentralCovering.Cover E (Sp (ZMod p))),
      ∃ s : Sp (ZMod p) →* E, f.toMonoidHom.comp s = MonoidHom.id (Sp (ZMod p))) :
    Covering.IsUniversal.{u, u, w} (quotientCover F) := by
  classical
  let := Fintype.ofFinite F
  let eF : ZMod p ≃+* F := ZMod.ringEquivOfPrime F hp.out
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let e := fieldEquivSp eF
  apply isUniversal_of_sections
  intro E _ _ f
  let f' : PerfectCentralCovering.Cover E (Sp (ZMod p)) := {
    toMonoidHom := e.symm.toMonoidHom.comp f.toMonoidHom
    surjective := e.symm.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      intro x hx
      apply f.ker_le_center
      apply e.symm.injective
      exact (show e.symm (f.toMonoidHom x) = 1 from hx).trans (map_one e.symm).symm }
  obtain ⟨s, hs⟩ := hsplit E f'
  refine ⟨s.comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  apply e.symm.injective
  exact DFunLike.congr_fun hs (e.symm x)

/-- The actual symplectic double cover already proves an unconditional lower
bound for the canonical Schur multiplier, without assuming its universality. -/
theorem two_dvd_universalKernel (hodd : (2 : F) ≠ 0) :
    2 ∣ Nat.card (PerfectCentralCovering.universalProjection (PSp F)).ker := by
  let c := PerfectCentralCovering.universalQuasisimpleCover (PSp F)
  have hc : Covering.IsUniversal.{u, u, u} c :=
    PerfectCentralCovering.universalQuasisimpleCover_isUniversal (PSp F)
  let a := hc.lift (quotientCover F)
  have ha := hc.lift_fac (quotientCover F)
  have hd := kernel_card_dvd_of_surjective_factor c.toMonoidHom
    (quotientCover F).toMonoidHom a.toMonoidHom a.surjective
    (congrArg Covering.toMonoidHom ha)
  change Nat.card (quotientCover F).toMonoidHom.ker ∣
    Nat.card (PerfectCentralCovering.universalProjection (PSp F)).ker at hd
  simpa only [quotientCover_ker, card_center hodd] using hd

/-- In particular, omitting the ordinary odd symplectic row cannot mean that
its multiplier is trivial. This conclusion does not use a multiplier table. -/
theorem universalKernel_ne_bot (hodd : (2 : F) ≠ 0) :
    (PerfectCentralCovering.universalProjection (PSp F)).ker ≠ ⊥ := by
  intro h
  have hd := two_dvd_universalKernel hodd
  rw [h, Subgroup.card_bot] at hd
  norm_num at hd

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
