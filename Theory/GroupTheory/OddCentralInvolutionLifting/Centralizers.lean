module

public import Theory.GroupTheory.OddCentralInvolutionLifting

/-!
# Involution centralizers in odd central extensions

The unique square-one lift of an involution is fixed by every conjugation
whose image fixes that involution. Thus its centralizer is exactly the
preimage of the quotient centralizer. The chosen lift retains its exact
image and square equations; no splitting or finiteness of the ambient
group is required. A map killing the center also detects properness of
the centralizer from a nonidentity image.

This is the elementary odd-central-extension step used in
Aschbacher–Smith A.2.19, after A.2.13's central-primary reduction.
-/

@[expose] public section

noncomputable section
namespace OddCentralLifting
variable {G H : Type*} [Group G] [Group H]

def involutionLift (q : G →* H) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) (t : H) (ht : t ^ 2 = 1) : G :=
  Classical.choose (exists_involution_lift q hodd hq t ht)

theorem involutionLift_image (q : G →* H) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) (t : H) (ht : t ^ 2 = 1) :
    q (involutionLift q hq hodd t ht) = t :=
  (Classical.choose_spec (exists_involution_lift q hodd hq t ht)).1

theorem involutionLift_square (q : G →* H) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) (t : H) (ht : t ^ 2 = 1) :
    involutionLift q hq hodd t ht ^ 2 = 1 :=
  (Classical.choose_spec (exists_involution_lift q hodd hq t ht)).2

theorem centralizes_of_image (q : G →* H) (hodd : Odd (Nat.card q.ker))
    (hcentral : q.ker ≤ Subgroup.center G) {t x : G} (ht : t ^ 2 = 1)
    (hx : q x * q t = q t * q x) : x * t = t * x := by
  have he : x * t * x⁻¹ = t := by
    apply involution_lift_unique q hodd hcentral
    · rw [conj_pow, ht]
      simp
    · exact ht
    · simp only [map_mul, map_inv]
      rw [hx, mul_inv_cancel_right]
  calc
    x * t = (x * t * x⁻¹) * x := by simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = t * x := congrArg (fun z => z * x) he

theorem centralizer_eq_comap (q : G →* H) (hodd : Odd (Nat.card q.ker))
    (hcentral : q.ker ≤ Subgroup.center G) {t : G} (ht : t ^ 2 = 1) :
    Subgroup.centralizer ({t} : Set G) =
      (Subgroup.centralizer ({q t} : Set H)).comap q := by
  ext x
  change x ∈ Subgroup.centralizer ({t} : Set G) ↔
    q x ∈ Subgroup.centralizer ({q t} : Set H)
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun hx => by simpa only [map_mul] using congrArg q hx,
    centralizes_of_image q hodd hcentral ht⟩

/-- An element with nonidentity image is noncentral if the map kills the center. -/
theorem centralizer_ne_top_of_image (q : G →* H)
    (hcenter : Subgroup.center G ≤ q.ker) {t : G} (ht : q t ≠ 1) :
    Subgroup.centralizer ({t} : Set G) ≠ ⊤ := by
  intro he
  apply ht
  apply hcenter
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Subgroup.mem_centralizer_singleton_iff.mp (he ▸ Subgroup.mem_top x)

end OddCentralLifting
