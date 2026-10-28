module

public import Theory.GroupAction.FiveFourSixteenOrbitCensus
public import Theory.GroupTheory.SpecificGroups.FiveFourPermutation

/-!
# The complementary ten-point orbit in a faithful S₅ action on sixteen

Restrict to the natural affine subgroup C₅:C₄. Its proved orbit census is
1+5+10. Thus an invariant five-element subset avoiding the identity is its
five-orbit, and its nonidentity complement is a single S₅-orbit of size ten.

Source application: Aschbacher--Smith F.5.4(3--4), printed p.301.
-/

public noncomputable section
namespace Theory.GroupAction
open MulAction

/-- An invariant five-set determines the other nonidentity orbit. -/
theorem symmetric_five_sixteen_complement_orbit
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (f : Equiv.Perm (Fin 5) →* MulAut V)
    (hf : Function.Injective f) (S : Set V) (hS : S.ncard = 5) (h1 : 1 ∉ S)
    (hinv : ∀ g x, x ∈ S → f g x ∈ S)
    (w : V) (hw1 : w ≠ 1) (hwS : w ∉ S) :
    (Set.range (fun g => f g w)).ncard = 10 := by
  let a := f.comp FiveFour.permutationHom
  have ha : Function.Injective a := hf.comp FiveFour.permutationHom_injective
  let : MulDistribMulAction (Equiv.Perm (Fin 5)) V := MulDistribMulAction.compHom V f
  let : MulDistribMulAction FiveFour.Group V := MulDistribMulAction.compHom V a
  obtain ⟨x,y,hx1,hy1,hx5,hy10,hcover⟩ := five_four_sixteen_orbit_census hV
    FiveFour.action FiveFour.action_injective a ha
  change (orbit FiveFour.Group x).ncard = 5 at hx5
  change (orbit FiveFour.Group y).ncard = 10 at hy10
  change ∀ v : V, v ≠ 1 → v ∈ orbit FiveFour.Group x ∪ orbit FiveFour.Group y at hcover
  have hstable (g : FiveFour.Group) (v : V) : g • v ∈ S ↔ v ∈ S := by
    constructor
    · intro hv
      have hh := hinv (FiveFour.permutationHom g⁻¹) (g • v) hv
      change g⁻¹ • (g • v) ∈ S at hh
      simpa only [inv_smul_smul] using hh
    · exact hinv (FiveFour.permutationHom g) v
  have hsub (v : V) (hv : v ∈ S) : orbit FiveFour.Group v ⊆ S := by
    rintro _ ⟨g,rfl⟩
    exact (hstable g v).mpr hv
  have hyS : y ∉ S := by
    intro hy
    have hh := Set.ncard_le_ncard (hsub y hy)
    rw [hy10,hS] at hh
    omega
  obtain ⟨r,hr⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hS]; decide)
  have hr1 : r ≠ 1 := by rintro rfl; exact h1 hr
  have hxS : x ∈ S := by
    rcases hcover r hr1 with ⟨g,hg⟩ | ⟨g,hg⟩
    · apply (hstable g x).mp
      change a g x ∈ S
      have he : a g x = r := hg
      rw [he]
      exact hr
    · apply (hyS ((hstable g y).mp ?_)).elim
      change a g y ∈ S
      have he : a g y = r := hg
      rw [he]
      exact hr
  have hwy : w ∈ orbit FiveFour.Group y := by
    rcases hcover w hw1 with h | h
    · exact (hwS (hsub x hxS h)).elim
    · exact h
  have hten : (orbit FiveFour.Group w).ncard = 10 := by
    rw [orbit_eq_iff.mpr hwy,hy10]
  have hsmall : orbit FiveFour.Group w ⊆ orbit (Equiv.Perm (Fin 5)) w := by
    rintro _ ⟨g,rfl⟩
    exact ⟨FiveFour.permutationHom g,rfl⟩
  have hlarge : orbit (Equiv.Perm (Fin 5)) w ⊆ (insert 1 S)ᶜ := by
    rintro _ ⟨g,rfl⟩ (he | hs)
    · apply hw1
      have hh := congrArg (fun v : V => g⁻¹ • v) he
      simpa only [inv_smul_smul,smul_one] using hh
    · apply hwS
      have hh := hinv g⁻¹ (g • w) hs
      change g⁻¹ • (g • w) ∈ S at hh
      simpa only [inv_smul_smul] using hh
  have hc : ((insert 1 S)ᶜ).ncard = 10 := by
    rw [Set.ncard_compl,Set.ncard_insert_of_notMem h1,hS,hV]
  have hlo := Set.ncard_le_ncard hsmall
  have hhi := Set.ncard_le_ncard hlarge
  change (orbit (Equiv.Perm (Fin 5)) w).ncard = 10
  rw [hten] at hlo
  rw [hc] at hhi
  omega

end Theory.GroupAction
