module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Orbit

/-!
# The actual normalizer action on A

The actor in the orbit argument is the image of N_G(A) in Aut(A).
The first isomorphism theorem identifies it with the quotient by the
conjugation kernel; `Subgroup.normalizerMonoidHom_ker` identifies that
kernel with C_G(A), taken inside N_G(A). Its orbits are exactly the
ambient conjugates by elements normalizing A.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1200–1201, the contained-A branch of Lemma 16.5.12.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup MulAction

variable {G : Type*} [Group G] (A : Subgroup G)

/-- This is M⁺ = N_G(A)/C_G(A), via the kernel of its actual conjugation action. -/
noncomputable def normalizerQuotientEquivImage :
    ((normalizer (A : Set G)) ⧸ A.normalizerMonoidHom.ker) ≃* normalizerImage A :=
  QuotientGroup.quotientKerEquivRange A.normalizerMonoidHom

/-- Image-action orbits are ambient normalizer conjugacy orbits. -/
theorem normalizerImage_orbit_iff (z x : A) : x ∈ orbit (normalizerImage A) z ↔
    ∃ g ∈ normalizer (A : Set G), MulAut.conj g (z : G) = (x : G) := by
  constructor
  · rintro ⟨⟨a, ha⟩, he⟩
    obtain ⟨g, rfl⟩ := ha
    exact ⟨g, g.property, congrArg Subtype.val he⟩
  · rintro ⟨g, hg, he⟩
    refine ⟨⟨A.normalizerMonoidHom ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩, ?_⟩
    exact Subtype.ext he

/-- The numerical contradiction for the genuine normalizer image.
All three geometric premises must still be proved in the contained-A branch. -/
theorem normalizer_orbit_obstruction [Finite G] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 32) (z : A)
    (hgen : closure (orbit (normalizerImage A) z) = ⊤)
    (hlen : Nat.card (orbit (normalizerImage A) z) = 7 ∨
      Nat.card (orbit (normalizerImage A) z) = 13)
    (hstab : Nat.card (stabilizer (normalizerImage A) z) = 72) : False :=
  no_generating_orbit_with_stabilizer_72 hA z hgen hlen hstab

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary
