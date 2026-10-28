module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import Theory.GroupTheory.PResidual.PrimeSetFiniteImage

/-!
# The offender families and residuals in 15.2.9--14

Minimality in Delta is minimality of the image in the actual two-core
quotient, not minimality of the elementary subgroup itself. Sigma outside
the fixed Sylow group is the difference of the two image families, as in
the source; it is not defined as the image of the difference of their domains.

The embedded K is O²(H), Kc is its Mc-orbit span, and O^{3'} uses the
prime-set residual for quotients of order prime to three. None of these
definitions asserts existence of a distinguished plane or a model recognition.

Source: Aschbacher--Smith, Notation 15.2.9 and Lemma 15.2.12,
printed pp.1110--1111, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Stellmacher

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

open ChapterD

variable {G : Type*} [Group G]

/-- The literal image A* in H/O₂(H). -/
noncomputable def offenderImage (H A : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- Delta from 15.2.9: nontrivial quotient images minimal under inclusion. -/
noncomputable def delta (H : Subgroup G) : Set (Subgroup G) :=
  {A | A ∈ elementaryAbelianMaxSubgroups H ∧ ¬ A ≤ twoCoreIn H ∧
    ∀ A' ∈ elementaryAbelianMaxSubgroups H, ¬ A' ≤ twoCoreIn H →
      offenderImage H A' ≤ offenderImage H A → offenderImage H A ≤ offenderImage H A'}

/-- Sigma consists of the actual intersections B(A)=A∩O₂(H). -/
noncomputable def sigma (H : Subgroup G) : Set (Subgroup G) :=
  (fun A => A ⊓ twoCoreIn H) '' delta H

/-- Sigma(V), with T=N_H(V) in the source application. -/
noncomputable def sigmaAt (T H : Subgroup G) : Set (Subgroup G) :=
  (fun A => A ⊓ twoCoreIn H) '' {A ∈ delta H | A ≤ T}

/-- The set difference Sigma minus Sigma(V), exactly as printed. -/
noncomputable def sigmaOutside (T H : Subgroup G) : Set (Subgroup G) :=
  sigma H \ sigmaAt T H

/-- The embedded two-residual, not the two-core. -/
noncomputable def residual (H : Subgroup G) : Subgroup G :=
  (pResidual 2 H).map H.subtype

/-- Kc is the orbit span of the literal K inside Mc. -/
noncomputable def partnerSpan (H Mc : Subgroup G) : Subgroup G :=
  conjugateSpanBy (residual H) Mc

/-- O^{3'}(Mc): the smallest normal subgroup with a 3'-group quotient. -/
noncomputable def threePrimeResidual (Mc : Subgroup G) : Subgroup G :=
  (piResidual {p : Nat.Primes | p.val ≠ 3} Mc).map Mc.subtype

/-- S is always the centralizer of the distinguished plane in the fixed T. -/
def planeCentralizer (T : Sylow 2 G) (ZS : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer (ZS : Set G)

/-- Membership in Sigma outside T supplies an actual offender outside T.
The converse requires excluding all other preimages in T. -/
theorem exists_offender_of_mem_sigmaOutside {T H B : Subgroup G}
    (hB : B ∈ sigmaOutside T H) :
    ∃ A ∈ delta H, ¬ A ≤ T ∧ B = A ⊓ twoCoreIn H := by
  obtain ⟨A, hA, rfl⟩ := hB.1
  refine ⟨A, hA, ?_, rfl⟩
  intro hAT
  exact hB.2 ⟨A, ⟨hA, hAT⟩, rfl⟩

/-- The prime-complement residual has the source quotient convention. -/
theorem threePrimeResidual_quotient [Finite G] (Mc : Subgroup G) :
    IsPiGroup {p : Nat.Primes | p.val ≠ 3}
      (Mc ⧸ piResidual {p : Nat.Primes | p.val ≠ 3} Mc) :=
  isPiGroup_quotient_piResidual _

/-- The embedded prime-complement residual is monotone under subgroup inclusion. -/
theorem threePrimeResidual_mono [Finite G] {A B : Subgroup G} (hAB : A ≤ B) :
    threePrimeResidual A ≤ threePrimeResidual B := by
  have hm := map_mono (f := B.subtype)
    (map_piResidual_le {p : Nat.Primes | p.val ≠ 3} (inclusion hAB))
  simpa only [threePrimeResidual, map_map, subtype_comp_inclusion] using hm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
