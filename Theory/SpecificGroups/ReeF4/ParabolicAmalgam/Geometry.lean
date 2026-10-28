module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.FixedProducts
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.DiagonalTorus
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration

/-!
# Root geometry and local residuals of the Ree parabolics

Coroot realization identifies the split word torus with its odd diagonal
matrix image, which normalizes each split root seed. The fixed-product
argument then separates a parabolic into its fixed seed and fixed torus.
Thus the seed is normal in its parabolic with odd relative index and contains
the embedded prime-to-two residual. Positive normal generation inside the
seed gives the reverse inclusion, since the positive subgroup is a two-group.

The split Bruhat and root-separation calculations identify the intersection
of the two split parabolics with the split Borel. Taking inverse images gives
the exact fixed overlap. Fixed Bruhat separation also identifies the full
normalizer of the fixed positive subgroup with the root Borel.

The final theorems discharge every premise of the retained conditional
reductions, for all parameters including the full binary group ²F₄(2).
All seed normality is relative to its full parabolic.

Source: Aschbacher–Smith F.1.4–5 and F.1.12(I)(5), printed pp.260,263–264
of `refs/quasithin.pdf`. O^{2′} is the residual with odd quotient, distinct
from O₂, O² and the solvable residual.
-/

public section
namespace ReeF4.Parabolics
noncomputable section
open Subgroup LargeLocalSeeds

theorem parabolic_le_seed_normalizer_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m))) :
    parabolic m s ≤ normalizer (seed m s : Set (Model m)) :=
  (comap_mono (sup_le (splitSeed m s).le_normalizer hn)).trans (le_normalizer_comap _)

/-- The seed is normal relative to its full parabolic. -/
theorem seed_normal_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m))) :
    ((seed m s).subgroupOf (parabolic m s)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (seed_le_parabolic m s)).mpr
    (parabolic_le_seed_normalizer_of_splitTorus m s hn)

private theorem relIndex_dvd_card_of_sup_eq {G : Type*} [Group G]
    (N T P : Subgroup G) (hN : N ≤ P) (hT : T ≤ P)
    [(N.subgroupOf P).Normal] (hsup : N ⊔ T = P) :
    N.relIndex P ∣ Nat.card T := by
  have he : N.relIndex P = N.relIndex T := by
    calc
      N.relIndex P = (N.subgroupOf P).relIndex (⊤ : Subgroup P) := (relIndex_top_right _).symm
      _ = (N.subgroupOf P).relIndex (N.subgroupOf P ⊔ T.subgroupOf P) := by
        rw [← subgroupOf_sup hN hT, hsup, subgroupOf_self]
      _ = (N.subgroupOf P).relIndex (T.subgroupOf P) := relIndex_sup_left _ _
      _ = N.relIndex T := relIndex_subgroupOf hT
  rw [he]
  exact relIndex_dvd_card _ _

/-- The seed index divides the order of the fixed torus. -/
theorem seed_relIndex_odd_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m))) :
    Odd ((seed m s).relIndex (parabolic m s)) := by
  let := seed_normal_of_splitTorus m s hn
  exact (fixedTorus_odd_card m hodd).of_dvd_nat
    (relIndex_dvd_card_of_sup_eq (seed m s) (fixedTorus m) (parabolic m s)
      (seed_le_parabolic m s) ((fixedTorus_le_borel m).trans (borel_le_parabolic m s))
      (parabolic_eq_seed_sup_fixedTorus_of_splitTorus m s hn hodd).symm)

/-- An odd torus quotient places the prime-to-two residual inside the seed. -/
theorem localFactor_le_seed_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m))) :
    localFactor m s ≤ seed m s := by
  let := seed_normal_of_splitTorus m s hn
  have hi : Nat.Coprime 2 ((seed m s).subgroupOf (parabolic m s)).index :=
    Nat.coprime_two_left.mpr (seed_relIndex_odd_of_splitTorus m s hn hodd)
  rintro _ ⟨x, hx, rfl⟩
  exact primeToResidual_le ((seed m s).subgroupOf (parabolic m s)) hi hx

/-- Normal generation by the positive two-subgroup gives the reverse residual inclusion. -/
theorem seed_le_localFactor_of_positive_normalClosure (m : ℕ) (s : Side)
    (hgen : normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) = ⊤) :
    seed m s ≤ localFactor m s := by
  let f : seed m s →* parabolic m s := inclusion (seed_le_parabolic m s)
  have hcl : normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) ≤
      (primeToResidual 2 (parabolic m s)).comap f := by
    apply normalClosure_le_normal
    intro x hx
    obtain ⟨n, hn⟩ := unipotent_isPGroup m ⟨x.val, hx⟩
    apply mem_primeToResidual_of_pow (n := n)
    apply Subtype.ext
    exact congrArg (fun y : unipotent m => (y : Model m)) hn
  rw [hgen] at hcl
  intro x hx
  exact ⟨f ⟨x, hx⟩, hcl trivial, rfl⟩

/-- Residual identification from torus geometry and local positive normal generation.
These are explicit root-calculation inputs, not an unconditional source theorem. -/
theorem seed_eq_localFactor_of_splitTorus_and_positive_normalClosure (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m)))
    (hgen : normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) = ⊤) :
    seed m s = localFactor m s :=
  le_antisymm (seed_le_localFactor_of_positive_normalClosure m s hgen)
    (localFactor_le_seed_of_splitTorus m s hn hodd)

/-- A matrix identification of the word torus suffices for Borel normalization. -/
theorem borel_le_unipotent_normalizer_of_le_diagonalTorus (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) :
    borel m ≤ normalizer (unipotent m : Set (Model m)) :=
  borel_le_unipotent_normalizer_of_splitTorus m
    (splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m hT)

/-- Fixed parabolic decomposition after identifying the coroot matrices. -/
theorem parabolic_eq_seed_sup_borel_of_le_diagonalTorus (m : ℕ) (s : Side)
    (hT : splitTorus m ≤ diagonalTorus m) :
    parabolic m s = seed m s ⊔ borel m :=
  parabolic_eq_seed_sup_borel_of_splitTorus m s
    (splitTorus_le_seed_normalizer_of_le_diagonalTorus m s hT)
    (splitTorus_odd_card_of_le_diagonalTorus m hT)

/-- Final residual reduction with the concrete diagonal-torus comparison. -/
theorem seed_eq_localFactor_of_diagonalTorus_and_positive_normalClosure (m : ℕ) (s : Side)
    (hT : splitTorus m ≤ diagonalTorus m)
    (hgen : normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) = ⊤) :
    seed m s = localFactor m s :=
  seed_eq_localFactor_of_splitTorus_and_positive_normalClosure m s
    (splitTorus_le_seed_normalizer_of_le_diagonalTorus m s hT)
    (splitTorus_odd_card_of_le_diagonalTorus m hT) hgen

/-- The coroot-word torus has odd order for every Ree parameter. -/
theorem splitTorus_odd_card (m : ℕ) : Odd (Nat.card (splitTorus m)) :=
  splitTorus_odd_card_of_le_diagonalTorus m (splitTorus_eq_diagonalTorus m).le

/-- Coroot realization gives the split positive subgroup's torus action. -/
theorem splitTorus_le_unipotent_normalizer (m : ℕ) :
    splitTorus m ≤ normalizer (splitUnipotent m : Set (SplitGroup m)) :=
  splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m
    (splitTorus_eq_diagonalTorus m).le

/-- The actual split torus normalizes each root-generated seed. -/
theorem splitTorus_le_seed_normalizer (m : ℕ) (s : Side) :
    splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)) :=
  splitTorus_le_seed_normalizer_of_le_diagonalTorus m s
    (splitTorus_eq_diagonalTorus m).le

/-- Fixed-product descent retains the whole fixed torus in the parabolic. -/
theorem parabolic_eq_seed_sup_fixedTorus (m : ℕ) (s : Side) :
    parabolic m s = seed m s ⊔ fixedTorus m :=
  parabolic_eq_seed_sup_fixedTorus_of_splitTorus m s
    (splitTorus_le_seed_normalizer m s) (splitTorus_odd_card m)

/-- The full fixed parabolic is generated by its fixed seed and root Borel. -/
theorem parabolic_eq_seed_sup_borel (m : ℕ) (s : Side) :
    parabolic m s = seed m s ⊔ borel m :=
  parabolic_eq_seed_sup_borel_of_le_diagonalTorus m s
    (splitTorus_eq_diagonalTorus m).le

/-- The root Borel decomposes into its fixed positive subgroup and fixed torus. -/
theorem borel_eq_unipotent_sup_fixedTorus (m : ℕ) :
    borel m = unipotent m ⊔ fixedTorus m :=
  borel_eq_unipotent_sup_fixedTorus_of_splitTorus m
    (splitTorus_le_unipotent_normalizer m) (splitTorus_odd_card m)

/-- Normality of the fixed seed is relative to the full parabolic. -/
theorem seed_normal (m : ℕ) (s : Side) :
    ((seed m s).subgroupOf (parabolic m s)).Normal :=
  seed_normal_of_splitTorus m s (splitTorus_le_seed_normalizer m s)

/-- The fixed seed has odd relative index in its full parabolic. -/
theorem seed_relIndex_odd (m : ℕ) (s : Side) :
    Odd ((seed m s).relIndex (parabolic m s)) :=
  seed_relIndex_odd_of_splitTorus m s
    (splitTorus_le_seed_normalizer m s) (splitTorus_odd_card m)

/-- Each fixed seed is exactly the embedded O^{2′} of its full parabolic,
including at the full binary endpoint. -/
theorem seed_eq_localFactor (m : ℕ) (s : Side) : seed m s = localFactor m s :=
  seed_eq_localFactor_of_diagonalTorus_and_positive_normalClosure m s
    (splitTorus_eq_diagonalTorus m).le (positive_normalClosure_eq_top m s)

/-- The source local factor and the root Borel generate the full parabolic. -/
theorem parabolic_eq_localFactor_sup_borel (m : ℕ) (s : Side) :
    parabolic m s = localFactor m s ⊔ borel m := by
  rw [parabolic_eq_seed_sup_borel, seed_eq_localFactor]

/-- The two split parabolics meet in the independently defined split Borel. -/
theorem splitParabolic_inf_eq_splitBorel (m : ℕ) :
    splitParabolic m .suzuki ⊓ splitParabolic m .linear = splitBorel m :=
  Overlap.splitParabolic_inf_eq_splitBorel m (splitTorus_eq_diagonalTorus m)

/-- Exact overlap descends to the fixed group by taking inverse images. -/
theorem parabolic_inf_eq_borel (m : ℕ) :
    parabolic m .suzuki ⊓ parabolic m .linear = borel m := by
  change (splitParabolic m .suzuki).comap (toSplitGroup m) ⊓
    (splitParabolic m .linear).comap (toSplitGroup m) =
      (splitBorel m).comap (toSplitGroup m)
  rw [← comap_inf, splitParabolic_inf_eq_splitBorel]

/-- The fixed root Borel normalizes the fixed positive subgroup. -/
theorem borel_le_unipotent_normalizer (m : ℕ) :
    borel m ≤ normalizer (unipotent m : Set (Model m)) :=
  borel_le_unipotent_normalizer_of_le_diagonalTorus m
    (splitTorus_eq_diagonalTorus m).le

/-- The root Borel is the full normalizer of the fixed positive subgroup,
also in the full group ²F₄(2) at m = 0. -/
theorem unipotent_normalizer_eq_borel (m : ℕ) :
    normalizer (unipotent m : Set (Model m)) = borel m :=
  le_antisymm (Overlap.unipotent_normalizer_le_borel m (splitTorus_eq_diagonalTorus m))
    (borel_le_unipotent_normalizer m)

end
end ReeF4.Parabolics
