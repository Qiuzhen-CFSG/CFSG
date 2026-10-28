module

public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.PerfectCentralCoverLocalBound

/-!
# Reduction of Suzuki covering kernels to the root group

For the actual Suzuki matrix group over `GF(2^(2*m+1))`, simplicity and
nonsolvability give perfectness and quasisimplicity when `m > 0`. The free
central construction supplies a finite universal covering, with its genuine
unique lifting property in every target universe.

Cyclic odd Sylow subgroups exclude every odd prime from the kernel of any
finite perfect central covering. Transfer then puts the entire kernel in the
derived subgroup of the full preimage of the standard root group, and hence
in any subgroup mapping onto that root group. This reduces multiplier upper
bounds to local lifts. It does not assert an exceptional order or a splitting.

Sources: Aschbacher–Smith I.1.1–I.1.3, printed p.407 (PDF p.418) of
`refs/quasithin.pdf`; Huppert–Blackburn III, XI.3.6 and XI.3.10–12 for the
matrix model and odd Sylow structure. The two-primary calculations remain
separate from this reduction.
-/

@[expose] public noncomputable section
universe u

open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.SchurCover

/-- The nondegenerate matrix Suzuki group is perfect. -/
theorem isPerfect (m : ℕ) (hm : 0 < m) : Group.IsPerfect (SuzukiMatrixGroup m) := by
  let := (External.huppert_blackburn_XI_3_6 m hm).1
  constructor
  rcases (inferInstance : (commutator (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top
      with h | h
  · exact False.elim (External.suzukiMatrixGroup_not_isSolvable m hm
      ⟨⟨1, (derivedSeries_one _).trans h⟩⟩)
  · exact h

/-- Simplicity on the exact source parameter range. -/
instance base_isSimple (m : ℕ) [hm : Fact (0 < m)] :
    IsSimpleGroup (SuzukiMatrixGroup m) := (External.huppert_blackburn_XI_3_6 m hm.out).1

/-- The matrix group meets the quasisimple covering API. -/
instance base_isQuasisimple (m : ℕ) [hm : Fact (0 < m)] :
    IsQuasisimple (SuzukiMatrixGroup m) := by
  let := isPerfect m hm.out
  have hz : center (SuzukiMatrixGroup m) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

/-- The derived subgroup of the canonical free central extension. -/
abbrev CoverGroup (m : ℕ) := PerfectCentralCovering.UniversalGroup (SuzukiMatrixGroup m)

/-- The actual projection of the finite universal covering group. -/
def cover (m : ℕ) [Fact (0 < m)] : Covering (CoverGroup m) (SuzukiMatrixGroup m) :=
  PerfectCentralCovering.universalQuasisimpleCover _

/-- Unique lifting to covers in every target universe. -/
theorem cover_isUniversal (m : ℕ) [Fact (0 < m)] :
    Covering.IsUniversal.{0,0,u} (cover m) :=
  PerfectCentralCovering.universalQuasisimpleCover_isUniversal _

/-- The kernel of the literal universal projection. -/
abbrev Kernel (m : ℕ) := (PerfectCentralCovering.universalProjection
  (SuzukiMatrixGroup m)).ker

/-- Odd cyclic Sylow transfer eliminates the entire odd part of every kernel. -/
theorem kernel_isTwoGroup {E : Type*} [Group E] [Finite E] {m : ℕ}
    (hm : 0 < m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra hn
    let : Fact p.Prime := ⟨hpp⟩
    exact f.not_dvd_card_multiplier_of_isCyclic_sylow
      (suzukiSylow_isCyclic_of_ne_two hm hn) hpd
  norm_num [heq]

/-- Apply the prime exclusion to the constructed universal cover. -/
theorem universalKernel_isTwoGroup (m : ℕ) [hm : Fact (0 < m)] :
    IsPGroup 2 (Kernel m) := kernel_isTwoGroup hm.out
      (PerfectCentralCovering.universalCover (SuzukiMatrixGroup m))

/-- The standard root group has index prime to two. -/
theorem root_index_odd (m : ℕ) (hm : 0 < m) :
    ¬ 2 ∣ (SuzukiRootSubgroup m).index := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  rw [← hP]
  exact P.not_dvd_index

/-- Transfer places the whole kernel in the derived group of the root preimage. -/
theorem kernel_le_rootPreimage_commutator {E : Type*} [Group E] [Finite E] {m : ℕ}
    (hm : 0 < m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m)) :
    f.toMonoidHom.ker ≤ ⁅(SuzukiRootSubgroup m).comap f.toMonoidHom,
      (SuzukiRootSubgroup m).comap f.toMonoidHom⁆ := by
  let := f.isPerfect
  apply central_pSubgroup_le_commutator _ _ ((SuzukiRootSubgroup m).ker_le_comap _)
    f.ker_le_center (kernel_isTwoGroup hm f)
  rw [(SuzukiRootSubgroup m).index_comap_of_surjective f.surjective]
  exact root_index_odd m hm

/-- Every lift onto the root subgroup contains the global kernel. -/
theorem kernel_le_rootLift {E : Type*} [Group E] [Finite E] {m : ℕ}
    (hm : 0 < m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (H : Subgroup E) (hH : H.map f.toMonoidHom = SuzukiRootSubgroup m) :
    f.toMonoidHom.ker ≤ H :=
  (kernel_le_rootPreimage_commutator hm f).trans
    (PerfectCentralCovering.commutator_preimage_le_of_map_eq
      f.toMonoidHom f.ker_le_center H _ hH)

/-- A bound for a literal local lift bounds the full covering kernel. -/
theorem kernel_card_le_rootLift {E : Type*} [Group E] [Finite E] {m : ℕ}
    (hm : 0 < m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (H : Subgroup E) (hH : H.map f.toMonoidHom = SuzukiRootSubgroup m) :
    Nat.card f.toMonoidHom.ker ≤ Nat.card (H ⊓ f.toMonoidHom.ker : Subgroup E) := by
  rw [inf_eq_right.mpr (kernel_le_rootLift hm f H hH)]

/-- A section over the literal standard root group kills the full kernel,
since transfer places that kernel in the image of the section. -/
theorem kernel_eq_bot_of_rootSection {E : Type*} [Group E] [Finite E] {m : ℕ}
    (hm : 0 < m) (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup m))
    (s : SuzukiRootSubgroup m →* E)
    (hs : f.toMonoidHom.comp s = (SuzukiRootSubgroup m).subtype) :
    f.toMonoidHom.ker = ⊥ := by
  have hH : s.range.map f.toMonoidHom = SuzukiRootSubgroup m := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      have hy : f.toMonoidHom (s y) = (y : SuzukiMatrixGroup m) :=
        DFunLike.congr_fun hs y
      rw [hy]
      exact y.property
    · intro hx
      exact ⟨s ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, DFunLike.congr_fun hs ⟨x, hx⟩⟩
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := kernel_le_rootLift hm f s.range hH hx
  have hy : (y : SuzukiMatrixGroup m) = 1 := (DFunLike.congr_fun hs y).symm.trans hx
  have hy' : y = 1 := Subtype.ext hy
  simp [hy']

end BenderSuzuki.MatrixGroups.SchurCover

end
