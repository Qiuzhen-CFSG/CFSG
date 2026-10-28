module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Initial
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PCoreKernelRange

/-!
# The exact starred image of L₁ in 13.5.15

The restriction of H→H/O₂(H) to the original L₁ has kernel O₂(L₁)
when L₁ is normal inside H. Its range is the literal starred image,
so the first isomorphism theorem identifies L₁* with L₁/O₂(L₁)
and proves O₂(L₁*)=1. The further cyclic-order-three calculation is
not assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
first paragraph of the proof of 13.5.15, printed p.920 (PDF p.937).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

noncomputable def localStarMap (h : D.Hypothesis) : D.L₁ →* Section08.Source.Hstar D.H :=
  (QuotientGroup.mk' (pCore 2 D.H)).comp
    (inclusion (le_sup_left.trans h.local_le))

theorem localStarMap_range (h : D.Hypothesis) :
    (localStarMap h).range = Section08.Source.starImage D.H D.L₁ := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion (le_sup_left.trans h.local_le) a, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- This equality is for the restriction of the original quotient map. -/
theorem localStarMap_kernel (h : D.Hypothesis)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    (localStarMap h).ker = pCore 2 D.L₁ := by
  ext x
  let xH : D.H := inclusion (le_sup_left.trans h.local_le) x
  change xH ∈ (QuotientGroup.mk' (pCore 2 D.H)).ker ↔ x ∈ pCore 2 D.L₁
  rw [QuotientGroup.ker_mk']
  constructor
  · intro hx
    have hxQ : (x : G) ∈ D.QH := ⟨xH, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := (local_core_intersection h hn).le ⟨x.property, hxQ⟩
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hxQ := ((local_core_intersection h hn).ge
      (mem_map_of_mem D.L₁.subtype hx)).2
    obtain ⟨y, hy, he⟩ := hxQ
    exact (show y = xH from Subtype.ext he) ▸ hy

/-- The first-isomorphism equivalence retains the literal starred image. -/
noncomputable def localStarEquiv (h : D.Hypothesis)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    (D.L₁ ⧸ pCore 2 D.L₁) ≃* Section08.Source.starImage D.H D.L₁ :=
  (QuotientGroup.quotientMulEquivOfEq (localStarMap_kernel h hn).symm).trans
    ((QuotientGroup.quotientKerEquivRange (localStarMap h)).trans
      (MulEquiv.subgroupCongr (localStarMap_range h)))

/-- The first assertion of the proof of 13.5.15, for the actual quotient image. -/
theorem localStar_core_eq_bot (h : D.Hypothesis)
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    pCore 2 (Section08.Source.starImage D.H D.L₁) = ⊥ := by
  rw [← localStarMap_range h]
  exact pCore_range_eq_bot_of_ker_eq_pCore 2 (localStarMap h) (localStarMap_kernel h hn)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
