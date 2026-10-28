module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Basic
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Plane
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# The five-subgroup generates U from the original plane

The B₅-span of V₂ lies in the original elementary group U of order32. Its
fixed subgroup is the central point Z of order2. Orbit counting modulo5 and
Lagrange leave only span orders2 or32, and V₂ already has order4. Thus the
span is U. This supplies the first-parabolic generation step in J.4.5(1)
without introducing a model isomorphism or an irreducibility assumption.

Source: Aschbacher–Smith, J.4.5, printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The unchanged five-subgroup generates U from the original plane. -/
theorem Plane.five_span_plane (B5 : Sylow 5 d.toTypeRuSetup.H) :
    conjugateSpanBy p.group (B5Image B5) = d.toTypeRuSetup.U := by
  let M := conjugateSpanBy p.group (B5Image B5)
  have hpU : p.group ≤ d.toTypeRuSetup.U := p.le_seed.trans (le_conjugateSpan _ _)
  have hMU : M ≤ d.toTypeRuSetup.U := conjugateSpanBy_le hpU
    ((map_subtype_le _).trans d.ru2.natural.normalized)
  have hZM : d.toTypeRuSetup.Z ≤ M := p.point_le.trans (le_conjugateSpanBy _ _)
  have hfix : (M ⊓ centralizer (B5Image B5 : Set G) : Subgroup G) = d.toTypeRuSetup.Z := by
    apply le_antisymm
    · intro x hx
      have hm : x ∈ CQ B5 ⊓ d.toTypeRuSetup.U :=
        ⟨⟨d.ru2.six.kernel_le (hMU hx.1),hx.2⟩,hMU hx.1⟩
      rwa [five_centralizer_inf_U] at hm
    · intro z hz
      exact ⟨hZM hz,((five_centralizer_inf_U B5).symm ▸ hz).1.2⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hm := card_modEq_card_inf_centralizer (B5Image B5) M
    (B5.isPGroup'.map d.toTypeRuSetup.H.subtype) (le_normalizer_conjugateSpanBy _ _)
  rw [hfix,d.card_Z] at hm
  have hd : Nat.card M ∣ 32 := by
    rw [← d.ru2.card_U d.card_Z]
    exact card_dvd_of_le hMU
  have hlow : 4 ≤ Nat.card M := by
    rw [← p.card]
    exact card_le_of_le (le_conjugateSpanBy _ _)
  have hmem := Nat.mem_divisors.mpr ⟨hd,(by decide : 32 ≠ 0)⟩
  have he : (32:ℕ).divisors = {1,2,4,8,16,32} := by decide
  rw [he] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  have hc : Nat.card M = 32 := by
    change Nat.card M % 5 = 2 % 5 at hm
    omega
  apply eq_of_le_of_card_ge hMU
  rw [d.ru2.card_U d.card_Z,hc]

/-- Any overgroup containing B₅ and normalizing a subgroup containing V₂
also normalizes enough conjugates to contain the whole original U. -/
theorem Plane.U_le_of_five_normalized
    (B5 : Sylow 5 d.toTypeRuSetup.H) (N : Subgroup G)
    (hp : p.group ≤ N) (hB : B5Image B5 ≤ normalizer (N : Set G)) :
    d.toTypeRuSetup.U ≤ N := by
  rw [← p.five_span_plane B5]
  exact conjugateSpanBy_le hp hB

end CFSG.Quasithin.ChapterJ.RuSubgroup
