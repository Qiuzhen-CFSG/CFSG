module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerResidual
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups

/-!
# The original linear-three point-centralizer residual

The opposite component's point stabilizer contains its entire two-core,
which centralizes the original full module. When the point is not fixed
by L₀, that stabilizer has proper image in the actual SL₃(2) quotient and
is solvable. The normal perfect factor L is therefore exactly the
solvable residual of C_{L₀}(v).

Source: Aschbacher--Smith 10.2.10, printed p.753. This adapts the existing
A₅ residual proof using solvability for the literal binary linear model.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- In the original linear-three pair, a full-module vector fixed by the first block
but moved by the pair has exactly that first block as its point-centralizer
solvable residual. -/
theorem point_centralizer_residual
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hvL : v ∈ centralizer (L : Set G))
    (hvnot : v ∉ centralizer (localOrbit T L : Set G)) :
    (solvableResidual (localOrbit T L ⊓ centralizer ({v} : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer ({v} : Set G)).subtype = L := by
  let X := localOrbit T L
  let C := centralizer ({v} : Set G)
  obtain ⟨t,ht,_,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let a := MulAut.conj t
  let B := L.map a.toMonoidHom
  have hpair' : X = L ⊔ B := hpair
  have hLX : L ≤ X := hpair' ▸ le_sup_left
  have hBX : B ≤ X := hpair' ▸ le_sup_right
  have hXL : X ≤ normalizer (L : Set G) := source_nonnormal_orbit_le_normalizer D hn
  have hXmap : X.map a.toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_componentOrbit L T) ht)
  have hXB : X ≤ normalizer (B : Set G) := by
    rw [←hXmap]
    exact (map_mono hXL).trans (L.le_normalizer_map a.toMonoidHom)
  have hLC : L ≤ C := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hBnot : ¬ B ≤ C := by
    intro hBC
    apply hvnot
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((hpair' ▸ sup_le hLC hBC) hx)
  have hcore : B.pCoreIn 2 ≤ C := by
    intro b hb
    have hc := source_fullModule_orbit_core_centralizes D
      (pCoreIn_mono_of_normalizes hBX hXB hb)
    exact mem_centralizer_singleton_iff.mpr (hc v hv).symm
  let N := B ⊓ C
  let K := N.subgroupOf B
  have hKne : K ≠ ⊤ := by
    intro he
    apply hBnot
    intro b hb
    have hh : (⟨b,hb⟩ : B) ∈ K := he ▸ mem_top _
    exact hh.2
  have hcoreK : pCore 2 B ≤ K := by
    intro b hb
    exact ⟨b.property,hcore (mem_map_of_mem B.subtype hb)⟩
  let eb : B ≃* L := (a.subgroupMap L).symm
  let eq : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let : Group.IsSolvable K :=
    Matrix.PSL3Two.isSolvable_proper_subgroup_containing_twoCore (eq.trans e) K hKne hcoreK
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show N ≤ B from inf_le_left)).surjective
  have hsplit : X ⊓ C = L ⊔ N := by
    apply le_antisymm
    · intro x hx
      have hp : x ∈ (L : Set G) * (B : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right L B (hLX.trans hXB),←hpair']
        exact hx.1
      obtain ⟨l,hl,b,hb,rfl⟩ := hp
      have hbc : b ∈ C := by
        simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem (hLC hl)) hx.2
      exact mul_mem_sup hl ⟨hb,hbc⟩
    · exact sup_le (le_inf hLX hLC) (le_inf (inf_le_left.trans hBX) inf_le_right)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  rw [show localOrbit T L ⊓ centralizer ({v} : Set G) = L ⊔ N from hsplit]
  exact map_solvableResidual_sup_eq_of_perfect_normalized L N (inf_le_left.trans (hBX.trans hXL))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
