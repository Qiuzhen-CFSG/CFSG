module

public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage

/-!
# An actual outer Sylow actor in the linear-three source

The source Sylow alignment supplies an element moving the two parabolic
types. Inner automorphisms preserve each type, so this element acts outerly
on the normal component. In the original maximal-core quotient, lift the
element through the prescribed Sylow image and retain its literal
conjugation formula. No outer actor or model-module marking is a premise.

Source: Aschbacher--Smith, E.2.2(2b), printed pp.215--216, and the
linear-three branch of E.2.17, printed p.230.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.ChapterE.Structure.LinearThree
variable {H : Type*} [Group H] [Finite H]

/-- A genuine element of the prescribed Sylow acts noninnerly on the component. -/
theorem exists_outer_sylow_actor
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (K : Subgroup H) [K.Normal] (e : K ≃* PSL(3,F)) (T : Sylow 2 H)
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) :
    ∃ t ∈ (T : Subgroup H),
      (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K := by
  obtain ⟨g, _, ⟨t, ht, ha⟩, _⟩ :=
    exists_diagram_and_borel F hn hF K e T hgen hP
  refine ⟨t, ht, ?_⟩
  intro hi
  let e' := e.trans (MulAut.conj g)
  have hi' : modelAction F K e' t ∈ MulAut.innerSubgroup PSL(3,F) := by
    rw [← MulAut.map_innerSubgroup_congr e']
    exact mem_map_of_mem (MulAut.congr e').toMonoidHom hi
  have hd : modelAction F K e' t ∈ diagramTrivial F := by
    obtain ⟨z, hz⟩ := hi'
    rw [← hz]
    exact (mem_diagramTrivial F _).mpr (fun b => ⟨z, rfl⟩)
  have hk : modelAction F K e' t ∈ (diagramAction F hn hF).ker := by
    rwa [diagramAction_ker]
  exact ha hk

/-- The original E.2.2 quotient has an outer actor lifted from the original T,
with its actual conjugation action on the original component image. -/
theorem source_outer_sylow_actor
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ n)) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    let D := K.map q
    ∃ (t : T) (α : MulAut D), α ∉ MulAut.innerSubgroup D ∧
      ∀ d : D, (α d : H ⧸ ChapterB.minimalParabolicCore T hP) =
        q (t : H) * (d : H ⧸ ChapterB.minimalParabolicCore T hP) * (q (t : H))⁻¹ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let D := K.map q
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  obtain ⟨t, ht, ho⟩ := exists_outer_sylow_actor F hn hcard D e S hi.2.2.2 hmin
  obtain ⟨u, hu, rfl⟩ := ht
  exact ⟨⟨u, hu⟩, MulAut.conjNormal (q u), ho, fun d => rfl⟩

end CFSG.Quasithin.ChapterE.Structure.LinearThree
