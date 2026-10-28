module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Simple subgroups in repeated transitive coordinates

A nonzero minimal invariant subgroup of a repeated module is one copy of
its transitive constituent. A nonzero coordinate projection is surjective
by transitivity; its kernel is invariant and hence trivial by minimality.
The resulting coordinates preserve the literal conjugation action.

Source: the homogeneous-module step in Aschbacher--Smith 10.1.1 and the
irreducible-orbit argument in 10.2.9, printed pp.741 and 752.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G V ι : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {L A B : Subgroup G} {ρ : Representation (ZMod 2) L V}
  {τ : Representation (ZMod 2) L (ι → V)}

/-- A simple nonzero invariant subgroup in repeated transitive coordinates
is identified with one copy by a coordinate projection. -/
theorem single_copy_of_minimal
    (s : BinaryConjugationSection L A ⊥ τ)
    (hτ : ∀ l z i, τ l z i = ρ l (z i))
    (htrans : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ l : L, ρ l x = y)
    (hBA : B ≤ A) (hNB : L ≤ normalizer (B : Set G)) (hB : B ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K ≤ B → L ≤ normalizer (K : Set G) → K = B ∨ K = ⊥) :
    Nonempty (BinaryConjugationSection L B ⊥ ρ) := by
  have hinj : Function.Injective s.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [s.kernel_eq,bot_subgroupOf])
  obtain ⟨w,hw⟩ := ne_bot_iff_exists_ne_one.mp hB
  have hcoord : (s.coordinates (inclusion hBA w)).toAdd ≠ 0 := by
    intro hz
    apply hw
    apply Subtype.ext
    exact congrArg (fun z : A => (z : G))
      (hinj (hz.trans (map_one s.coordinates).symm))
  obtain ⟨i,hi⟩ : ∃ i : ι, (s.coordinates (inclusion hBA w)).toAdd i ≠ 0 := by
    by_contra! hn
    exact hcoord (funext hn)
  let f : B →* Multiplicative V := {
    toFun z := Multiplicative.ofAdd ((s.coordinates (inclusion hBA z)).toAdd i)
    map_one' := by change (s.coordinates (inclusion hBA 1)).toAdd i = 0; rw [map_one,map_one]; rfl
    map_mul' x y := by
      change (s.coordinates (inclusion hBA (x*y))).toAdd i =
        (s.coordinates (inclusion hBA x)).toAdd i + (s.coordinates (inclusion hBA y)).toAdd i
      rw [map_mul,map_mul]
      rfl }
  have hf (l : L) (z : B) :
      (f ⟨(l:G)*z*(l:G)⁻¹,(mem_normalizer_iff.mp (hNB l.property) z).mp z.property⟩).toAdd =
      ρ l (f z).toAdd :=
    (congrFun (s.equivariant l (inclusion hBA z)) i).trans (hτ l _ i)
  have honto : Function.Surjective f := by
    intro z
    by_cases hz : z = 1
    · exact ⟨1,(map_one f).trans hz.symm⟩
    obtain ⟨l,hl⟩ := htrans (f w).toAdd z.toAdd hi hz
    exact ⟨⟨(l:G)*w*(l:G)⁻¹,(mem_normalizer_iff.mp (hNB l.property) w).mp w.property⟩,
      Multiplicative.toAdd.injective ((hf l w).trans hl)⟩
  let K := f.ker.map B.subtype
  have hKB : K ≤ B := map_subtype_le _
  have hK (z : B) : (z:G) ∈ K ↔ f z = 1 := mem_map_iff_mem B.subtype_injective
  have hNK : L ≤ normalizer (K : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro l z hz
    obtain ⟨z,hz,rfl⟩ := hz
    let z' : B := ⟨(l:G)*z*(l:G)⁻¹,(mem_normalizer_iff.mp (hNB l.property) z).mp z.property⟩
    apply (hK z').mpr
    apply Multiplicative.toAdd.injective
    rw [hf l z]
    change f z = 1 at hz
    rw [hz]
    exact map_zero _
  have hzero : K = ⊥ := by
    rcases hmin K hKB hNK with he | hc
    · have hwk : (w:G) ∈ K := he.symm ▸ w.property
      exact (hi ((hK w).mp hwk)).elim
    · exact hc
  refine ⟨{
    section_le := hBA.trans s.section_le
    kernel_le := bot_le
    normalized := hNB
    coordinates := f
    onto := honto
    kernel_eq := ?_
    equivariant := hf }⟩
  rw [bot_subgroupOf]
  apply bot_unique
  intro z hz
  have hzK : (z:G) ∈ K := (hK z).mpr hz
  rw [hzero,mem_bot] at hzK
  exact Subtype.ext hzK

end Representation.BinaryConjugationSection

