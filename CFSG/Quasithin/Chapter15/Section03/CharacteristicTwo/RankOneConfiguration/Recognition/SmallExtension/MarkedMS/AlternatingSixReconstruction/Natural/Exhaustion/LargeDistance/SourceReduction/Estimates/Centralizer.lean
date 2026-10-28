module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Conjugacy
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Offenders

/-!
# The centralizer of the derived offender image

Two commuting-word tests place the centralizer of the even four-group in
the three-pair group. Its alternating intersection is the original four-group.
Conjugation preserves this conclusion. Applying it to the actual elementary
Thompson image gives its self-centralizer in A₆ and identifies the inverse
image of that quotient centralizer as J(R)O₂(M). This inverse image is not
identified with the centralizer of J(R) in M.

Source: the unique-offender calculation in MS93 (3.8), printed p.877.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six

private theorem centralizing_words :
    ∀ g : Equiv.Perm (Fin 6),
      g * planeWords 4 1 = planeWords 4 1 * g →
      g * planeWords 4 2 = planeWords 4 2 * g →
      ∃ i : Fin 8, dWords i = g := by
  decide +kernel

/-- The unique even offender is self-centralizing in the alternating actor. -/
theorem evenPart_centralizer :
    alternatingGroup (Fin 6) ⊓ centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) =
      evenPart 6 := by
  apply le_antisymm
  · intro g hg
    have h1 := hg.2 (planeWords 4 1) ((mem_evenPart_iff _).mpr ⟨1,rfl⟩)
    have h2 := hg.2 (planeWords 4 2) ((mem_evenPart_iff _).mpr ⟨2,rfl⟩)
    obtain ⟨i, hi⟩ := centralizing_words g h1.symm h2.symm
    refine ⟨?_, hg.1⟩
    exact (mem_disjointTranspositions_iff 3 g).mpr ⟨i,hi⟩
  · intro g hg
    refine ⟨hg.2, ?_⟩
    let := isElementaryTwo_evenPart.2
    intro a ha
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : evenPart 6) ⟨g,hg⟩)

/-- The self-centralizer calculation retains any conjugate marking. -/
theorem conjugate_evenPart_centralizer {A : Subgroup (Equiv.Perm (Fin 6))}
    (hA : IsConjugateTo A (evenPart 6)) :
    alternatingGroup (Fin 6) ⊓ centralizer (A : Set (Equiv.Perm (Fin 6))) = A := by
  obtain ⟨g, rfl⟩ := hA
  let f := (MulAut.conj g).toMonoidHom
  apply le_antisymm
  · intro x hx
    let y := (MulAut.conj g).symm x
    have hy : y ∈ alternatingGroup (Fin 6) ⊓
        centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) := by
      constructor
      · exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem x hx.1 g⁻¹
      · intro a ha
        apply (MulAut.conj g).injective
        rw [map_mul, map_mul]
        have hf : (MulAut.conj g) y = x := (MulAut.conj g).apply_symm_apply x
        rw [hf]
        exact hx.2 _ (mem_map_of_mem f ha)
    rw [evenPart_centralizer] at hy
    exact ⟨y, hy, (MulAut.conj g).apply_symm_apply x⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨(inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem a ha.2 g, ?_⟩
    rintro b ⟨c, hc, rfl⟩
    have hcomm := ((show a ∈ alternatingGroup (Fin 6) ⊓
        centralizer (evenPart 6 : Set (Equiv.Perm (Fin 6))) by
      rw [evenPart_centralizer]; exact ha).2 c hc)
    simpa only [map_mul] using congrArg f hcomm

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

/-- The literal elementary Thompson image is self-centralizing in A₆. -/
theorem thompson_image_centralizer
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    alternatingGroup (Fin 6) ⊓
        centralizer ((Stellmacher.elementaryAbelianMaxJ d.radical).map
          (projection h e hz hn d) : Set (Equiv.Perm (Fin 6))) =
      (Stellmacher.elementaryAbelianMaxJ d.radical).map (projection h e hz hn d) :=
  conjugate_evenPart_centralizer (Cover.thompson_even_image h e hz hn d himage).1

/-- The preimage of the quotient centralizer is exactly J(R)O₂(M).
This retains the original map and does not assert that O₂(M) centralizes J(R). -/
theorem thompson_image_centralizer_comap
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    (centralizer ((Stellmacher.elementaryAbelianMaxJ d.radical).map
      (projection h e hz hn d) : Set (Equiv.Perm (Fin 6)))).comap (projection h e hz hn d) =
      Stellmacher.elementaryAbelianMaxJ d.radical ⊔ pCore 2 d.overgroup := by
  have ha : (alternatingGroup (Fin 6)).comap (projection h e hz hn d) = ⊤ := by
    apply top_unique
    intro x _
    rw [mem_comap, ← himage]
    exact ⟨x, rfl⟩
  have he := congrArg (Subgroup.comap (projection h e hz hn d))
    (thompson_image_centralizer h e hz hn d himage)
  rw [comap_inf, ha, top_inf_eq, comap_map_eq, projection_kernel] at he
  exact he

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
