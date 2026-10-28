module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Lifting
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.ProductTransport
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.QuotientLift
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.CoordinateRecognition
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Conjugation

/-!
# The cyclic-three internal products of B.1.12

Recognition in the faithful action on C_V(O₂(H)) identifies every distinct
T-conjugate of K with one concrete coordinate odd core. The action is
injective on K₀, so independent coordinate inclusions lift to its internal
direct product. Pulling the whole factors back through the identified
embedding of M/O₂(M) gives its internal product and actual SL₂(2) models.
Naturality of the odd core and the quotient conjugation equations identify
the marked K_i images and establish the transitive induced T-action.

`threeConjugates_of_solvableFF` discharges recognition and factor permutation,
as well as all local-group and quotient premises. Its sole upstream theorem
input is the permitted universal valid B.1.8 contract `SolvableFFTheorem`;
that contract is to be discharged by the parent B.1.8/B.1.12 assembly owner.
The false arbitrary-family equality in printed B.1.8(5) is not used.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  [FiniteDimensional (ZMod 2) V]
  (hf : Function.Injective ρ) (K : Subgroup G) (T : Sylow 2 G)
  (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3)
  (d : SolvableFFStructure (subspaceImageRepresentation
    (localRepresentation ρ K (T : Subgroup G)) (localFixedSpace ρ K (T : Subgroup G))))
  (r : CoordinateRecognition d (localImageFamily ρ K (T : Subgroup G))
    (localImageThree ρ K (T : Subgroup G)) (localImageSylow ρ K T))

/-- Index the actual original conjugates by the recognized concrete factors. -/
noncomputable def sourceCoordinateIndex : conjugateFamily K (T : Subgroup G) ≃ Fin d.count :=
  (conjugateImageEquiv ρ hf K T hK hcard).trans r.index

/-- Each indexed odd core is the literal action image of its original conjugate. -/
theorem sourceCoordinateIndex_oddCore (c : conjugateFamily K (T : Subgroup G)) :
    d.toSolvableFFFactors.factorOddCore (sourceCoordinateIndex ρ hf K T hK hcard d r c) =
      localImageOf ρ K (T : Subgroup G) c :=
  r.oddCore_eq (conjugateImageEquiv ρ hf K T hK hcard c)

/-- Conjugation of the original subgroups transports their recognized factors. -/
theorem sourceCoordinateIndex_equivariant (t : T) (c c' : conjugateFamily K (T : Subgroup G))
    (he : (c : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom = (c' : Subgroup G)) :
    (d.factor (sourceCoordinateIndex ρ hf K T hK hcard d r c)).map
      (MulAut.conj (localActionHom ρ K (T : Subgroup G)
        (inclusion (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) t))).toMonoidHom =
      d.factor (sourceCoordinateIndex ρ hf K T hK hcard d r c') := by
  let s : localImageSylow ρ K T :=
    ⟨localActionHom ρ K (T : Subgroup G)
      (inclusion (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right) t),
      mem_map_of_mem (localActionHom ρ K (T : Subgroup G)) t.property⟩
  apply r.equivariant s (conjugateImageEquiv ρ hf K T hK hcard c)
    (conjugateImageEquiv ρ hf K T hK hcard c')
  change (localImageOf ρ K (T : Subgroup G) c).map _ = localImageOf ρ K (T : Subgroup G) c'
  rw [← localImageOf_map_conj ρ K (T : Subgroup G) c t, he]

/-- The distinct original order-three conjugates form an internal direct product. -/
noncomputable def sourceConjugateProduct :
    ((c : conjugateFamily K (T : Subgroup G)) → (c : Subgroup G)) ≃*
      conjugateClosure K (T : Subgroup G) := by
  classical
  letI := Fintype.ofFinite (conjugateFamily K (T : Subgroup G))
  let f := (localActionHom ρ K (T : Subgroup G)).comp
    (inclusion (conjugateClosure_le_sup K (T : Subgroup G)))
  let inc (c : conjugateFamily K (T : Subgroup G)) := inclusion (conjugate_le_closure _ _ c)
  have hfac (c : conjugateFamily K (T : Subgroup G)) :
      (f.comp (inc c)).range ≤ d.factor (sourceCoordinateIndex ρ hf K T hK hcard d r c) := by
    have he : f.comp (inc c) = (localActionHom ρ K (T : Subgroup G)).comp
        (inclusion ((conjugate_le_closure _ _ c).trans (conjugateClosure_le_sup K (T : Subgroup G)))) := rfl
    rw [he, ← localImageOf_eq_range, ← sourceCoordinateIndex_oddCore ρ hf K T hK hcard d r]
    exact d.toSolvableFFFactors.factorOddCore_le _
  have hgen : (⨆ c, (inc c).range) = ⊤ := by
    apply Subgroup.map_injective (conjugateClosure K (T : Subgroup G)).subtype_injective
    rw [Subgroup.map_iSup]
    simp only [inc, inclusion_range, map_subgroupOf_eq_of_le (conjugate_le_closure _ _ _),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact (conjugateClosure_eq_iSup_family K (T : Subgroup G)).symm
  exact coordinateProduct d.toSolvableFFFactors f
    (closureAction_injective ρ hf K (T : Subgroup G) hK hcard T.isPGroup')
    (sourceCoordinateIndex ρ hf K T hK hcard d r)
    (sourceCoordinateIndex ρ hf K T hK hcard d r).injective inc
    (fun c => inclusion_injective _) hfac hgen

@[simp] theorem sourceConjugateProduct_single
    (c : conjugateFamily K (T : Subgroup G)) (k : (c : Subgroup G)) :
    letI := Classical.decEq (conjugateFamily K (T : Subgroup G))
    (sourceConjugateProduct ρ hf K T hK hcard d r (Pi.mulSingle c k) : G) = (k : G) := by
  classical
  simp only [sourceConjugateProduct, coordinateProduct_single]
  rfl

variable (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆)

/-- The quotient factors are actual subgroups of the intrinsic quotient M/O₂(M). -/
noncomputable def sourceQuotientFactor (c : conjugateFamily K (T : Subgroup G)) :
    Subgroup (mixedSubgroup ρ K (T : Subgroup G) ⧸ pCore 2 (mixedSubgroup ρ K (T : Subgroup G))) :=
  pulledFactor d.toSolvableFFFactors (mixedImageEmbedding ρ hf K T hK hcard hcomm)
    (sourceCoordinateIndex ρ hf K T hK hcard d r c)

/-- The actual quotient image of each factor is the specified concrete coordinate. -/
theorem sourceQuotientFactor_map (c : conjugateFamily K (T : Subgroup G)) :
    (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c).map
      (mixedImageEmbedding ρ hf K T hK hcard hcomm) =
        d.factor (sourceCoordinateIndex ρ hf K T hK hcard d r c) :=
  pulledFactor_map d.toSolvableFFFactors _
    ((mixedImageEmbedding_range ρ hf K T hK hcard hcomm).trans r.generated_eq) _

/-- No two original conjugates label the same quotient factor. -/
theorem sourceQuotientFactor_injective :
    Function.Injective (sourceQuotientFactor ρ hf K T hK hcard d r hcomm) := by
  intro c c' he
  apply (sourceCoordinateIndex ρ hf K T hK hcard d r).injective
  apply d.toSolvableFFFactors.factor_injective
  rw [← sourceQuotientFactor_map ρ hf K T hK hcard d r hcomm c,
    ← sourceQuotientFactor_map ρ hf K T hK hcard d r hcomm c', he]

/-- The literal quotient is the internal product of these factors. -/
noncomputable def sourceQuotientProduct :
    ((c : conjugateFamily K (T : Subgroup G)) → sourceQuotientFactor ρ hf K T hK hcard d r hcomm c) ≃*
      (mixedSubgroup ρ K (T : Subgroup G) ⧸ pCore 2 (mixedSubgroup ρ K (T : Subgroup G))) := by
  classical
  letI := Fintype.ofFinite (conjugateFamily K (T : Subgroup G))
  let f := mixedImageEmbedding ρ hf K T hK hcard hcomm
  let hi := mixedImageEmbedding_injective ρ hf K T hK hcard hcomm
  let j := sourceCoordinateIndex ρ hf K T hK hcard d r
  let A := sourceQuotientFactor ρ hf K T hK hcard d r hcomm
  have hfac (c : conjugateFamily K (T : Subgroup G)) :
      (f.comp (A c).subtype).range ≤ d.factor (j c) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (sourceQuotientFactor_map ρ hf K T hK hcard d r hcomm c).le
  have hgen : (⨆ c, (A c).subtype.range) = ⊤ := by
    simp only [Subgroup.range_subtype]
    change (⨆ c, pulledFactor d.toSolvableFFFactors f (j c)) = ⊤
    rw [j.surjective.iSup_comp]
    exact iSup_pulledFactor d.toSolvableFFFactors f hi
      ((mixedImageEmbedding_range ρ hf K T hK hcard hcomm).trans r.generated_eq)
  exact coordinateProduct d.toSolvableFFFactors f hi j j.injective
    (fun c => (A c).subtype) (fun c => (A c).subtype_injective) hfac hgen

@[simp] theorem sourceQuotientProduct_single
    (c : conjugateFamily K (T : Subgroup G)) (g : sourceQuotientFactor ρ hf K T hK hcard d r hcomm c) :
    letI := Classical.decEq (conjugateFamily K (T : Subgroup G))
    sourceQuotientProduct ρ hf K T hK hcard d r hcomm (Pi.mulSingle c g) = g := by
  classical
  simp only [sourceQuotientProduct, coordinateProduct_single, Subgroup.subtype_apply]

/-- Each quotient factor has an actual L₂(2)=SL₂(2) matrix model. -/
noncomputable def sourceQuotientFactorModel (c : conjugateFamily K (T : Subgroup G)) :
    sourceQuotientFactor ρ hf K T hK hcard d r hcomm c ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (pulledFactorEquiv d.toSolvableFFFactors _
    (mixedImageEmbedding_injective ρ hf K T hK hcard hcomm)
    ((mixedImageEmbedding_range ρ hf K T hK hcard hcomm).trans r.generated_eq) _).trans
      (d.factorModel (sourceCoordinateIndex ρ hf K T hK hcard d r c))

/-- The odd core is exactly the prescribed original conjugate's quotient image. -/
theorem sourceQuotientFactor_oddCore (c : conjugateFamily K (T : Subgroup G)) :
    (pPrimeCore 2 (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c)).map
      (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c).subtype =
        quotientConjugate ρ K (T : Subgroup G) c := by
  apply Subgroup.map_injective (mixedImageEmbedding_injective ρ hf K T hK hcard hcomm)
  rw [quotientConjugate_image]
  exact (pulledFactor_oddCore d.toSolvableFFFactors _
    (mixedImageEmbedding_injective ρ hf K T hK hcard hcomm)
    ((mixedImageEmbedding_range ρ hf K T hK hcard hcomm).trans r.generated_eq) _).trans
      (sourceCoordinateIndex_oddCore ρ hf K T hK hcard d r c)

/-- The factor action is induced by conjugation on M and passage through its two-core. -/
theorem sourceQuotientFactor_equivariant (t : T) (c c' : conjugateFamily K (T : Subgroup G))
    (he : (c : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom = (c' : Subgroup G)) :
    (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c).map
      (mixedQuotientAction ρ K (T : Subgroup G) t).toMonoidHom =
        sourceQuotientFactor ρ hf K T hK hcard d r hcomm c' := by
  apply Subgroup.map_injective (mixedImageEmbedding_injective ρ hf K T hK hcard hcomm)
  rw [mixedImageEmbedding_map_action, sourceQuotientFactor_map, sourceQuotientFactor_map]
  exact sourceCoordinateIndex_equivariant ρ hf K T hK hcard d r t c c' he

/-- Every induced T-automorphism preserves the actual quotient factor family. -/
theorem sourceQuotientFactor_permuted (t : T) (c : conjugateFamily K (T : Subgroup G)) :
    ∃ c' : conjugateFamily K (T : Subgroup G),
      (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c).map
        (mixedQuotientAction ρ K (T : Subgroup G) t).toMonoidHom =
          sourceQuotientFactor ρ hf K T hK hcard d r hcomm c' := by
  obtain ⟨a, ha⟩ := c.property
  let c' : conjugateFamily K (T : Subgroup G) :=
    ⟨K.map (MulAut.conj ((t * a : T) : G)).toMonoidHom, ⟨t * a, rfl⟩⟩
  refine ⟨c', sourceQuotientFactor_equivariant ρ hf K T hK hcard d r hcomm t c c' ?_⟩
  rw [← ha, Subgroup.map_map]
  change K.map _ = K.map _
  congr 1
  apply MonoidHom.ext
  intro x
  change (t : G) * ((a : G) * x * (a : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (a : G)) * x * ((t : G) * (a : G))⁻¹
  group

/-- Transitivity concerns the literal induced T-action on quotient subgroups. -/
theorem sourceQuotientFactor_transitive (c c' : conjugateFamily K (T : Subgroup G)) :
    ∃ t : T, (sourceQuotientFactor ρ hf K T hK hcard d r hcomm c).map
      (mixedQuotientAction ρ K (T : Subgroup G) t).toMonoidHom =
        sourceQuotientFactor ρ hf K T hK hcard d r hcomm c' := by
  obtain ⟨t, ht⟩ := conjugateFamily_transitive K (T : Subgroup G) c c'
  exact ⟨t, sourceQuotientFactor_equivariant ρ hf K T hK hcard d r hcomm t c c' ht⟩

/-- Assemble the two internal products from recognition in the faithful fixed-space image. -/
noncomputable def conclusionOfRecognition : ThreeConjugatesConclusion ρ K (T : Subgroup G) where
  groupProduct := sourceConjugateProduct ρ hf K T hK hcard d r
  groupProduct_single := sourceConjugateProduct_single ρ hf K T hK hcard d r
  quotientFactor := sourceQuotientFactor ρ hf K T hK hcard d r hcomm
  quotientProduct := sourceQuotientProduct ρ hf K T hK hcard d r hcomm
  quotientProduct_single := sourceQuotientProduct_single ρ hf K T hK hcard d r hcomm
  factorModel := sourceQuotientFactorModel ρ hf K T hK hcard d r hcomm
  oddCore := sourceQuotientFactor_oddCore ρ hf K T hK hcard d r hcomm
  equivariant := sourceQuotientFactor_equivariant ρ hf K T hK hcard d r hcomm
  transitive := sourceQuotientFactor_transitive ρ hf K T hK hcard d r hcomm

include hf hK hcard hcomm in
/-- B.1.12 from the universal valid B.1.8 theorem. Every local, coordinate,
normalization, kernel and product premise is discharged here; only B.1.8
remains with the source-theorem assembly owner. -/
theorem threeConjugates_of_solvableFF (structureTheorem : SolvableFFTheorem.{v, v}) :
    Nonempty (ThreeConjugatesConclusion ρ K (T : Subgroup G)) := by
  obtain ⟨d', ⟨r'⟩⟩ := localImage_coordinateRecognition structureTheorem hf K T hK hcard hcomm
    (fun d' => d'.toSolvableFFFactors.exists_factor_map_conj)
  exact ⟨conclusionOfRecognition ρ hf K T hK hcard d' r' hcomm⟩

end CFSG.Quasithin.ChapterB.ThreeConjugates
