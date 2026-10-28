module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.AutomorphismExhaustion
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterQuotientCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OrderSixApplication

/-!
# The marked outer quotient of the actual second Tits core

The 96 checked representative words define a homomorphism from C₂² × S₄
into the quotient of the actual automorphism group by its inner subgroup.
The transition identities prove multiplicativity. The 384-by-64 exhaustion
proves surjectivity and gives quotient order 96, hence an isomorphism.
The original Sylow actor s8 maps to a transposition; relabelling the four
points gives the precise marked element required by the action census.

The final theorem applies this quotient to the proved order-six subgroup
conjugacy, producing conjugacy of the actual core action overgroups. No
abstract family tag or unproved automorphism enumeration is used.
Source and marking: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.12
and14.2.21, printed pp.263 and988--989.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.SecondCoreAction
namespace OuterQuotient
open CoreGenerators OuterGenerators AutomorphismExhaustion
local notation "C" => Core
local notation "Q" => MulAut Core ⧸ MulAut.innerSubgroup Core
local notation "mk" => QuotientGroup.mk' (MulAut.innerSubgroup Core)

def representative (j : Fin 96) : MulAut Core := wordAut (OuterQuotientCertificate.word j)

theorem representative_normalForm (j : Fin 96) (n : Fin 1024) :
    representative j (coreNormalForm n) = coreNormalForm (OuterQuotientCertificate.evaluate j n) :=
  wordAut_normalForm _ _

private theorem perm_normalForm (n : Fin 1024) :
    perm (coreNormalForm n) = CoreAutomorphismCertificate.form n := by
  change AmalgamRigidity.SecondExtension.perm (coreNormalForm n : second) = _
  rw [coreNormalForm_val,AmalgamRigidity.SecondExtension.map_word]
  unfold CoreAutomorphismCertificate.form
  congr 1
  exact funext AmalgamRigidity.SecondExtension.perm_gen

/-- The finite transition table holds for actual core automorphisms. -/
theorem representative_transition (j : Fin 96) (a : Fin 5) :
    candidateAut a * representative j =
      MulAut.conj (coreNormalForm (OuterQuotientCertificate.correction j a)) * representative (OuterQuotientCertificate.next j a) := by
  have h (i : Fin 2) :
      (candidateAut a * representative j) (pairGenerator i) =
      (MulAut.conj (coreNormalForm (OuterQuotientCertificate.correction j a)) *
        representative (OuterQuotientCertificate.next j a)) (pairGenerator i) := by
    rw [pairGenerator_eq]
    change candidateAut a (representative j (coreNormalForm (pairIndex i))) =
      coreNormalForm (OuterQuotientCertificate.correction j a) *
        representative (OuterQuotientCertificate.next j a) (coreNormalForm (pairIndex i)) *
          (coreNormalForm (OuterQuotientCertificate.correction j a))⁻¹
    rw [representative_normalForm,candidateAut_normalForm,representative_normalForm]
    apply eq_of_points
    · simpa only [map_mul,map_inv,perm_normalForm,pairIndex] using
        (OuterQuotientCertificate.transitions j a i).1
    · simpa only [map_mul,map_inv,perm_normalForm,pairIndex] using
        (OuterQuotientCertificate.transitions j a i).2
  exact aut_ext _ _ (h 0) (h 1)

private theorem mk_conj (c : Core) : mk (MulAut.conj c) = 1 := by
  apply (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup Core) (x := MulAut.conj c)).mpr
  exact ⟨c,rfl⟩

theorem quotient_transition (j : Fin 96) (a : Fin 5) :
    mk (representative (OuterQuotientCertificate.next j a)) = mk (candidateAut a) * mk (representative j) := by
  have h := congrArg mk (representative_transition j a)
  simpa only [map_mul,mk_conj,one_mul] using h.symm

private theorem label_generated :
    Submonoid.closure (Set.range OuterQuotientCertificate.labelGenerator) = ⊤ := by
  let N := Submonoid.closure (Set.range OuterQuotientCertificate.labelGenerator)
  have hl (i : Fin 6) : OuterQuotientCertificate.labelLetter i ∈ N := by
    unfold OuterQuotientCertificate.labelLetter
    split
    · exact Submonoid.subset_closure ⟨_,rfl⟩
    · exact N.one_mem
  have hw (w : List (Fin 6)) (x : OuterModel) (hx : x ∈ N) :
      w.foldl (fun z i => OuterQuotientCertificate.labelLetter i * z) x ∈ N := by
    induction w generalizing x with
    | nil => exact hx
    | cons i w ih => exact ih _ (N.mul_mem (hl i) hx)
  apply top_unique
  intro x _
  rw [← OuterQuotientCertificate.label_index x]
  exact hw _ 1 N.one_mem

private theorem generator_images : ∀ a : Fin 5,
    OuterQuotientCertificate.evaluate (OuterQuotientCertificate.index (OuterQuotientCertificate.labelGenerator a)) 4 = CoreAutomorphismCertificate.image a 4 ∧
    OuterQuotientCertificate.evaluate (OuterQuotientCertificate.index (OuterQuotientCertificate.labelGenerator a)) 256 = CoreAutomorphismCertificate.image a 256 := by
  decide +kernel

private theorem representative_generator (a : Fin 5) :
    representative (OuterQuotientCertificate.index (OuterQuotientCertificate.labelGenerator a)) = candidateAut a := by
  apply aut_ext
  · change representative _ (coreNormalForm 4) = candidateAut a (coreNormalForm 4)
    rw [representative_normalForm,candidateAut_normalForm,(generator_images a).1]
  · change representative _ (coreNormalForm 256) = candidateAut a (coreNormalForm 256)
    rw [representative_normalForm,candidateAut_normalForm,(generator_images a).2]

private theorem representative_one : representative (OuterQuotientCertificate.index 1) = 1 := by
  have h : OuterQuotientCertificate.evaluate (OuterQuotientCertificate.index 1) 4 = 4 ∧ OuterQuotientCertificate.evaluate (OuterQuotientCertificate.index 1) 256 = 256 := by
    decide +kernel
  apply aut_ext
  · change representative _ (coreNormalForm 4) = coreNormalForm 4
    rw [representative_normalForm,h.1]
  · change representative _ (coreNormalForm 256) = coreNormalForm 256
    rw [representative_normalForm,h.2]

private def quotientRepresentative (x : OuterModel) : Q :=
  mk (representative (OuterQuotientCertificate.index x))

private theorem quotientRepresentative_one : quotientRepresentative 1 = 1 :=
  (congrArg mk representative_one).trans (map_one mk)

private theorem quotientRepresentative_generator (a : Fin 5) :
    quotientRepresentative (OuterQuotientCertificate.labelGenerator a) = mk (candidateAut a) :=
  congrArg mk (representative_generator a)

private theorem quotientRepresentative_mul (a : Fin 5) (y : OuterModel) :
    quotientRepresentative (OuterQuotientCertificate.labelGenerator a * y) =
      quotientRepresentative (OuterQuotientCertificate.labelGenerator a) * quotientRepresentative y := by
  have he : OuterQuotientCertificate.label
      (OuterQuotientCertificate.next (OuterQuotientCertificate.index y) a) =
      OuterQuotientCertificate.labelGenerator a * y :=
    (OuterQuotientCertificate.label_next _ _).trans
      (congrArg (OuterQuotientCertificate.labelGenerator a * ·)
        (OuterQuotientCertificate.label_index y))
  have hi : OuterQuotientCertificate.index (OuterQuotientCertificate.labelGenerator a * y) =
      OuterQuotientCertificate.next (OuterQuotientCertificate.index y) a :=
    (congrArg OuterQuotientCertificate.index he.symm).trans
      (OuterQuotientCertificate.index_label _)
  calc
    quotientRepresentative (OuterQuotientCertificate.labelGenerator a * y) =
        mk (representative (OuterQuotientCertificate.next (OuterQuotientCertificate.index y) a)) :=
      congrArg (fun j => mk (representative j)) hi
    _ = mk (candidateAut a) * quotientRepresentative y := quotient_transition _ _
    _ = quotientRepresentative (OuterQuotientCertificate.labelGenerator a) * quotientRepresentative y :=
      congrArg (· * quotientRepresentative y) (quotientRepresentative_generator a).symm

/-- The representatives give a homomorphism into the literal outer quotient. -/
def fromModel : OuterModel →* Q :=
  MonoidHom.ofClosureMEqTopLeft quotientRepresentative label_generated
    quotientRepresentative_one (by
      rintro x ⟨a,rfl⟩ y
      exact quotientRepresentative_mul a y)

theorem fromModel_generator (a : Fin 5) :
    fromModel (OuterQuotientCertificate.labelGenerator a) = mk (candidateAut a) :=
  quotientRepresentative_generator a

theorem fromModel_surjective : Function.Surjective fromModel := by
  have hl (i : Fin 6) : mk (letterAut i) ∈ fromModel.range := by
    unfold letterAut
    split
    · exact ⟨OuterQuotientCertificate.labelGenerator _,fromModel_generator _⟩
    · rw [map_one]
      exact fromModel.range.one_mem
  have hw (w : List (Fin 6)) : mk (wordAut w) ∈ fromModel.range := by
    induction w with
    | nil => simpa only [wordAut,map_one] using fromModel.range.one_mem
    | cons i w ih =>
      rw [wordAut,map_mul]
      exact fromModel.range.mul_mem ih (hl i)
  intro z
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Core) z
  obtain ⟨i,j,rfl⟩ := exhaustion a
  rw [map_mul]
  exact fromModel.range.mul_mem (hw _) (hw _)

theorem quotient_card : Nat.card Q = 96 := by
  have h := (MulAut.innerSubgroup Core).index_mul_card
  rw [Subgroup.index_eq_card,inner_card,automorphism_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 256) h

/-- The target and the actual outer quotient have equal order, so the
surjective homomorphism of representatives is an isomorphism. -/
def equiv : OuterModel ≃* Q :=
  MulEquiv.ofBijective fromModel (fromModel_surjective.bijective_of_nat_card_le (by
    rw [quotient_card]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_multiplicative,
      Fintype.card_perm,ZMod.card]))

/-- Projection from the actual automorphism group, before adjusting the mark. -/
def projection : MulAut Core →* OuterModel := equiv.symm.toMonoidHom.comp mk

theorem projection_surjective : Function.Surjective projection :=
  equiv.symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_ker : projection.ker = MulAut.innerSubgroup Core := by
  rw [projection,MonoidHom.ker_comp_of_injective _ _ equiv.symm.injective,
    QuotientGroup.ker_mk']


theorem projection_generator (a : Fin 5) :
    projection (candidateAut a) = OuterQuotientCertificate.labelGenerator a := by
  change equiv.symm (mk (candidateAut a)) = _
  apply equiv.symm_apply_eq.mpr
  exact (fromModel_generator a).symm

private def labelWord : List (Fin 6) → OuterModel
  | [] => 1
  | i :: w => labelWord w * OuterQuotientCertificate.labelLetter i

private theorem projection_word (w : List (Fin 6)) :
    projection (wordAut w) = labelWord w := by
  induction w with
  | nil => exact map_one projection
  | cons i w ih =>
    rw [wordAut,map_mul,ih,labelWord]
    congr 1
    unfold letterAut OuterQuotientCertificate.labelLetter
    split
    · exact projection_generator _
    · exact map_one projection

private def markingWord : List (Fin 6) := [0,1,1,4,1,0,0,0,4]

private theorem perm_marking (n : Fin 1024) :
    perm (sylow (SecondRecognition.positive 8) (coreNormalForm n)) =
      AmalgamRigidity.SecondExtension.packedGen 8 * CoreAutomorphismCertificate.form n *
        (AmalgamRigidity.SecondExtension.packedGen 8)⁻¹ := by
  have hs : Subgroup.inclusion sylow_le_second (SecondRecognition.positive 8) =
      AmalgamRigidity.SecondExtension.gen 8 := SecondRecognition.inclusion_positive 8 (by decide)
  change AmalgamRigidity.SecondExtension.perm
    (Subgroup.inclusion sylow_le_second (SecondRecognition.positive 8) *
      (coreNormalForm n).val *
        (Subgroup.inclusion sylow_le_second (SecondRecognition.positive 8))⁻¹) = _
  rw [hs,map_mul,map_mul,map_inv,AmalgamRigidity.SecondExtension.perm_gen]
  change _ * perm (coreNormalForm n) * _ = _
  rw [perm_normalForm]

private theorem marking_images : ∀ i : Fin 2,
    let n : Fin 1024 := ![4,256] i
    let m := wordIndex markingWord n
    (AmalgamRigidity.SecondExtension.packedGen 8 * CoreAutomorphismCertificate.form n *
      (AmalgamRigidity.SecondExtension.packedGen 8)⁻¹) 0 = CoreAutomorphismCertificate.form m 0 ∧
    (AmalgamRigidity.SecondExtension.packedGen 8 * CoreAutomorphismCertificate.form n *
      (AmalgamRigidity.SecondExtension.packedGen 8)⁻¹) 930 = CoreAutomorphismCertificate.form m 930 := by
  decide +kernel

private theorem marking_eq_word : sylow (SecondRecognition.positive 8) = wordAut markingWord := by
  have h (i : Fin 2) : sylow (SecondRecognition.positive 8) (pairGenerator i) =
      wordAut markingWord (pairGenerator i) := by
    rw [pairGenerator_eq,wordAut_normalForm]
    apply eq_of_points
    · simpa only [perm_marking,perm_normalForm,pairIndex] using (marking_images i).1
    · simpa only [perm_marking,perm_normalForm,pairIndex] using (marking_images i).2
  exact aut_ext _ _ (h 0) (h 1)

theorem projection_marking : projection (sylow (SecondRecognition.positive 8)) =
    (1,Equiv.swap 0 2) := by
  rw [marking_eq_word,projection_word]
  decide +kernel

/-- Change only the four-point labels so that the original Sylow actor is
marked by the specified transposition. -/
def markedProjection : MulAut Core →* OuterModel :=
  (MulAut.conj ((1,Equiv.swap 1 2) : OuterModel)).toMonoidHom.comp projection

theorem markedProjection_surjective : Function.Surjective markedProjection :=
  (MulAut.conj _).surjective.comp projection_surjective

theorem markedProjection_ker : markedProjection.ker = MulAut.innerSubgroup Core := by
  rw [markedProjection,MonoidHom.ker_comp_of_injective _ _ (MulAut.conj _).injective,
    projection_ker]

theorem markedProjection_marking : markedProjection (sylow (SecondRecognition.positive 8)) =
    markedTransposition 1 := by
  change MulAut.conj _ (projection _) = _
  rw [projection_marking]
  decide +kernel

end OuterQuotient

/-- The marked outer quotient of the literal normal core of the second
Tits parabolic, with exactly the inner automorphisms as kernel. -/
theorem exists_marked_outer_quotient :
    ∃ (q : MulAut Core →* OuterModel) (v : BinaryPair),
      Function.Surjective q ∧ q.ker = MulAut.innerSubgroup Core ∧
      markedTransposition v ∈ sylow.range.map q := by
  refine ⟨OuterQuotient.markedProjection,1,OuterQuotient.markedProjection_surjective,
    OuterQuotient.markedProjection_ker,?_⟩
  exact Subgroup.mem_map.mpr ⟨sylow (SecondRecognition.positive 8),
    ⟨SecondRecognition.positive 8,rfl⟩,OuterQuotient.markedProjection_marking⟩

/-- The marked quotient supplies the full finite action census. -/
theorem action_census (A : Subgroup (MulAut Core)) (hA : sylow.range ≤ A)
    (hc : Nat.card (Subgroup.center Core) * Nat.card A = 6144) :
    ∃ α : MulAut Core, A.map (MulAut.congr α).toMonoidHom = model.range := by
  obtain ⟨q,v,hq,hk,hv⟩ := exists_marked_outer_quotient
  exact action_census_of_outer_quotient q hq hk v hv A hA hc

end Tits.ExceptionalParabolics.SecondCoreAction

