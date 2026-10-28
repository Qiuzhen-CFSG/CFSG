module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Structure.Collection
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Kernel
/-!
# The radical action and its faithful relative-kernel quotient

Reverse collection shows that the entire actual radical preserves each block.
Its action is transported through the literal map to the barred radical inside
`N1Image`; the inclusion and quotient equations retain the original block action.
The quotient by this action's full kernel acts faithfully, with the exact word
criterion inherited from the signed-vector calculation. Its order and
extraspecial structure are separate group-theoretic obligations.

Source: Aschbacher, *Sporadic Groups*, Section 27's bar convention and
Lemma 29.13(4), printed pp. 144 and 160–161.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin Atlas.Codes Atlas.Fischer
/-- Collection proves that every element of the radical stabilizes every block. -/
theorem R_mem_blockStabilizer (h : GeneratorLaws) (c : Octad) (g : N1)
    (hg : g.val ∈ R) : g ∈ blockStabilizer c := by
  obtain ⟨d,e,a,ha,he⟩ := R_collection g.val hg
  have he' : normalForm d e (parkerCocodeStandard a) = g := Subtype.ext he
  rw [← he']
  exact normalForm_mem_blockStabilizer h d e a ha c

/-- The full radical, identified with the previously defined block actor. -/
def radicalActorEquiv (h : GeneratorLaws) (c : Octad) : R ≃* blockActor c where
  toFun g := ⟨⟨⟨g.val,R_le_N1 g.prop⟩,
    R_mem_blockStabilizer h c _ g.prop⟩, g.prop⟩
  invFun g := ⟨g.val.val.val,g.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The existing block action on the full, unbarred radical. -/
def radicalAction (h : GeneratorLaws) (c : Octad) : Representation ℝ R (block c) :=
  (blockAction c).comp (radicalActorEquiv h c).toMonoidHom

@[simp] theorem radicalAction_val (h : GeneratorLaws) (c : Octad) (g : R) (v : block c) :
    (radicalAction h c g v).val = representation ⟨g.val,R_le_N1 g.prop⟩ v.val := rfl

/-- The actual restriction of the published quotient map to the radical. -/
def radicalBarMap : R →* barredR where
  toFun g := ⟨n1ImageMap ⟨g.val,R_le_N1 g.prop⟩,
    ⟨⟨g.val,R_le_N1 g.prop⟩,g.prop,rfl⟩⟩
  map_one' := Subtype.ext (map_one n1ImageMap)
  map_mul' g k := Subtype.ext (map_mul n1ImageMap ⟨g.val,R_le_N1 g.prop⟩ ⟨k.val,R_le_N1 k.prop⟩)

theorem radicalBarMap_surjective : Function.Surjective radicalBarMap := by
  rintro ⟨g,q,hq,he⟩
  exact ⟨⟨q.val,hq⟩,Subtype.ext he⟩

theorem imageRepresentation_preserves_block (h : GeneratorLaws) (c : Octad)
    (g : barredR) (v : Space) (hv : v ∈ block c) :
    imageRepresentation g.val v ∈ block c := by
  obtain ⟨q,rfl⟩ := radicalBarMap_surjective g
  rw [show (radicalBarMap q).val = n1ImageMap ⟨q.val,R_le_N1 q.prop⟩ from rfl,
    imageRepresentation_map]
  exact (radicalAction h c q ⟨v,hv⟩).prop

/-- The action on the genuine barred radical in the literal `N1Image`. -/
def barredBlockAction (h : GeneratorLaws) (c : Octad) :
    Representation ℝ barredR (block c) where
  toFun g := (imageRepresentation g.val).restrict (imageRepresentation_preserves_block h c g)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one imageRepresentation) v.val
  map_mul' g k := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul imageRepresentation g.val k.val) v.val

@[simp] theorem barredBlockAction_val (h : GeneratorLaws) (c : Octad)
    (g : barredR) (v : block c) :
    (barredBlockAction h c g v).val = imageRepresentation g.val v.val := rfl

/-- The barred action and the original block action use exactly the same quotient map. -/
@[simp] theorem barredBlockAction_map (h : GeneratorLaws) (c : Octad) (g : R) :
    barredBlockAction h c (radicalBarMap g) = radicalAction h c g := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (imageRepresentation_map ⟨g.val,R_le_N1 g.prop⟩) v.val

theorem barredBlockAction_blockAction (h : GeneratorLaws) (c : Octad) (g : blockActor c) :
    barredBlockAction h c (radicalBarMap ((radicalActorEquiv h c).symm g)) =
      blockAction c g := by
  rw [barredBlockAction_map]
  rfl

/-- The literal relative kernel in the actual barred radical. -/
def relativeKernel (h : GeneratorLaws) (c : Octad) : Subgroup barredR :=
  (barredBlockAction h c).ker

instance relativeKernel_normal (h : GeneratorLaws) (c : Octad) :
    (relativeKernel h c).Normal := inferInstanceAs (barredBlockAction h c).ker.Normal

/-- The quotient in 29.13(4), prior to its order and extraspeciality calculation. -/
abbrev BlockQuotient (h : GeneratorLaws) (c : Octad) := barredR ⧸ relativeKernel h c

/-- The faithful action of the actual relative-kernel quotient. -/
def quotientBlockAction (h : GeneratorLaws) (c : Octad) :
    Representation ℝ (BlockQuotient h c) (block c) :=
  QuotientGroup.lift (relativeKernel h c) (barredBlockAction h c) le_rfl

@[simp] theorem quotientBlockAction_mk (h : GeneratorLaws) (c : Octad) (g : barredR) :
    quotientBlockAction h c (QuotientGroup.mk' (relativeKernel h c) g) =
      barredBlockAction h c g := rfl

theorem quotientBlockAction_injective (h : GeneratorLaws) (c : Octad) :
    Function.Injective (quotientBlockAction h c) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr rfl

/-- Collected words detect the whole relative kernel, now in the barred actor. -/
theorem relativeKernel_word_iff (h : GeneratorLaws) (c : Octad)
    (d e : ParkerLoop) (a : Cocode) (ha : EvenCocode a) :
    radicalBarMap ⟨(normalForm d e (parkerCocodeStandard a)).val,normalForm_mem_R d e a ha⟩ ∈
      relativeKernel h c ↔ KernelParameters c d e a := by
  change barredBlockAction h c _ = 1 ↔ _
  rw [barredBlockAction_map]
  exact wordActor_kernel_iff h d e a ha c

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
