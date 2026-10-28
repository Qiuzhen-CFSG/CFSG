module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Relations
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization

/-!
# Verification of the G₂ presentation equations in the octonion model

The positive equations follow from the six-coordinate product. Torus weights,
Weyl conjugations, the braid relation and the two full rank-one words are
verified with their literal A–F orientation. Characteristic two includes the
fields of orders two and four. This validates evaluation of the proposed
presentation; it does not assert that evaluation is injective.

Coordinate formulas are from the licensed ATLAS port (LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff). The three missing root-conjugation checks and the
torus-conjugation checks adapt the existing `FrameAlignment/RootRecovery` and
`FrameAlignment/WeylCorrection` calculations to this narrow module.
Source application: DGS, Groups and Graphs, Theorem D, p.224.
-/

@[expose] public section
namespace Atlas.G2.RootPresentationRecognition
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

/-- The six literal octonion root homomorphisms. -/
def modelRoots : PositiveRoots F (Model F) where
  root i := {
    toFun := fun a => ![rootA,rootB,rootC,rootD,rootE,rootF] i a.toAdd
    map_one' := by fin_cases i <;> simp
    map_mul' := by
      intro a b
      fin_cases i <;> simp [rootA_add,rootB_add,rootC_add,rootD_add,rootE_add,rootF_add] }

/-- The characteristic-free positive collection equations. -/
theorem model_collectionRelations : (modelRoots (F := F)).CollectionRelations := by
  constructor
  · constructor
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,s,0,0,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,s,0,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,s,0,0,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,0,0,t,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,t,0,0,0,0])
  · constructor
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,0,t,0,0])
    · intro s t
      simpa [modelRoots, PositiveRoots.x,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,0,0,t,0])

/-- The actual roots, full torus and both Weyl elements. -/
def modelData : BorelWeylData F (Model F) where
  toPositiveRoots := modelRoots
  torus := torusHom
  r := weylR
  s := weylS

private theorem reverse_conjugation {G : Type*} [Group G] (w a b : G)
    (hw : w^2 = 1) (hab : w*a*w⁻¹ = b) : w*b*w⁻¹ = a := by
  rw [← hab]
  calc
    _ = (w*w)*a*(w*w)⁻¹ := by group
    _ = a := by rw [← pow_two, hw]; simp

private theorem rC (a : F) [CharP F 2] :
    weylR * rootC a * weylR⁻¹ = rootC a := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [weylR,weylREquiv,weylRLinear,weylRApply,
      rootC,rootCEquiv,rootCLinear,rootCApply,CharTwo.neg_eq,CharTwo.sub_eq_add]

private theorem sA (a : F) [CharP F 2] :
    weylS * rootA a * weylS⁻¹ = rootA a := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [weylS,weylSEquiv,weylSLinear,weylSApply,
      rootA,rootAEquiv,rootALinear,rootAApply,CharTwo.neg_eq,CharTwo.sub_eq_add]

private theorem sD (a : F) [CharP F 2] :
    weylS * rootD a * weylS⁻¹ = rootC a := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [weylS,weylSEquiv,weylSLinear,weylSApply,
      rootD,rootDEquiv,rootDLinear,rootDApply,
      rootC,rootCEquiv,rootCLinear,rootCApply,CharTwo.neg_eq,CharTwo.sub_eq_add]
  all_goals ring

private theorem r_torus (l m : Fˣ) :
    weylR * torus l m * weylR⁻¹ = torus l (l/m) := by
  rw [weylR_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,
      weylR,weylREquiv,weylRLinear,weylRApply, div_eq_mul_inv]
  field_simp
  simp

private theorem s_torus (l m : Fˣ) :
    weylS * torus l m * weylS⁻¹ = torus m l := by
  rw [weylS_inverse]
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,
      weylS,weylSEquiv,weylSLinear,weylSApply] <;> field_simp
  all_goals simp

private theorem braid : ((weylR : Model F) * weylS)^6 = 1 := by
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  funext i; fin_cases i <;>
    simp [pow_succ,weylR,weylREquiv,weylRLinear,weylRApply,
      weylS,weylSEquiv,weylSLinear,weylSApply]

/-- All Borel–Weyl equations hold in the full model, including the binary field. -/
theorem model_relations [CharP F 2] : (modelData (F := F)).Relations := by
  refine {
    toCharTwoRelations := model_collectionRelations.charTwo
    torus_root := ?_
    r_sq := weylR_sq
    s_sq := weylS_sq
    braid := braid
    r_torus := r_torus
    s_torus := s_torus
    rA := weylR_rootA
    rB := fun a => reverse_conjugation _ _ _ weylR_sq (weylR_rootA a)
    rC := fun a => rC a
    rD := weylR_rootD
    rF := fun a => reverse_conjugation _ _ _ weylR_sq (weylR_rootD a)
    sA := fun a => sA a
    sB := weylS_rootB
    sC := fun a => reverse_conjugation _ _ _ weylS_sq (sD a)
    sD := fun a => sD a
    sE := fun a => reverse_conjugation _ _ _ weylS_sq (weylS_rootB a)
    long_word := ?_
    short_word := ?_ }
  · intro l m i a
    fin_cases i <;>
      simp [modelData,modelRoots,PositiveRoots.x,BorelWeylData.weight,
        torusHom,torus_rootA,torus_rootB,torus_rootC,torus_rootD,torus_rootE,torus_rootF]
  · intro a
    have hn : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
    simpa [modelData,modelRoots,PositiveRoots.x,torusHom,CharTwo.neg_eq, hn] using
      long_rank_one_word a
  · intro a
    have hn : (-a⁻¹ : Fˣ) = a⁻¹ := Units.ext (by simp [CharTwo.neg_eq])
    simpa [modelData,modelRoots,PositiveRoots.x,torusHom,CharTwo.neg_eq, hn] using
      short_rank_one_word a

end Atlas.G2.RootPresentationRecognition
