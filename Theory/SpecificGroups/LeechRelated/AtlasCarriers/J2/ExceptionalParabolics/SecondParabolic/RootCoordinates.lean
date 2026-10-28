module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Coverage
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.IntrinsicCoordinates.Collection
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.RootRealization

/-!
# Native coordinates for the second Hall–Janko radical

The fixed radical generators contain a hyperbolic frame at enumeration
indices 1, 28, 2 and 39, with central generators at indices 5 and 6.
Ten checked square and swap relations give the existing binary word
multiplication. Explicit preimages of the six original Seed generators
prove surjectivity, and both groups have order 64. The existing word-model
realization then identifies the native radical with literal UT₃(F₄).

The center coordinates retain the two actual central involutions. The full
normalizer comparison consumes these coordinates together with its native
conjugation action; no group-name identification is assumed.

Source: DGS, *Groups and Graphs* (1985), (10.9), printed pp.162–163;
Aschbacher, *Sporadic Groups* (1994), 46.14, printed pp.257–258.
The unchanged degree-100 ATLAS J2G1-p100B0 permutation data and Seed words
are retained in the imported carrier modules. Python supplies only the
frame witnesses; all relations used here are checked by the Lean kernel.
-/

public noncomputable section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates
open Subgroup Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData GeneratorPair.SecondOrbitCertificate
open HyperbolicRecognition HyperbolicRecognition.Intrinsic

private def element (i : Fin 64) : q₂ := ⟨qElement i,qElement_mem i⟩

private def centralChoice (r : Central) : Fin 4 :=
  if r.1 = 0 then if r.2 = 0 then 0 else 2 else if r.2 = 0 then 1 else 3

private def centralIndex (r : Central) : Fin 64 :=
  RankOneFourNormalizer.Checks.fourIndex (centralChoice r)

private theorem central_mem (r : Central) : element (centralIndex r) ∈ center q₂ := by
  obtain ⟨x,hx,he⟩ := RankOneFourNormalizer.fourElement_mem (centralChoice r)
  have hh : x = element (centralIndex r) := Subtype.ext he
  exact hh ▸ hx

set_option maxRecDepth 100000 in
private theorem central_mul_check : ∀ r s : Central,
    qTable (centralIndex (r+s)) = qTable (centralIndex r) * qTable (centralIndex s) := by
  decide +kernel

private def centralHom : Multiplicative Central →* center q₂ where
  toFun r := ⟨element (centralIndex r.toAdd),central_mem r.toAdd⟩
  map_one' := rfl
  map_mul' r s := by
    apply Subtype.ext
    apply Subtype.ext
    apply inclusion_injective
    change inclusion (qElement (centralIndex (r.toAdd+s.toAdd))) =
      inclusion (qElement (centralIndex r.toAdd) * qElement (centralIndex s.toAdd))
    rw [map_mul,qElement_inclusion,qElement_inclusion,qElement_inclusion]
    exact central_mul_check _ _

private theorem element_table (i : Fin 64) : inclusion (element i : Carrier) = qTable i :=
  qElement_inclusion i

private theorem central_table (r : Central) :
    inclusion ((centralEval centralHom r : q₂) : Carrier) = qTable (centralIndex r) :=
  qElement_inclusion _

set_option maxRecDepth 100000 in
private theorem relations : CollectionRelations centralHom alignedMatrix
    (element 1) (element 28) (element 2) (element 39) := by
  constructor <;> apply Subtype.ext <;> apply inclusion_injective <;>
    simp only [Subgroup.coe_mul,Subgroup.coe_pow,map_mul,map_pow,element_table,central_table] <;> decide +kernel

private def hom : Word alignedMatrix →* q₂ := wordHom centralHom relations

private def nativeGenWord : Fin 6 → Word alignedMatrix := ![
  ⟨((1,0),(0,0)),(0,0)⟩,
  ⟨((0,0),(1,0)),(0,0)⟩,
  ⟨((1,1),(0,1)),(1,0)⟩,
  ⟨((1,1),(1,0)),(1,0)⟩,
  ⟨((0,0),(0,0)),(1,0)⟩,
  ⟨((0,0),(0,0)),(0,1)⟩]

private def tableWord (w : Word alignedMatrix) : Equiv.Perm (Fin 100) :=
  ((qTable 1)^w.vector.1.1.val * (qTable 28)^w.vector.1.2.val) *
    ((qTable 2)^w.vector.2.1.val * (qTable 39)^w.vector.2.2.val) *
      qTable (centralIndex w.central)

private theorem hom_table (w : Word alignedMatrix) :
    inclusion (hom w : Carrier) = tableWord w := by
  change inclusion ((((element 1)^w.vector.1.1.val * (element 28)^w.vector.1.2.val) *
    ((element 2)^w.vector.2.1.val * (element 39)^w.vector.2.2.val) *
      centralEval centralHom w.central : q₂) : Carrier) = _
  simp only [Subgroup.coe_mul,Subgroup.coe_pow,map_mul,map_pow,element_table,central_table]
  rfl

set_option maxRecDepth 100000 in
private theorem native_generator_check : ∀ i : Fin 6,
    tableWord (nativeGenWord i) = qGenTable i := by
  apply allFin
  decide +kernel

private theorem native_generator (i : Fin 6) : (hom (nativeGenWord i) : Carrier) = q₂Generator i := by
  apply inclusion_injective
  rw [hom_table,q₂Generator_inclusion]
  exact native_generator_check i

private theorem hom_surjective : Function.Surjective hom := by
  have hh : q₂ ≤ (q₂.subtype.comp hom).range := by
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨nativeGenWord i,native_generator i⟩
  intro x
  obtain ⟨w,hw⟩ := hh x.property
  exact ⟨w,Subtype.ext hw⟩

private theorem centralHom_injective : Function.Injective centralHom := by
  intro r s h
  have he : qElement (centralIndex r.toAdd) = qElement (centralIndex s.toAdd) :=
    congrArg (fun z : center q₂ => ((z : q₂) : Carrier)) h
  have hi := qElement_injective he
  have hinj : Function.Injective centralIndex := by decide +kernel
  exact hinj hi

/-- The center coordinates retain the two literal native central involutions. -/
def centerEquiv : Multiplicative Central ≃* center q₂ :=
  MulEquiv.ofBijective centralHom ((Nat.bijective_iff_injective_and_card centralHom).mpr
    ⟨centralHom_injective,by
      have hc : Nat.card (center q₂) = 4 := by
        rw [←card_map_of_injective q₂.subtype_injective]
        exact RankOneFourNormalizer.card_four
      rw [hc,Nat.card_eq_fintype_card]
      decide⟩)

/-- The native second radical is the literal upper-unitriangular group over four elements. -/
def rootEquiv : q₂ ≃* Matrix.PSL3Four.RootNormalizerModel.Root :=
  (MulEquiv.ofBijective hom ((Nat.bijective_iff_surjective_and_card hom).mpr
    ⟨hom_surjective,(card_Word _).trans card_q₂.symm⟩)).symm.trans (modelEquiv 0)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates
