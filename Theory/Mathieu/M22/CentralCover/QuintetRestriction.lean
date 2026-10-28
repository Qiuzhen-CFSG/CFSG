module
public import Theory.Mathieu.M22.CentralCover.AffinePairRestriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Displacement

/-!
# The literal native quintet actor in a central double cover of M₂₂

The coordinate-zero hexacode and its local letter kernel give the entire
native tetrad-pointwise actor its natural affine marking over F₄. Its
embedding in degree-22 M₂₂ retains the original inclusion into the outer
pair stabilizer. The two undeleted tetrad points put this actual order-960
image in a pair stabilizer of order 1920.

Consequently every perfect central double cover restricts to this native
actor with perfect full preimage and elementary two-core of order 32. The
whole core is its commutator with the preimage, the local orientation used
in Aschbacher--Smith 8.2.10(3), printed p.721, from I.2.2(3b),(6), pp.410,412.
The native coordinates reuse the licensed ATLAS results documented in
`ChapterHLocalClassification.Quintet.Natural`.
-/

public section
noncomputable section
open Subgroup Representation Atlas.Codes MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Quintet

/-- The complete native affine model, using the same coordinates as its natural action. -/
def naturalActorAffineEquiv : naturalActor ≃* Matrix.SL2.Affine Matrix.PSL3Four.F :=
  naturalActorEquiv.symm.trans
    (SemidirectProduct.congr
      ((Hexacode.ZeroNatural.vectorCoordinates.trans SL2FourNatural.standardVectorEquiv).toAddEquiv.toMultiplicative)
      (Hexacode.ZeroNatural.modelEquiv.trans SL2FourNatural.standardGroupEquiv)
      (fun a => by
        apply MulEquiv.ext
        intro v
        apply Multiplicative.toAdd.injective
        change SL2FourNatural.standardVectorEquiv
          (Hexacode.ZeroNatural.vectorCoordinates (hexZeroLinear naturalIndex a.val v.toAdd)) = _
        rw [← Hexacode.ZeroNatural.matrixAction_equivariant, SL2FourNatural.standard_equivariant]
        rfl))

private theorem pairEmbedding_injective : Function.Injective m22ToPairStabilizer := by
  intro a b h
  exact m22Embedding_injective (congrArg Subtype.val h)

/-- The original native actor regarded in degree-22 M22, without an arbitrary conjugator. -/
def nativeActorMap : naturalActor →* M22 :=
  (MonoidHom.ofInjective pairEmbedding_injective).symm.toMonoidHom.comp {
    toFun a := ⟨a.val.val, naturalActor_inner a⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

theorem nativeActorMap_pair (a : naturalActor) :
    m22ToPairStabilizer (nativeActorMap a) = a.val.val :=
  MonoidHom.apply_ofInjective_symm pairEmbedding_injective _

theorem nativeActorMap_injective : Function.Injective nativeActorMap := by
  intro a b h
  have he : a.val.val = b.val.val := by
    rw [← nativeActorMap_pair, ← nativeActorMap_pair, h]
  exact Subtype.ext (Subtype.ext he)

/-- The actual native degree-22 image of the tetrad-pointwise actor. -/
def nativeActor : Subgroup M22 := nativeActorMap.range

/-- Equality of literal images in the outer pair stabilizer. -/
theorem nativeActor_map_pair : nativeActor.map m22ToPairStabilizer =
    naturalActor.map MathieuCode.M22Quintet.Q.subtype := by
  ext g
  constructor
  · rintro ⟨x,⟨a,rfl⟩,rfl⟩
    exact ⟨a.val,a.property,(nativeActorMap_pair a).symm⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨nativeActorMap ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,nativeActorMap_pair _⟩

def nativeActorAffineEquiv : nativeActor ≃* Matrix.SL2.Affine Matrix.PSL3Four.F :=
  (MonoidHom.ofInjective nativeActorMap_injective).symm.trans naturalActorAffineEquiv

theorem nativeActor_card : Nat.card nativeActor = 960 := by
  change Nat.card nativeActorMap.range = 960
  rw [← Nat.card_congr (MonoidHom.ofInjective nativeActorMap_injective).toEquiv,
    ← Nat.card_congr naturalActorEquiv.toEquiv]
  exact tetradPointAffine_card _

private theorem nativeActor_pair_placement :
    ∃ J : Subgroup M22, Nat.card J = 1920 ∧ nativeActor ≤ J := by
  have hm (k : Fin 4) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
      ∃ i : Fin 22, m22Coordinates i = naturalPointCoordinates (naturalIndex,k) := by
    obtain h | h | h := pairResidual_coordinates_cover (naturalPointCoordinates (naturalIndex,k))
    · exact False.elim (hk0 (congrArg Prod.snd (naturalPointCoordinates.injective
        (h.trans naturalPointCoordinates_zero.symm))))
    · exact False.elim (hk1 (congrArg Prod.snd (naturalPointCoordinates.injective
        (h.trans naturalPointCoordinates_nine.symm))))
    · exact h
  obtain ⟨x,hx⟩ := hm 2 (by decide) (by decide)
  obtain ⟨y,hy⟩ := hm 3 (by decide) (by decide)
  have hxy : x ≠ y := by
    intro he
    have hh := naturalPointCoordinates.injective (hx.symm.trans ((congrArg m22Coordinates he).trans hy))
    exact (by decide : (2 : Fin 4) ≠ 3) (congrArg Prod.snd hh)
  refine ⟨MulAction.stabilizer M22 ({x,y} : Finset (Fin 22)), ?_, ?_⟩
  · obtain ⟨g,hg1,hg2⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
      (by decide : (1 : Fin 22) ≠ 2) hxy
    have hg : g • m22Pair12 = ({x,y} : Finset (Fin 22)) := by
      rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, ←hg1, ←hg2]
    exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
      m22PairStabilizer_card
  · rintro _ ⟨a,rfl⟩
    have hf (i : Fin 22) (k : Fin 4) (hi : m22Coordinates i = naturalPointCoordinates (naturalIndex,k)) :
        nativeActorMap a • i = i := by
      apply m22Coordinates.injective
      rw [←m22Embedding_apply,hi]
      have he : m22Embedding (nativeActorMap a) = a.val.val.val :=
        congrArg Subtype.val (nativeActorMap_pair a)
      rw [he]
      exact (mem_naturalActor_iff a.val).mp a.property k
    change nativeActorMap a • ({x,y} : Finset (Fin 22)) = _
    rw [Finset.smul_finset_insert,Finset.smul_finset_singleton,hf x 2 hx,hf y 3 hy]

/-- The full native actor preimage retains perfectness and the binary kernel. -/
theorem nativeActor_preimage_isPerfect {K : Type*} [Group K] [Finite K]
    (c : PerfectCentralCovering.Cover K M22) (hk : Nat.card c.toMonoidHom.ker = 2) :
    Group.IsPerfect (nativeActor.comap c.toMonoidHom) := by
  let : Group.IsPerfect nativeActor := Matrix.SL2.isPerfect_of_equiv_affine _
    (by rw [Matrix.PSL3Four.card_F]) nativeActorAffineEquiv
  obtain ⟨J,hJ,hBJ⟩ := nativeActor_pair_placement
  exact M22CentralCover.perfect_pair_half_preimage c hk J nativeActor hJ
    nativeActor_card hBJ

/-- The original central double cover restricts to the native actor with the full
elementary five-space as its local commutator. -/
theorem nativeActor_preimage_core {K : Type*} [Group K] [Finite K]
    (c : PerfectCentralCovering.Cover K M22) (hk : Nat.card c.toMonoidHom.ker = 2) :
    let P := nativeActor.comap c.toMonoidHom
    IsElementaryAbelian 2 (pCore 2 P) ∧
      ⁅pCore 2 P, (⊤ : Subgroup P)⁆ = pCore 2 P ∧ Nat.card (pCore 2 P) = 32 := by
  obtain ⟨J,hJ,hBJ⟩ := nativeActor_pair_placement
  exact M22CentralCover.affine_pair_half_preimage_core c hk J nativeActor hJ
    nativeActor_card hBJ nativeActorAffineEquiv

end Sporadic.Mathieu.M22ChapterH.Quintet
