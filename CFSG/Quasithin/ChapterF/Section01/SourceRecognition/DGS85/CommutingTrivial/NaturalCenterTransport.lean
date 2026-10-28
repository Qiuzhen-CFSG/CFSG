module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ExtendedCartanKernels

/-!
# Transporting the natural center to the middle vertex

The actual conjugating element induces compatible isomorphisms on the local
actor, its core quotient and the center. Pulling coordinates through these
maps transports the natural section without identifying separate fields or
changing the quotient map. The reduced application combines its order with
the existing neighboring-center theorem to obtain Z_x = Z_beta Z_d.

Source: DGS, *Groups and Graphs* (1985), printed p.150, the natural middle
center used in the final 9.10 contradiction.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Transport a natural center through the literal graph conjugation. -/
theorem graph_natural_center_transport
    (h : LocallyRankOneTriple P B) {v w : Vertex (family P)}
    (g : G) (hg : g • v = w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (cv : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      BinaryConjugationSection (graphLocalGroup (family P) v) (Z (family P) v) ⊥
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp
          (ev.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))))) :
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F),
      Nonempty (BinaryConjugationSection (graphLocalGroup (family P) w) (Z (family P) w) ⊥
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp
          (ew.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) w)))))) := by
  let Γ := family P
  let : ∀ i, Finite (Γ i) := finite_endpoints h
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨e,f,he,hf,_⟩ := local_quotient_parameter_transport h g hg
  let ew := f.symm.trans ev
  have hZ : (Z Γ v).map (MulAut.conj g).toMonoidHom = Z Γ w := by
    rw [←Z_translate,hg]
  let z : Z Γ v ≃* Z Γ w :=
    ((Z Γ v).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hZ)
  have hz (a : Z Γ v) : (z a : G) = g*(a:G)*g⁻¹ := rfl
  have hcoord (l : graphLocalGroup Γ v) :
      ew (QuotientGroup.mk' _ (e l)) = ev (QuotientGroup.mk' _ l) := by
    change ev (f.symm (QuotientGroup.mk' _ (e l))) = _
    rw [←hf,f.symm_apply_apply]
  have hn : graphLocalGroup Γ w ≤ normalizer (Z Γ w : Set G) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ w)
  refine ⟨ew,⟨{
    section_le := ((source_Z_Q_U h w).1.trans (map_subtype_le _)).trans
      (core_le_graphLocalGroup h w)
    kernel_le := bot_le
    normalized := hn
    coordinates := cv.coordinates.comp z.symm.toMonoidHom
    onto := cv.onto.comp z.symm.surjective
    kernel_eq := ?_
    equivariant := ?_ }⟩⟩
  · ext a
    change cv.coordinates (z.symm a) = 1 ↔ (a : G) ∈ (⊥ : Subgroup G)
    rw [cv.coordinates_eq_one_iff,mem_bot,mem_bot]
    constructor
    · intro hh
      have hh' : z.symm a = 1 := Subtype.ext hh
      have hh'' := congrArg z hh'
      rw [z.apply_symm_apply,map_one] at hh''
      exact congrArg Subtype.val hh''
    · intro hh
      have hh' : a = 1 := Subtype.ext hh
      rw [hh',map_one]
      rfl
  · intro l a
    obtain ⟨k,rfl⟩ := e.surjective l
    obtain ⟨b,rfl⟩ := z.surjective a
    let b' : Z Γ v := ⟨(k:G)*b*(k:G)⁻¹,
      (mem_normalizer_iff.mp (cv.normalized k.property) b).mp b.property⟩
    have hb' : (z b' : G) = (e k : G)*(z b : G)*(e k : G)⁻¹ := by
      rw [hz,hz,he]
      change g*((k:G)*(b:G)*(k:G)⁻¹)*g⁻¹ = _
      group
    have ht : z.symm ⟨(e k : G)*(z b : G)*(e k : G)⁻¹,
        (mem_normalizer_iff.mp (hn (e k).property) (z b)).mp (z b).property⟩ = b' := by
      apply z.injective
      rw [z.apply_symm_apply]
      exact Subtype.ext hb'.symm
    change (cv.coordinates (z.symm _)).toAdd =
      Matrix.mulVec (ew (QuotientGroup.mk' _ (e k))).val
        (cv.coordinates (z.symm (z b))).toAdd
    rw [ht,z.symm_apply_apply,hcoord]
    exact cv.equivariant k b

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Transport the original natural center to x and construct its actual neighboring-line split. -/
theorem reduced_middle_natural_center
    (h : HypothesisF11 L S)
    {a x beta d : Vertex (Reduction.reducedFamily L S)}
    (g : Reduction.G₀ L S) (hg : g • a = x)
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (ea : (graphLocalGroup (Reduction.reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a)) ≃* SL(2,K))
    (ca : letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      BinaryConjugationSection (graphLocalGroup (Reduction.reducedFamily L S) a)
        (Z (Reduction.reducedFamily L S) a) ⊥
        (((specialLinearNatural (k := K) 2).restrictScalars (k := ZMod 2)).comp
          (ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2
            (graphLocalGroup (Reduction.reducedFamily L S) a))))))
    (hωd : Z (Reduction.reducedFamily L S) d =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) d))
    (hZcardd : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card K) :
    let Γ := Reduction.reducedFamily L S
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    ∃ ex : (graphLocalGroup Γ x ⧸ pCore 2 (graphLocalGroup Γ x)) ≃* SL(2,K),
      Nonempty (BinaryConjugationSection (graphLocalGroup Γ x) (Z Γ x) ⊥
        (((specialLinearNatural (k := K) 2).restrictScalars (k := ZMod 2)).comp
          (ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ x)))))) ∧
      Nat.card (Z Γ x) = Nat.card K ^ 2 ∧ Z Γ x = Z Γ beta ⊔ Z Γ d := by
  let Γ := Reduction.reducedFamily L S
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨ex,⟨cx⟩⟩ := graph_natural_center_transport (Reduction.reduced_triple h) g hg ea ca
  have hxcard : Nat.card (Z Γ x) = Nat.card K ^ 2 := by
    have hh := cx.card_section
    simp only [Nat.card_fun,Nat.card_fin,card_bot,mul_one] at hh
    exact hh
  refine ⟨ex,⟨cx⟩,hxcard,?_⟩
  simpa only [sup_comm] using
    (reduced_natural_neighbor_centers_split h hd hb hne.symm hωd hxcard hZcardd).1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
