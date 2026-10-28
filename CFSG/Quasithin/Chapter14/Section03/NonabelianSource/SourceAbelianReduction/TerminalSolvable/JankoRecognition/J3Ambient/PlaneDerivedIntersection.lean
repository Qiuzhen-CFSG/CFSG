module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicDerivedFactor
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicNormalizer
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicCentralizer
public import Theory.SpecificGroups.GL2.FourDerived

/-!
# The original plane overlap with the canonical cubic-derived factor

The full plane/cubic-normalizer intersection is its original GL₂(4)
complement. Its actual derived A₅ is precisely the intersection with the
canonical A₆ in the cubic centralizer. Both embeddings are retained.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The shared A₅ is the literal derived subgroup of the original natural
GL₂(4) complement, inside the canonical derived A₆ of the cubic centralizer. -/
theorem literal_plane_cubic_derived_intersection
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let Z := centralizer ({j cubic} : Set G)
    let E := (_root_.commutator C).map
      ((normalizer (A : Set G)).subtype.comp C.subtype)
    normalizer (A : Set G) ⊓ (_root_.commutator Z).map Z.subtype = E ∧
      Nonempty (E ≃* alternatingGroup (Fin 5)) := by
  classical
  let s := j cubic
  let N := normalizer (A : Set G)
  let Z := centralizer ({s} : Set G)
  let V := zpowers s
  let Cg := C.map N.subtype
  let c : C →* G := N.subtype.comp C.subtype
  let E := (_root_.commutator C).map c
  let Dg := (_root_.commutator Z).map Z.subtype
  change N ⊓ Dg = E ∧ Nonempty (E ≃* alternatingGroup (Fin 5))
  have hci : Function.Injective c := N.subtype_injective.comp C.subtype_injective
  have hcr : c.range = Cg := by rw [MonoidHom.range_comp,range_subtype]
  have hCgZ : Cg ≤ Z := by
    rintro x ⟨y,hy,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (PlaneTransport.field_cubic_centralizes_complement A C l a ha j hj ⟨y,hy⟩).symm.eq
  have hEC : E ≤ Cg := by
    rintro x ⟨y,_hy,rfl⟩
    exact ⟨y,y.property,rfl⟩
  have hED : E ≤ Dg := by
    change (_root_.commutator C).map c ≤ (_root_.commutator Z).map Z.subtype
    rw [map_commutator_eq,map_commutator_eq,range_subtype,hcr]
    exact commutator_mono hCgZ hCgZ
  have hDZ : Dg ≤ Z := map_subtype_le _
  have hVC : V ≤ Cg := by
    change zpowers (j cubic) ≤ C.map (normalizer (A : Set G)).subtype
    rw [← PlaneTransport.field_cubic_normalizer_intersection A C l a hC ha j hj]
    exact le_inf (zpowers_le.mpr (hj.2.1 ⟨cubic,rfl⟩)) (zpowers (j cubic)).le_normalizer
  obtain ⟨hcomp,_⟩ := literal_cubic_derived_factor P hc A C l a ha j hj
  have hVD : Disjoint V Dg := by
    apply disjoint_def.mpr
    rintro x hx ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (disjoint_def.mp hcomp.disjoint hx hy)
  have hmap : (_root_.commutator C).map l.toMonoidHom = _root_.commutator LinearGroup := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr l.surjective]
    rfl
  obtain ⟨eGL⟩ := Representation.SL2FourNatural.SemilinearNormalizer.linear_commutator_equiv_alternatingFive
  let eE : E ≃* alternatingGroup (Fin 5) :=
    (((_root_.commutator C).equivMapOfInjective c hci).symm.trans
      (((_root_.commutator C).equivMapOfInjective l.toMonoidHom l.injective).trans
        (MulEquiv.subgroupCongr hmap))).trans eGL
  have hEc : Nat.card E = 60 := by
    rw [Nat.card_congr eE.toEquiv,Nat.card_eq_fintype_card]
    decide +kernel
  have hCc : Nat.card Cg = 180 := by
    rw [← Nat.card_congr (C.equivMapOfInjective N.subtype N.subtype_injective).toEquiv,
      Nat.card_congr l.toEquiv,Matrix.card_GL_field]
    norm_num [Representation.SL2FourNatural.card_field,Fin.prod_univ_succ]
  have hVc : Nat.card V = 3 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective j hj.1 _).trans cubic_order
  have hCE : (V.subgroupOf Cg).IsComplement' (E.subgroupOf Cg) := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv,hVc,hEc,hCc]
    · apply disjoint_def.mpr
      intro x hxV hxE
      apply Subtype.ext
      exact disjoint_def.mp hVD hxV (hED hxE)
  refine ⟨le_antisymm ?_ (le_inf (hEC.trans (map_subtype_le _)) hED),⟨eE⟩⟩
  intro x hx
  have hxC : x ∈ Cg := by
    change x ∈ C.map (normalizer (A : Set G)).subtype
    rw [← PlaneTransport.field_cubic_normalizer_intersection A C l a hC ha j hj]
    exact ⟨hx.1,cubic_centralizer_le_normalizer s (hDZ hx.2)⟩
  obtain ⟨⟨v,e⟩,hve⟩ := hCE.2 (⟨x,hxC⟩ : Cg)
  have heq : ((v : Cg) : G) * ((e : Cg) : G) = x := congrArg Subtype.val hve
  have hvD : ((v : Cg) : G) ∈ Dg := by
    have hv : ((v : Cg) : G) = x * ((e : Cg) : G)⁻¹ := by
      rw [← heq,mul_inv_cancel_right]
    rw [hv]
    exact Dg.mul_mem hx.2 (Dg.inv_mem (hED e.property))
  have hv1 : ((v : Cg) : G) = 1 := disjoint_def.mp hVD v.property hvD
  rw [hv1,one_mul] at heq
  exact heq ▸ e.property

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
