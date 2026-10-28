module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointResidual
public import Theory.Representation.HexacodeAction.FullWeightVectorNonsplit
public import Theory.Representation.BinaryConjugationSection.Generation
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The original whole module lies in its triple-six point residual

The literal chart is a binary conjugation section with zero kernel.
The full-weight vector-stabilizer calculation therefore lifts its complete
commutator span to the original subgroup U. The actual point-centralizer
projection maps its two-residual onto the perfect A5 vector stabilizer,
so the same argument gives U=[U,Lt]. Since U lies in the original point
centralizer, it normalizes Lt, and the commutator identity puts U in Lt.

This proves the generation and containment in Aschbacher--Smith12.7.4(3),
printed p.840, retaining the original G,K,U,t and the whole chosen module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private def chartSection (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    BinaryConjugationSection K U ⊥
      (Hexacode.evenAction.comp (a.groupEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 K)))) where
  section_le := D.le_component
  kernel_le := bot_le
  normalized := D.normalizes
  coordinates := (tripleSixPointCoordinates D a).toMonoidHom
  onto := (tripleSixPointCoordinates D a).surjective
  kernel_eq := by
    rw [bot_subgroupOf]
    exact ((tripleSixPointCoordinates D a).toMonoidHom.ker_eq_bot_iff).mpr
      (tripleSixPointCoordinates D a).injective
  equivariant k u := by
    have h := tripleSixPointCoordinates_conjugate D a k u
    have hs : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
        (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
          (tripleSixPointCoordinates D a u).toAdd)) =
        ⟨(k : G) * u * (k : G)⁻¹,
          (mem_normalizer_iff.mp (D.normalizes k.property) u).mp u.property⟩ :=
      Subtype.ext h
    have he := congrArg (tripleSixPointCoordinates D a) hs
    rw [MulEquiv.apply_symm_apply] at he
    exact (congrArg Multiplicative.toAdd he).symm

private theorem commutator_eq_of_full_actor (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (A : Subgroup G) (hAC : A ≤ K ⊓ centralizer ({(t : G)} : Set G))
    (himage : (A.subgroupOf (K ⊓ centralizer ({(t : G)} : Set G))).map
      (tripleSixPointCentralizerProjection D a t) = ⊤) : U = ⁅U,A⁆ := by
  let s := chartSection D a
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let q := tripleSixPointCentralizerProjection D a t
  let v := (tripleSixPointCoordinates D a t).toAdd
  have hAK : A ≤ K := hAC.trans inf_le_left
  have hP := tripleSixPoint_full_weight D a t ht heven
  have hv : v ≠ 0 := by
    intro hz
    have hh : tripleSixPointCoordinates D a t = 1 := hz
    exact ht ((tripleSixPointCoordinates D a).injective
      (hh.trans (map_one _).symm))
  have hweight : hammingNorm v.val = 6 :=
    hP.2.2 ⟨v,Submodule.mem_span_singleton_self v⟩
      (fun h => hv (congrArg Subtype.val h))
  have hspan : subspaceCommutator Hexacode.evenAction ⊤
      (Hexacode.fullWeightVectorStabilizer v) ≤ s.image ⁅U,A⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,w,_,rfl⟩
    obtain ⟨c,hc,hcg⟩ := show (⟨g,hg⟩ : Hexacode.fullWeightVectorStabilizer v) ∈
        (A.subgroupOf C).map q by rw [himage]; trivial
    have hm := s.coinvariants_le_image_commutator A hAK
      (Coinvariants.sub_mem_ker
        (ρ := (Hexacode.evenAction.comp (a.groupEquiv.toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 K)))).comp (inclusion hAK)) (⟨c.val,hc⟩ : A) w)
    change Hexacode.evenAction
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c.val,hAK hc⟩)) w - w ∈ _ at hm
    have he : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c.val,hAK hc⟩) = g :=
      congrArg Subtype.val hcg
    rwa [he] at hm
  have hfull : s.image ⁅U,A⁆ = ⊤ := by
    apply top_unique
    rw [← Hexacode.fullWeightVectorStabilizer_commutator v hweight]
    exact hspan
  apply le_antisymm
  · simpa using s.le_sup_kernel_of_image_top ⁅U,A⁆ hfull
  · exact le_normalizer_iff_commutator_le_left.mp (hAK.trans D.normalizes)

/-- The original point centralizer generates the whole original module. -/
theorem tripleSixPointCentralizer_commutator (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    U = ⁅U, K ⊓ centralizer ({(t : G)} : Set G)⁆ := by
  apply commutator_eq_of_full_actor D a t ht heven _ le_rfl
  rw [subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (tripleSixPointCentralizerProjection_surjective D a t)]

/-- The literal two-residual Lt already generates the whole original module,
and consequently contains it. -/
theorem tripleSixPointCentralizerResidual_commutator (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    let C := K ⊓ centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 C).map C.subtype
    U = ⁅U,Lt⁆ ∧ U ≤ Lt := by
  dsimp only
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  let v := (tripleSixPointCoordinates D a t).toAdd
  let q := tripleSixPointCentralizerProjection D a t
  have hv : v ≠ 0 := by
    intro hz
    have hh : tripleSixPointCoordinates D a t = 1 := hz
    exact ht ((tripleSixPointCoordinates D a).injective
      (hh.trans (map_one _).symm))
  have hP := tripleSixPoint_full_weight D a t ht heven
  let e := Hexacode.fullWeightVectorStabilizerEquiv v hv hP
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Hexacode.fullWeightVectorStabilizer v) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have himage : (Lt.subgroupOf C).map q = ⊤ := by
    rw [show Lt.subgroupOf C = pResidual 2 C from
      comap_map_eq_self_of_injective C.subtype_injective _,
      map_pResidual_of_surjective 2 q (tripleSixPointCentralizerProjection_surjective D a t)]
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (Hexacode.fullWeightVectorStabilizer v ⧸ N) :=
      QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (Hexacode.fullWeightVectorStabilizer v ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (Hexacode.fullWeightVectorStabilizer v ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Hexacode.fullWeightVectorStabilizer v ⧸ N)
      _root_.IsNilpotent.to_isSolvable
  have hcomm : U = ⁅U,Lt⁆ := commutator_eq_of_full_actor D a t ht heven Lt
    (map_subtype_le _) himage
  have hUC : U ≤ C := by
    intro u hu
    refine ⟨D.le_component hu, mem_centralizer_singleton_iff.mpr ?_⟩
    let := D.elementary
    exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) t)
  refine ⟨hcomm, ?_⟩
  exact hcomm.le.trans (le_normalizer_iff_commutator_le_right.mp
    (hUC.trans (le_normalizer_embedded_pResidual 2 C)))

end CFSG.Quasithin.Chapter12.Section07
