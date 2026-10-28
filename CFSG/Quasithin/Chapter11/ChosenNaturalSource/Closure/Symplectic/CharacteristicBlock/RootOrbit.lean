module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootProduct
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.MinimalParabolicSource
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.UniqueMaximalNormalExtension
/-!
# The minimal-parabolic residual in the root-image case

The action kernel on the original V lies in Q₁. The actual marked
SL₂ quotient therefore makes IQ₁ a minimal parabolic over Q₁. The
characteristic-subgroup exclusion from the original normalizers supplies
C.1.27's nonempty residual orbit of chi-zero blocks. Every quotient and
Sylow subgroup here belongs to the literal original IQ₁.

Source: Aschbacher--Smith 11.5.7, printed p.783, and C.1.27.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
open scoped Pointwise

private theorem sl2_minimal {A F : Type*} [Group A] [Finite A]
    [Field F] [Finite F] [CharP F 2]
    (q : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (S : Sylow 2 A) (hk : q.ker ≤ (S : Subgroup A)) :
    ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hu : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ :=
    hasUniqueMaximalOver_of_surjective q hq hk
      (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (S.mapSurjective hq))
  refine ⟨hu,?_⟩
  intro hn
  exact Matrix.SpecialLinearGroup.sylow_normalizer_ne_top_of_surjective q hq S (top_unique hn)

private theorem no_normal_characteristic_of_image {G : Type*} [Group G]
    (J Q I : Subgroup G) (hIJ : I ≤ J) (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype = Q)
    (hno : ∀ C : Subgroup Q, C.Characteristic → C ≠ ⊥ →
      ¬ I ≤ normalizer (C.map Q.subtype : Set G)) :
    ∀ A : Subgroup S, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (S : Subgroup J).subtype).Normal := by
  intro A hA hne hn
  let := hA
  let := hn
  let e : S ≃* Q := ((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hS)
  let C := A.map e.toMonoidHom
  have hC : C.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) z,
      characteristic_iff_le_comap.mp hA (MulAut.congr e.symm a) hz,?_⟩
    exact e.apply_symm_apply (a (e z))
  have hCne : C ≠ ⊥ := fun h => hne ((A.map_eq_bot_iff_of_injective e.injective).mp h)
  have he : C.map Q.subtype = (A.map (S : Subgroup J).subtype).map J.subtype := by
    rw [map_map,map_map]
    rfl
  apply hno C hC hCne
  rw [he]
  have hh := (A.map (S : Subgroup J).subtype).le_normalizer_map J.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hIJ.trans hh

@[expose] def RootResidualOrbit {H : Type*} [Group H] (S : Sylow 2 H) : Prop :=
  ∃ F : Set (Subgroup H), F.Nonempty ∧
    (∀ K ∈ F, ChapterC.IsChiZeroBlockIn K) ∧ sSup F = pResidual 2 H ∧
    F.Pairwise (fun K L => ⁅K,L⁆ = ⊥) ∧
    (∀ K ∈ F, ∀ t : S, K.map (MulAut.conj (t : H)).toMonoidHom ∈ F) ∧
    (∀ K ∈ F, ∀ L ∈ F, ∃ t : S, K.map (MulAut.conj (t : H)).toMonoidHom = L) ∧
    ∀ K ∈ F, K = ⁅K,Stellmacher.elementaryAbelianMaxJ (S : Subgroup H)⁆

private theorem rootResidualOrbit_of_minimal {H : Type*} [Group H] [Finite H]
    (hq : IsSQTK KnownSimple.IsKnownSimple H) (hf : generalizedFitting H = pCore 2 H)
    (S : Sylow 2 H) (hp : ChapterB.IsMinimalParabolicOver S ⊤)
    (hno : ∀ A : Subgroup S, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (S : Subgroup H).subtype).Normal) : RootResidualOrbit S :=
  ChapterC.RankOne.ChiProduct.residual_chiZero_orbit_of_characteristic_exclusion hq hf S hp hno

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

theorem root_case_minimal_of_kernel (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (g : Sp E.input.field.Carrier)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2)
    (S : Sylow 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G))
    (hS : (S : Subgroup _).map (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2).subtype =
      E.G₁.pCoreIn 2) : ChapterB.IsMinimalParabolicOver S ⊤ := by
  let I := oppositeJoin (auxiliaryW E) y
  let Q := E.G₁.pCoreIn 2
  let J := I ⊔ Q
  have hJL : J ≤ L ⊔ Q := sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  have hQN : Q ≤ normalizer (V : Set G) := (core_le_sylow E m).trans E.input.sylow_normalizes
  have hJN : J ≤ normalizer (V : Set G) := hJL.trans (sup_le D.normalizes hQN)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJN)
  have hSQ : (S : Subgroup J) = Q.subgroupOf J := by
    calc
      (S : Subgroup J) = ((S : Subgroup J).map J.subtype).subgroupOf J :=
        (subgroupOf_map_subtype_eq (S : Subgroup J)).symm
      _ = Q.subgroupOf J := congrArg (fun A : Subgroup G => A.subgroupOf J) hS
  have hJimage : actionImage (V := V) J = actionImage (V := V) I := by
    change ((I ⊔ Q).subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom = _
    rw [subgroupOf_sup (le_sup_left.trans hJN) hQN,Subgroup.map_sup]
    change actionImage (V := V) I ⊔ actionImage (V := V) Q = _
    apply sup_eq_left.mpr
    rw [hroot,←hrootW]
    exact Terminal.actionImage_mono le_sup_left
  have hrange : f.range = actionImage (V := V) I := by
    rw [←hJimage]
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hJN x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  let e := (MulEquiv.subgroupCongr hrange).trans
    (OppositeGeometry.markedPairImageEquiv E m g hpair)
  let q := e.toMonoidHom.comp f.rangeRestrict
  apply sl2_minimal q (e.surjective.comp f.rangeRestrict_surjective) S
  intro x hx
  rw [hSQ]
  apply hkernel
  refine ⟨?_,hJL x.property⟩
  have hx0 : f x = 1 := by
    have hh : e (f.rangeRestrict x) = 1 := hx
    exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
  change V.normalizerMonoidHom (inclusion hJN x) = 1 at hx0
  rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker] at hx0
  exact hx0

theorem root_case_residual_orbit_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    ∃ (g' : Sp E.input.field.Carrier) (y : L),
      let J : Subgroup G := oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g').toMonoidHom).map (FullAction.modelHom m) ∧
      ∃ S : Sylow 2 J,
        (S : Subgroup J).map J.subtype = E.G₁.pCoreIn 2 ∧
        ChapterB.IsMinimalParabolicOver S ⊤ ∧ RootResidualOrbit S := by
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  obtain ⟨hV,hW,hU,hrootW,hmove,_,hPhi,_⟩ :=
    RadicalAction.initial_branch_of_preceding E m g hpoint hthree hcartan hXL hXG
      hn3 hirr hti hgen hVX hfour hfive hne
  have hcore := NaturalQuotient.core_le_point_core E m hX hV hW hrootW hmove hPhi
    hfour hfive hti (CoverGeometry.radical_commutator m g hpoint hthree) hgen
  have hkernel := core_join_action_kernel_of_root_image E m g hpoint hcartan hXL hXG hcore hroot
  obtain ⟨g',y,hpair,S,hS,hq,hf,hno⟩ := root_case_inputs_of_preceding
    (G := G) (T := T) (L := L) (V := V) (D := D) E m g hpoint hthree
    hX hcartan hn3 hirr hti hgen hVX hfour hfive hout hne hroot
  have hp := root_case_minimal_of_kernel E m hW y.property g' hpair hrootW hroot hkernel S hS
  refine ⟨g',y,hpair,S,hS,hp,?_⟩
  apply rootResidualOrbit_of_minimal hq hf S hp
  exact no_normal_characteristic_of_image _ _ _ le_sup_left S hS hno

/-- C.1.27 for the specified original opposite pair; in particular its
Cartan marking need not be discarded by a new existential choice. -/
theorem root_case_residual_orbit_of_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    ∃ S : Sylow 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G),
      (S : Subgroup _).map (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2).subtype =
        E.G₁.pCoreIn 2 ∧ ChapterB.IsMinimalParabolicOver S ⊤ ∧ RootResidualOrbit S := by
  obtain ⟨S,hS,hq,hf,hno⟩ := root_case_structure_of_pair E m hout hV hW hy g hlocal hpair hroot hkernel
  have hp := root_case_minimal_of_kernel E m hW hy g hpair hrootW hroot hkernel S hS
  refine ⟨S,hS,hp,?_⟩
  apply rootResidualOrbit_of_minimal hq hf S hp
  exact no_normal_characteristic_of_image _ _ _ le_sup_left S hS hno

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
