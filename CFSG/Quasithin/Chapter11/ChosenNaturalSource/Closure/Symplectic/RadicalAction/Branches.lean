module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.ActionOperations
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.LocalIdentification

/-!
# Closure assembly from the two original action comparisons

The native point-radical lattice has already been transported to Aut(V).
A nonabelian U must move V₃. Its image is neither zero nor the local root,
so it is the full radical, giving [V,U]=V₃, contrary to [V,U]≤V₁.
Once U is abelian, both choices of the auxiliary W fix V₃ and have nonzero
image under the contradiction hypothesis. The lattice and hyperplane-fixer
bound force precisely the root image. Its full-cover displacement gives
[V,W]=V₁; conjugate generation gives Φ(W_H)≤V₁, whereas Φ(U)=1.

All subgroups and maps are the original ones. The ambient radical-image
bound and the full-cover commutator/fixer comparisons remain explicit,
separate obligations. This conditional assembly is not yet a proof of the
initial source branch until those inputs have been discharged.
Source: Aschbacher--Smith 11.5.7, printed pp.782--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hR : actionImage (V := V) E.R₁ ≤ actionImage (V := V) (E.L₁.pCoreIn 2))

include hlocal hcartan hXL hXG hR in
private theorem core_subgroup_lattice (A : Subgroup G)
    (hA : A ≤ E.G₁.pCoreIn 2) (hn : E.G₁ ≤ normalizer (A : Set G)) :
    actionImage (V := V) A = ⊥ ∨
      actionImage (V := V) A = (center (actionImage (V := V) E.L₁)).map
        (actionImage (V := V) E.L₁).subtype ∨
      actionImage (V := V) A = actionImage (V := V) (E.L₁.pCoreIn 2) := by
  apply FullAction.invariant_lattice m g hlocal hcartan hXL
  · exact (image_mono (hA.trans (core_le_local_radical E m))).trans hR
  · exact image_normalizes A (E.L₁ ⊔ E.X) ((sup_le ((residualIn_le _).trans inf_le_right) hXG).trans hn)

include hlocal hcartan hXL hXG hR in
/-- The full radical alternative contradicts [V,U]≤V₁. The zero and root
alternatives centralize the original V₃, so its G₁-closure is abelian.
The explicit action comparisons are discharged by the ambient normalizer
and central-cover producers, not by this group-theoretic assembly. -/
theorem U_abelian_of_action_comparisons
    (hV : V ≤ E.G₁.pCoreIn 2) (hU : E.U ≤ E.G₁.pCoreIn 2)
    (hc : ⁅E.U,E.G₁.pCoreIn 2⁆ ≤ E.V₁)
    (hroot : ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥)
    (hmove : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃) : IsMulCommutative E.U := by
  have hnU : E.U ≤ normalizer (V : Set G) :=
    hU.trans (core_normalizes_seed E m E.input.sylow_normalizes)
  have hnroot : FullAction.rootPreimage (E := E) ≤ normalizer (V : Set G) :=
    FullAction.rootPreimage_le.trans D.normalizes
  have hncore : E.L₁.pCoreIn 2 ≤ normalizer (V : Set G) :=
    ((pCoreIn_le 2 E.L₁).trans E.L₁_le).trans D.normalizes
  apply (conjugateSpanBy_commutative_iff E.V₃ E.G₁).mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  change ⁅E.V₃,E.U⁆ = ⊥
  rcases core_subgroup_lattice E m g hlocal hcartan hXL hXG hR E.U hU
    (closure_normalizations E).1 with hz | hz | hz
  · have hu := (actionImage_eq_bot_iff E.U hnU).mp hz
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hu.trans (centralizer_le (D.centralQuotientPreimage_le E.threeSpace))))
  · rw [commutator_eq_of_image_eq E.U (FullAction.rootPreimage (E := E)) E.V₃
      (D.centralQuotientPreimage_le E.threeSpace) hnU hnroot
      (hz.trans (FullAction.rootPreimage_image m).symm), hroot]
  · have he : ⁅V,E.U⁆ = E.V₃ :=
      (commutator_eq_of_image_eq E.U (E.L₁.pCoreIn 2) V le_rfl hnU hncore hz).trans hmove
    have hle : E.V₃ ≤ E.V₁ := by
      rw [← he, commutator_comm]
      exact (commutator_mono le_rfl hV).trans hc
    exact (m.point_lt_threeSpace.not_ge hle).elim

/-- Both choices of the auxiliary W centralize the original V₃, once U is
abelian. In the W_H branch normality propagates [V,U]=1 to [W_H,U]=1. -/
theorem auxiliaryW_fixes_threeSpace (hu : IsMulCommutative E.U) :
    ⁅E.V₃,auxiliaryW E⁆ = ⊥ := by
  classical
  unfold auxiliaryW
  split_ifs with hc
  · exact threeSpace_centralizes_W_of_U_centralizes_seed E hc
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (le_conjugateSpanBy E.V₃ E.G₁).trans (le_centralizer_iff_isMulCommutative.mpr hu)

include m in
/-- Under the contradiction hypothesis, either definition of W has nonzero
original action image. -/
theorem auxiliaryW_image_ne_bot (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hne : ¬ IsMulCommutative E.W) : actionImage (V := V) (auxiliaryW E) ≠ ⊥ := by
  classical
  unfold auxiliaryW
  split_ifs with hc
  · exact W_actionImage_ne_bot_of_nonabelian E m E.input.sylow_normalizes hW hne
  · intro hz
    apply hc
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (actionImage_eq_bot_iff E.U ?_).mp hz
    exact (closure_containments E m).2.1.trans
      (hW.trans (core_normalizes_seed E m E.input.sylow_normalizes))

include hlocal hcartan hXL hXG hR in
/-- The native invariant lattice and the actual V₃-fixer bound determine the
nontrivial auxiliary image uniquely as the local center. -/
theorem auxiliaryW_image_eq_center (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hne : ¬ IsMulCommutative E.W) (hu : IsMulCommutative E.U)
    (hfix : actionImage (V := V) E.R₁ ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  obtain ⟨_,hc,hn⟩ := auxiliaryW_containment_and_normalization E hW
  have haN := hc.trans (core_normalizes_seed E m E.input.sylow_normalizes)
  have hle := (le_inf (image_mono (hc.trans (core_le_local_radical E m)))
    ((image_le_fixer_iff (auxiliaryW E) E.V₃ (D.centralQuotientPreimage_le _) haN).mpr
      (auxiliaryW_fixes_threeSpace E hu))).trans hfix
  rcases core_subgroup_lattice E m g hlocal hcartan hXL hXG hR (auxiliaryW E) hc hn
    with hz | hz | hz
  · exact (auxiliaryW_image_ne_bot E m hW hne hz).elim
  · exact hz
  · rw [hz] at hle
    exact ((FullAction.chief_series m g hlocal).2.not_ge hle).elim

include hlocal hcartan hXL hXG hR in
/-- The complete auxiliary conclusion from the two independent action
comparisons. The U branch uses Φ(U)=1, correcting the printed equality. -/
theorem auxiliaryW_properties_of_action_comparisons
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hU : E.U ≤ E.G₁.pCoreIn 2) (hc : ⁅E.U,E.G₁.pCoreIn 2⁆ ≤ E.V₁)
    (hroot : ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥)
    (hmove : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃)
    (hrootmove : ⁅V,FullAction.rootPreimage (E := E)⁆ = E.V₁)
    (hfix : actionImage (V := V) E.R₁ ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hne : ¬ IsMulCommutative E.W) :
    IsMulCommutative E.U ∧
    actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∧
    ⁅V,auxiliaryW E⁆ = E.V₁ ∧ ⁅E.V₃,auxiliaryW E⁆ = ⊥ ∧
    (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁ ∧
    auxiliaryW E ≤ E.W ∧ auxiliaryW E ≤ E.G₁.pCoreIn 2 ∧
    E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  have hu := U_abelian_of_action_comparisons E m g hlocal hcartan hXL hXG hR
    hV hU hc hroot hmove
  have him := auxiliaryW_image_eq_center E m g hlocal hcartan hXL hXG hR hW hne hu hfix
  have hb := auxiliaryW_containment_and_normalization E hW
  have hm : ⁅V,auxiliaryW E⁆ = E.V₁ := by
    rw [commutator_eq_of_image_eq (auxiliaryW E) (FullAction.rootPreimage (E := E)) V
      le_rfl (hb.2.1.trans (core_normalizes_seed E m E.input.sylow_normalizes))
      (FullAction.rootPreimage_le.trans D.normalizes)
      (him.trans (FullAction.rootPreimage_image m).symm)]
    exact hrootmove
  refine ⟨hu,him,hm,auxiliaryW_fixes_threeSpace E hu,?_,hb⟩
  classical
  by_cases hcomm : ⁅V,E.U⁆ = ⊥
  · have he : auxiliaryW E = E.W := by unfold auxiliaryW; exact if_pos hcomm
    rw [he] at hm ⊢
    exact closure_frattini_le_point E m hW hm.le
  · have he : auxiliaryW E = E.U := by unfold auxiliaryW; exact if_neg hcomm
    rw [he, U_frattini_eq_bot E hu]
    exact bot_le

/-- The full source M_V-fixer gives the fixer bound actually used on R₁.
Its containment follows from the original Sylow and both normalizations. -/
theorem local_fixer_bound_of_ambient
    (hfix : actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    actionImage (V := V) E.R₁ ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  apply le_trans _ hfix
  apply inf_le_inf_right
  apply image_mono
  exact (LocalGeometry.localRadical_le_sylow E.V₁).trans
    (le_inf D.sylow_normalizes_component E.input.sylow_normalizes)

include m in
/-- Source assertion (!), with its full actual M_V action and central
attachment retained, assembled from the upper fixer bound and cover fixation. -/
theorem ambient_fixer_eq_center
    (hfix : actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥) :
    actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) =
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  apply le_antisymm hfix
  rw [← FullAction.rootPreimage_image m]
  apply le_inf
  · exact image_mono (FullAction.rootPreimage_le.trans
      (le_inf L.le_normalizer D.normalizes))
  · exact (image_le_fixer_iff _ E.V₃ (D.centralQuotientPreimage_le _)
      (FullAction.rootPreimage_le.trans D.normalizes)).mpr hroot

include hcartan hXL hXG hR in
/-- Application to the exact preceding closure and Cartan conclusions. This
supplies all core premises internally. Only the independent original-action
comparisons remain to be discharged in this branch's final assembly. -/
theorem initial_branch_of_preceding_and_action_comparisons
    (hpoint : m.flag.space 0 =
      (point E.input.field.Carrier).map (toLinear g).toLinearMap)
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
    (hroot : ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥)
    (hmove : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃)
    (hrootmove : ⁅V,FullAction.rootPreimage (E := E)⁆ = E.V₁)
    (hfix : actionImage (V := V) (E.M ⊓ normalizer (V : Set G)) ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
    actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∧
    ⁅V,auxiliaryW E⁆ = E.V₁ ∧ ⁅E.V₃,auxiliaryW E⁆ = ⊥ ∧
    (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁ ∧
    auxiliaryW E ≤ E.W ∧ auxiliaryW E ≤ E.G₁.pCoreIn 2 ∧
    E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  obtain ⟨hV,hW,hU,_,hc⟩ := initial_core_bounds E m hn3 hirr hti hgen hVX hfour hfive
  have hlocal := PointModel.local_identification m g hpoint
  exact ⟨hV,hW,auxiliaryW_properties_of_action_comparisons E m g hlocal hcartan hXL hXG hR
    hV hW hU hc hroot hmove hrootmove (local_fixer_bound_of_ambient E hfix) hne⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction
