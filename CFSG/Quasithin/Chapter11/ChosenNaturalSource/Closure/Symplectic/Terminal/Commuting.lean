module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Algebra
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.Commutator.PerfectCoreKernel
public import Theory.ThreeSubgroups

/-!
# The commuting branch of the symplectic closure argument

Perfectness of the actual solvable residual L₁ improves the root-action
bound [W_H,L₁] ≤ O₂(L)=V to [W_H,L₁] ≤ V₃. Relative normal generation
then propagates this bound to K, without identifying K with L₁.
The supplement Y normalizes L₁ by its actual quotient-kernel action and
the perfect residual argument. In the commuting branch it consequently
normalizes V₃=[W_H,L₁]. The preceding normalizer control of 11.1.4 puts Y
in M₁, whose TI action preserves V. This supplies the missing supplement
action and proves W_H=UV from the actual equation G₁=KYM₁.

Source: Aschbacher--Smith 11.5.7, printed p.783, commuting terminal branch.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

include E in
private theorem centralizer_in_component_le_core :
    L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  rintro x ⟨hx,hc⟩
  let l : L := ⟨x,hx⟩
  have he : D.chosenCentralAction l = 1 := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      have hv : (v.val.toMul.val : G) ∈ V :=
        D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have hvfix : D.chosenAction l v = v := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change x * (v.val.toMul.val : G) * x⁻¹ = (v.val.toMul.val : G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) _ hv).symm
      change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
      rw [hvfix]
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := by
    apply E.input.faithful
    rw [D.centralQuotientAction_mk, map_one]
    exact he
  exact mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff l).mp hq)

/-- The central root action really gives the core commutator bound: W_H
normalizes L through its original Sylow containment, and the action kernel
inside L is detected by the faithful chosen central quotient. -/
theorem root_action_commutator_le_core (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) E.W ≤
      centralizer (actionImage (V := V) E.L₁ : Set (MulAut V))) :
    ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2 := by
  have hWT : E.W ≤ (T : Subgroup G) :=
    (closure_le_R₁ E m hW).trans (LocalGeometry.localRadical_le_sylow E.V₁)
  have hWN : E.W ≤ normalizer (V : Set G) := hWT.trans E.input.sylow_normalizes
  have hLN : E.L₁ ≤ normalizer (V : Set G) := E.L₁_le.trans D.normalizes
  have hCN : ⁅E.W,E.L₁⁆ ≤ normalizer (V : Set G) :=
    (commutator_le_sup _ _).trans (sup_le hWN hLN)
  have he : actionImage (V := V) ⁅E.W,E.L₁⁆ = ⊥ := by
    rw [actionImage_commutator V E.W E.L₁ hWN hLN]
    exact commutator_eq_bot_iff_le_centralizer.mpr hroot
  have hL : ⁅E.W,E.L₁⁆ ≤ L :=
    (commutator_mono le_rfl E.L₁_le).trans
      (le_normalizer_iff_commutator_le_right.mp (hWT.trans D.sylow_normalizes_component))
  exact (le_inf hL ((actionImage_eq_bot_iff V _ hCN).mp he)).trans
    (centralizer_in_component_le_core E)

omit [Finite G] in
private theorem normalizes_join_of_commutator (A B C : Subgroup G)
    (hAC : A ≤ normalizer (C : Set G)) (hAB : ⁅A,B⁆ ≤ B ⊔ C) :
    A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have h : B ⊔ C ≤ (B ⊔ C).comap (MulAut.conj a).toMonoidHom := by
    apply sup_le
    · intro b hb
      have hh := (B ⊔ C).mul_mem
        (hAB (commutator_mem_commutator ha hb)) (mem_sup_left hb)
      change a * b * a⁻¹ ∈ B ⊔ C
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · intro c hc
      exact mem_sup_right (le_normalizer_iff.mp hAC a ha c hc)
  exact h hx

/-- The source's perfect residual improves the root-action bound to U. -/
theorem closure_commutator_le_U (hcore : L.pCoreIn 2 = V)
    (hroot : ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2)
    (hmoved : ⁅V,E.L₁⁆ = E.V₃) : ⁅E.W,E.L₁⁆ ≤ E.U := by
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect E.V₁
  have hL : E.L₁ ≤ E.G₁ := (residualIn_le _).trans inf_le_right
  let := D.elementary
  have hV : V ≤ E.G₁ := V.le_centralizer.trans
    ((centralizer_le E.V₁_le).trans (centralizer_le_normalizer _))
  have hW : E.W ≤ E.G₁ := conjugateSpanBy_le_self hV
  have hU : E.G₁ ≤ normalizer (E.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hb : ⁅⁅E.W,E.L₁⁆,E.L₁⁆ ≤ E.U :=
    ((commutator_mono (hroot.trans_eq hcore) le_rfl).trans_eq hmoved).trans
      (le_conjugateSpanBy E.V₃ E.G₁)
  have hh := commutator_commutator_le_of_rotate_of_le_normalizer
    (hL.trans hU) (hL.trans hU) (hW.trans hU)
    (by simpa only [commutator_comm E.L₁ E.W] using hb) hb
  simpa only [E.L₁.commutator_eq_self, commutator_comm E.L₁ E.W] using hh

/-- The actual G₁-normal closure of L₁ centralizes W_H/U. -/
theorem closure_commutator_K_le_U (hb : ⁅E.W,E.L₁⁆ ≤ E.U) :
    ⁅E.W,E.K⁆ ≤ E.U := by
  have hL : E.L₁ ≤ E.G₁ := (residualIn_le _).trans inf_le_right
  have hU : E.G₁ ≤ normalizer (E.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hW : E.G₁ ≤ normalizer (E.W : Set G) := le_normalizer_conjugateSpanBy _ _
  rw [commutator_comm, Geometry.K, conjugateSpanBy_eq_iSup_conj]
  apply commutator_iSup_le_of_relative_normal E.G₁ E.W E.U _ hU
  · intro g
    exact (map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hL).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (E.G₁.le_normalizer g.property))
  · intro g
    have hm := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hb
    have hw : E.W.map (MulAut.conj (g : G)).toMonoidHom = E.W :=
      mem_normalizer_iff_map_conj_eq.mp (hW g.property)
    have hu : E.U.map (MulAut.conj (g : G)).toMonoidHom = E.U :=
      mem_normalizer_iff_map_conj_eq.mp (hU g.property)
    rw [map_commutator, hw, hu] at hm
    simpa only [commutator_comm] using hm

/-- The literal quotient centralizer Y normalizes L₁. The proof uses
O₂(K)≤T and the perfect residual, with no ambient normality assumption. -/
theorem Y_normalizes_local_residual (m : MarkedFlag E) :
    E.Y ≤ normalizer (E.L₁ : Set G) := by
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect E.V₁
  have hKT : E.K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc : E.K.pCoreIn 2 ≤ E.G₁.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 E.K)
        ((pCoreIn_le 2 _).trans E.K_le_G₁)
        (E.G₁_normalizes_K.trans
          (normalizer_le_normalizer_characteristic_image E.K (pCore 2 E.K)))
    exact hc.trans ((pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)).trans_eq
      (map_subgroupOf_eq_of_le m.sylow_le_point_normalizer))
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    LocalGeometry.sylow_normalizes_localResidual D E.V₁ m.sylow_le_point_normalizer
  have hKY : ⁅E.K,E.Y⁆ ≤ E.K.pCoreIn 2 := by
    rw [commutator_comm]
    exact commutator_le.mpr fun y hy k hk => coreQuotientCentralizer_commutator hy.2 hk
  exact le_normalizer_iff_commutator_le_left.mpr
    ((perfect_subgroup_core_commutator E.L₁ E.K E.Y (le_conjugateSpanBy _ _)
      (hKT.trans hTL) hKY).trans (pCoreIn_le 2 _))

/-- In the commuting branch the first commutator is exactly V₃, not only
contained in the globally generated U. -/
theorem closure_commutator_eq_threeSpace (hc : ⁅V,E.U⁆ = ⊥)
    (hcore : L.pCoreIn 2 = V) (hroot : ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2)
    (hmoved : ⁅V,E.L₁⁆ = E.V₃) : ⁅E.W,E.L₁⁆ = E.V₃ := by
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect E.V₁
  have hL : E.L₁ ≤ normalizer (E.V₃ : Set G) := by
    rw [← hmoved]
    exact normalizer_commutator_ge_right V E.L₁
  have hW : E.W ≤ normalizer (E.V₃ : Set G) :=
    (le_centralizer_iff.mp (U_centralizes_W E hc)).trans
      ((centralizer_le (le_conjugateSpanBy E.V₃ E.G₁)).trans (centralizer_le_normalizer _))
  have hb : ⁅⁅E.W,E.L₁⁆,E.L₁⁆ ≤ E.V₃ :=
    (commutator_mono (hroot.trans_eq hcore) le_rfl).trans_eq hmoved
  have hh := commutator_commutator_le_of_rotate_of_le_normalizer hL hL hW
    (by simpa only [commutator_comm E.L₁ E.W] using hb) hb
  have hle : ⁅E.W,E.L₁⁆ ≤ E.V₃ := by
    simpa only [E.L₁.commutator_eq_self, commutator_comm E.L₁ E.W] using hh
  exact le_antisymm hle
    (hmoved.symm.le.trans (commutator_mono (le_conjugateSpanBy V E.G₁) le_rfl))

/-- The source 11.1.4 control supplies the actual action of Y on V in the
commuting branch. No supposition that K=L₁ is used. -/
theorem Y_normalizes_seed_of_commuting (m : MarkedFlag E)
    (hc : ⁅V,E.U⁆ = ⊥) (hcore : L.pCoreIn 2 = V)
    (hroot : ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2) (hmoved : ⁅V,E.L₁⁆ = E.V₃)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) :
    E.Y ≤ normalizer (V : Set G) := by
  have hYL := Y_normalizes_local_residual E m
  have hcomm := closure_commutator_eq_threeSpace E hc hcore hroot hmoved
  have hY3 : E.Y ≤ normalizer (E.V₃ : Set G) := by
    intro y hy
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hw : E.W.map (MulAut.conj y).toMonoidHom = E.W :=
      mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy V E.G₁) (E.Y_le_G₁ hy))
    have hl : E.L₁.map (MulAut.conj y).toMonoidHom = E.L₁ :=
      mem_normalizer_iff_map_conj_eq.mp (hYL hy)
    change E.V₃.map (MulAut.conj y).toMonoidHom = E.V₃
    rw [← hcomm, map_commutator, hw, hl]
  have hYM : E.Y ≤ E.M₁ := le_inf ((le_inf hY3 hYL).trans hcontrol) E.Y_le_G₁
  exact hYM.trans (M₁_normalizes_seed_of_TI E m hTI)

/-- The supplement calculation needed for W_H=UV is [V,Y]≤VU.
M₁ acts on V by TI, and K acts trivially on W_H/U by the preceding theorem. -/
theorem closure_eq_U_sup_seed (m : MarkedFlag E)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hK : ⁅E.W,E.K⁆ ≤ E.U) (hY : ⁅V,E.Y⁆ ≤ V ⊔ E.U) :
    E.W = E.U ⊔ V := by
  have hU : E.G₁ ≤ normalizer (E.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hK' : E.K ≤ normalizer ((V ⊔ E.U : Subgroup G) : Set G) :=
    normalizes_join_of_commutator E.K V E.U (E.K_le_G₁.trans hU) (by
      rw [commutator_comm]
      exact ((commutator_mono (le_conjugateSpanBy V E.G₁) le_rfl).trans hK).trans le_sup_right)
  have hY' : E.Y ≤ normalizer ((V ⊔ E.U : Subgroup G) : Set G) :=
    normalizes_join_of_commutator E.Y V E.U (E.Y_le_G₁.trans hU) (by
      simpa only [commutator_comm] using hY)
  have hM : E.M₁ ≤ normalizer ((V ⊔ E.U : Subgroup G) : Set G) :=
    (le_inf (M₁_normalizes_seed_of_TI E m hTI) (inf_le_right.trans hU)).trans
      (normalizer_inf_normalizer_le_normalizer_sup V E.U)
  apply le_antisymm
  · rw [sup_comm]
    exact conjugateSpanBy_le le_sup_left (hgen.trans (sup_le (sup_le hK' hY') hM))
  · exact sup_le
      (conjugateSpanBy_mono (D.centralQuotientPreimage_le E.threeSpace) le_rfl)
      (le_conjugateSpanBy V E.G₁)

/-- A conditional application of the source's commuting branch, retaining the
literal supplement action rather than assuming the splitting conclusion. -/
theorem abelian_of_commuting (m : MarkedFlag E)
    (hcore : L.pCoreIn 2 = V) (hu : IsMulCommutative E.U)
    (hc : ⁅V,E.U⁆ = ⊥) (hroot : ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2)
    (hmoved : ⁅V,E.L₁⁆ = E.V₃)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hY : ⁅V,E.Y⁆ ≤ V ⊔ E.U) : IsMulCommutative E.W :=
  W_abelian_of_commuting_split E hu hc (closure_eq_U_sup_seed E m hTI hgen
    (closure_commutator_K_le_U E (closure_commutator_le_U E hcore hroot hmoved)) hY)

/-- The full commuting terminal branch, with the supplement action discharged
using the original preceding normalizer control. -/
theorem abelian_of_source_commuting (m : MarkedFlag E)
    (hcore : L.pCoreIn 2 = V) (hu : IsMulCommutative E.U)
    (hc : ⁅V,E.U⁆ = ⊥) (hroot : ⁅E.W,E.L₁⁆ ≤ L.pCoreIn 2)
    (hmoved : ⁅V,E.L₁⁆ = E.V₃)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M) :
    IsMulCommutative E.W :=
  abelian_of_commuting E m hcore hu hc hroot hmoved hTI hgen
    ((le_normalizer_iff_commutator_le_left.mp
      (Y_normalizes_seed_of_commuting E m hc hcore hroot hmoved hcontrol hTI)).trans le_sup_left)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
