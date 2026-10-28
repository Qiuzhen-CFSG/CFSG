module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPlaneCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.SolvableSource

/-!
# The singular-plane obstruction in the original degree-four action

The order-nine core realizes the original faithful representation inside
O₄⁺(2). The core's two cubic rotations identify every preserved nondegenerate
quadratic form with the model form. Thus a singular plane invariant under
the original Sylow subgroup gives a normal cubic in the original group.

Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- A marked orthogonal realization transfers the finite singular-plane
obstruction to the original acting group and its quadratic form. -/
theorem normal_cubic_of_orthogonal_singular_plane
    (ρ : Representation (ZMod 2) G V)
    (H : Subgroup OrthogonalFour) (hcore : pCore 3 OrthogonalFour≤H)
    (hr : OrthogonalRealization ρ H)
    (Q : QuadraticForm (ZMod 2) V) (hnd : Q.polarBilin.Nondegenerate)
    (hQ : ∀ g v, Q (ρ g v)=Q v)
    (P : Sylow 2 G) (S : Submodule (ZMod 2) V)
    (hd : 2≤finrank (ZMod 2) S) (hs : ∀ v∈S, Q v=0)
    (hi : ∀ g∈(P:Subgroup G), ∀ v∈S, ρ g v∈S) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C=3 := by
  obtain ⟨e,l,he⟩ := hr
  let E := splitOrthogonalEquiv.trans BinaryFourPlus.isometryEquivWreath
  let K := H.map E.toMonoidHom
  let k : G≃*K := e.trans (E.subgroupMap H)
  let f := l.trans splitCoordinates
  have hact (g : G) (v : V) :
      (BinaryFourPlus.wreathToIsometry (k g).val).val (f v)=f (ρ g v) := by
    change (BinaryFourPlus.wreathToIsometry
      (BinaryFourPlus.isometryEquivWreath (splitOrthogonalEquiv (e g).val))).val
      (splitCoordinates (l v))=splitCoordinates (l (ρ g v))
    rw [BinaryFourPlus.wreathToIsometry_equiv,splitOrthogonalEquiv_intertwines,he]
  have hKcore : pCore 3 BinaryFourPlus.Wreath≤K := by
    rw [←pCore_map_iso 3 E]
    exact map_mono hcore
  let R := Q.comp f.symm.toLinearMap
  have hR (g : G) (v : BinaryFourPlus.V) :
      R ((BinaryFourPlus.wreathToIsometry (k g).val).val v)=R v := by
    obtain ⟨w,rfl⟩ := f.surjective v
    rw [hact]
    change Q (f.symm (f (ρ g w)))=Q (f.symm (f w))
    simpa only [f.symm_apply_apply] using hQ g w
  have hRcore : ∀ a∈pCore 3 BinaryFourPlus.Wreath, ∀ v,
      R ((BinaryFourPlus.wreathToIsometry a).val v)=R v := by
    intro a ha v
    obtain ⟨g,hg⟩ := k.surjective ⟨a,hKcore ha⟩
    simpa only [hg] using hR g v
  have hRnd : R.polarBilin.Nondegenerate := by
    constructor
    · intro x hx
      apply f.symm.injective
      rw [map_zero]
      apply hnd.1
      intro y
      have hh := hx (f y)
      simp only [R,QuadraticMap.polarBilin_comp,LinearMap.compl₁₂_apply] at hh
      change Q.polarBilin (f.symm x) (f.symm (f y))=0 at hh
      simpa only [f.symm_apply_apply] using hh
    · intro x hx
      apply f.symm.injective
      rw [map_zero]
      apply hnd.2
      intro y
      have hh := hx (f y)
      simp only [R,QuadraticMap.polarBilin_comp,LinearMap.compl₁₂_apply] at hh
      change Q.polarBilin (f.symm (f y)) (f.symm x)=0 at hh
      simpa only [f.symm_apply_apply] using hh
  have hRq : R=BinaryFourPlus.q := BinaryFourPlus.eq_q_of_threeCore_invariant R hRcore hRnd
  let P' := P.mapSurjective (f:=k.toMonoidHom) k.surjective
  let S' := S.map f.toLinearMap
  have hd' : 2≤finrank (ZMod 2) S' := by
    change 2≤finrank (ZMod 2) (S.map f.toLinearMap)
    rw [LinearEquiv.finrank_map_eq]
    exact hd
  have hs' : ∀ v∈S', BinaryFourPlus.q v=0 := by
    rintro v ⟨w,hw,rfl⟩
    rw [←hRq]
    change Q (f.symm (f w))=0
    simpa only [f.symm_apply_apply] using hs w hw
  have hi' : ∀ a : P', ∀ v∈S',
      (BinaryFourPlus.wreathToIsometry a.val.val).val v∈S' := by
    rintro a v ⟨w,hw,rfl⟩
    obtain ⟨b,hb,heq⟩ := a.property
    change (BinaryFourPlus.wreathToIsometry a.val.val).val (f w)∈S.map f.toLinearMap
    rw [←heq]
    change (BinaryFourPlus.wreathToIsometry (k b).val).val (f w)∈S.map f.toLinearMap
    rw [hact]
    exact ⟨ρ b w,hi b hb w hw,rfl⟩
  obtain ⟨C,hCn,hCc⟩ := BinaryFourPlus.normal_cubic_of_sylow_invariant_singular_plane
    K hKcore P' S' hd' hs' hi'
  exact ⟨C.map k.symm.toMonoidHom,hCn.map _ k.symm.surjective,
    (card_map_of_injective k.symm.injective).trans hCc⟩

/-- The source three-core of order nine supplies the orthogonal realization
internally; all source subspaces and Sylow actions are retained. -/
theorem normal_cubic_of_nine_core_singular_plane
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hdV : finrank (ZMod 2) V=4) (h9 : Nat.card (pCore 3 G)=9)
    (Q : QuadraticForm (ZMod 2) V) (hnd : Q.polarBilin.Nondegenerate)
    (hQ : ∀ g v, Q (ρ g v)=Q v)
    (P : Sylow 2 G) (S : Submodule (ZMod 2) V)
    (hd : 2≤finrank (ZMod 2) S) (hs : ∀ v∈S, Q v=0)
    (hi : ∀ g∈(P:Subgroup G), ∀ v∈S, ρ g v∈S) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C=3 := by
  obtain ⟨H,hcore,hr⟩ := NineNormalizer.core_realization ρ hf hdV h9
  exact normal_cubic_of_orthogonal_singular_plane ρ H hcore hr Q hnd hQ P S hd hs hi
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
