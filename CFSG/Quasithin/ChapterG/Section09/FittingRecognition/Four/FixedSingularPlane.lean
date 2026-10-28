module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FixedSingularPlane
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.SingularPlane
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-! The fixed-plane calculation transported through the marked full orthogonal
realization, retaining the original quadratic form and literal actor.
Source:14.3.18(6). -/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
variable {G V:Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem fixed_plane_and_centralizer_of_full_orthogonal
    (ρ:Representation (ZMod 2) G V) (hr:OrthogonalRealization ρ ⊤)
    (Q:QuadraticForm (ZMod 2) V) (hnd:Q.polarBilin.Nondegenerate)
    (hQ:∀g v,Q (ρ g v)=Q v)
    (a:G) (ha:a≠1) (ha2:a^2=1) (S:Submodule (ZMod 2) V)
    (hd:2≤finrank (ZMod 2) S) (hs:∀v∈S,Q v=0)
    (hi:∀v∈S,ρ a v=v) :
    (∀z:V,ρ a z=z→z∈S) ∧
    Nonempty (centralizer ({a}:Set G) ≃*
      (Multiplicative (ZMod 2) × Equiv.Perm (Fin 3))) := by
  obtain ⟨e,l,he⟩ := hr
  let E := splitOrthogonalEquiv.trans BinaryFourPlus.isometryEquivWreath
  let K := (⊤:Subgroup OrthogonalFour).map E.toMonoidHom
  let k : G≃*K := e.trans (E.subgroupMap ⊤)
  let f := l.trans splitCoordinates
  have hact (g : G) (v : V) :
      (BinaryFourPlus.wreathToIsometry (k g).val).val (f v)=f (ρ g v) := by
    change (BinaryFourPlus.wreathToIsometry
      (BinaryFourPlus.isometryEquivWreath (splitOrthogonalEquiv (e g).val))).val
      (splitCoordinates (l v))=splitCoordinates (l (ρ g v))
    rw [BinaryFourPlus.wreathToIsometry_equiv,splitOrthogonalEquiv_intertwines,he]
  have hKcore : pCore 3 BinaryFourPlus.Wreath≤K := by
    rw [←pCore_map_iso 3 E]
    exact map_mono le_top
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
  let S' := S.map f.toLinearMap
  have hd':2≤finrank (ZMod 2) S' := by
    change 2≤finrank (ZMod 2) (S.map f.toLinearMap)
    rw [LinearEquiv.finrank_map_eq]
    exact hd
  have hs':∀v∈S',BinaryFourPlus.q v=0 := by
    rintro v ⟨w,hw,rfl⟩
    rw [←hRq]
    change Q (f.symm (f w))=0
    simpa only [f.symm_apply_apply] using hs w hw
  have ha':(k a).val≠1 := by
    intro hh
    apply ha
    apply k.injective
    exact Subtype.ext (hh.trans (congrArg Subtype.val (map_one k)).symm)
  have hi':∀v∈S',(BinaryFourPlus.wreathToIsometry (k a).val).val v=v := by
    rintro v ⟨w,hw,rfl⟩
    change (BinaryFourPlus.wreathToIsometry (k a).val).val (f w)=f w
    rw [hact,hi w hw]
  obtain ⟨hpar,hfix⟩ := BinaryFourPlus.fixed_singular_plane (k a).val ha' S' hd' hs' hi'
  constructor
  · intro z hz
    have hz':(BinaryFourPlus.wreathToIsometry (k a).val).val (f z)=f z := by
      rw [hact,hz]
    obtain ⟨w,hw,heq⟩ := hfix (f z) hz'
    exact f.injective heq ▸ hw
  · have hKtop:K=⊤ := by
      change (⊤:Subgroup OrthogonalFour).map E.toMonoidHom=⊤
      rw [←MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr E.surjective
    let j:G≃*BinaryFourPlus.Wreath :=
      k.trans ((MulEquiv.subgroupCongr hKtop).trans topEquiv)
    obtain ⟨c⟩ := BinaryFourPlus.swapping_involution_centralizer_equiv (j a) hpar
      (by rw [←map_pow,ha2,map_one])
    exact ⟨(Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv j a).trans c⟩
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
