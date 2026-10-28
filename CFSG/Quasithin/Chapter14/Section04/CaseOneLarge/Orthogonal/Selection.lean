module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.SeedPoint
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.RankOne
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
/-!
# Selecting the original involution outside the orthogonal residual

The source singular F₄-point is retained on the literal U/Z(U). For its
original binary commutator form, a rank-one matrix calculation produces a
singular conjugate perpendicular to the marked binary line but not to the
whole F₄-point. The proof uses invariance and nondegeneracy of the actual
binary form; no comparison of independently chosen forms is assumed.

Lifting the actor through the original residual gives sᵏ in W outside C_U(V).
Right conjugation by the same g then gives i=zˣ in Wᵍ with x=gkg. The elementary
intersection E excludes i from U. If its actual star image lay in O²(H)*,
field linearity would fix the entire seed point; the two disjoint commutator
lines would then force i to centralize V. Thus i* escapes the residual.

These deductions discharge the selection paragraph of 14.4.9. The diagonal
moved module, exchanged action and centralizer comparison required by
Orthogonal.Source remain subsequent source obligations.

Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010;
refs/quasithin.pdf. The singular matrix orbit is reused from the attributed
ATLAS adaptation in OrthogonalFourPlusMatrix.Comparison.RankOne.
-/

public noncomputable section
open Matrix Subgroup Module Representation Representation.BinaryOffender
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
section MatrixSelection
set_option linter.unusedSimpArgs false
private def entry (i j : Fin 2) (c : Binary.F) : Binary.V := Matrix.single i j c
private def entryMap (i j : Fin 2) : Binary.F →ₗ[ZMod 2] Binary.V :=
  (Matrix.singleLinearMap Binary.F i j).restrictScalars (ZMod 2)
private theorem entry_ne (i j : Fin 2) {c : Binary.F} (hc : c ≠ 0) : entry i j c ≠ 0 := by
  intro h
  have hh := congrArg (fun M : Binary.V => M i j) h
  exact hc (by simpa [entry] using hh)
private theorem act_mul (a b : Binary.G) (v : Binary.V) :
    Binary.action (a*b) v = Binary.action a (Binary.action b v) :=
  congrArg (fun f : Module.End (ZMod 2) Binary.V => f v) (Binary.action.map_mul a b)
private theorem act_one (v : Binary.V) : Binary.action 1 v = v := by
  rw [map_one]; rfl
private theorem singular_transitive (v w : Binary.V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hdv : v.det = 0) (hdw : w.det = 0) : ∃ a : Binary.G, Binary.action a v = w := by
  obtain ⟨a,b,hv'⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit v hv hdv
  obtain ⟨c,d,hw'⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit w hw hdw
  refine ⟨(c,d)*(a,b)⁻¹,?_⟩
  change v = Binary.action (a,b) ComparisonAux.MatrixTwo.E11 at hv'
  change w = Binary.action (c,d) ComparisonAux.MatrixTwo.E11 at hw'
  rw [hv',act_mul]
  rw [←act_mul (a,b)⁻¹ (a,b),inv_mul_cancel,act_one,←hw']

private theorem pairing_entry (B : LinearMap.BilinForm (ZMod 2) Binary.V)
    (hi : ∀ a : Binary.G, ∀ x y, B (Binary.action a x) (Binary.action a y) = B x y)
    (M : Binary.V) : B (entry 0 0 1) M = B (entry 0 0 1) (entry 1 1 (M 1 1)) := by
  let a : Binary.G := (Representation.SL2FourNatural.upper 1,1)
  let l : SpecialLinearGroup (Fin 2) Binary.F :=
    SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1
  let b : Binary.G := (1,l⁻¹)
  have ha : Binary.action a (entry 0 0 1) = entry 0 0 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a,entry,Matrix.single_apply,Representation.SL2FourNatural.upper,
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hb : Binary.action b (entry 0 0 1) = entry 0 0 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [b,l,entry,Matrix.single_apply,SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hrow (j : Fin 2) (c : Binary.F) : B (entry 0 0 1) (entry 0 j c) = 0 := by
    have h := hi a (entry 0 0 1) (entry 1 j c)
    have he : Binary.action a (entry 1 j c) = entry 1 j c + entry 0 j c := by
      apply Matrix.ext
      intro i k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [a,entry,Matrix.single_apply,Representation.SL2FourNatural.upper,
          Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [ha,he,map_add] at h
    exact add_eq_left.mp h
  have h10 (c : Binary.F) : B (entry 0 0 1) (entry 1 0 c) = 0 := by
    have h := hi b (entry 0 0 1) (entry 1 1 c)
    have he : Binary.action b (entry 1 1 c) = entry 1 1 c + entry 1 0 c := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [b,l,entry,Matrix.single_apply,SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hb,he,map_add] at h
    exact add_eq_left.mp h
  have hM : M = entry 0 0 (M 0 0) + entry 0 1 (M 0 1) +
      entry 1 0 (M 1 0) + entry 1 1 (M 1 1) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [entry,Matrix.single_apply]
  conv_lhs => rw [hM]
  simp only [map_add,hrow,h10,zero_add]

private theorem entry_selection (B : LinearMap.BilinForm (ZMod 2) Binary.V)
    (hn : B.Nondegenerate)
    (hi : ∀ a : Binary.G, ∀ x y, B (Binary.action a x) (Binary.action a y) = B x y) :
    ∃ w : Binary.V, w ≠ 0 ∧ w.det = 0 ∧ B (entry 0 0 1) w = 0 ∧
      ∃ c : Binary.F, B (c • entry 0 0 1) w ≠ 0 := by
  let f : Binary.F →ₗ[ZMod 2] ZMod 2 := (B (entry 0 0 1)).comp (entryMap 1 1)
  have hc : ∃ c : Binary.F, c ≠ 0 ∧ f c = 0 := by
    by_contra! h
    have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (by
      apply le_bot_iff.mp
      intro c hc
      exact (Submodule.mem_bot (ZMod 2)).mpr (by
        by_contra hc0
        exact h c hc0 hc))
    have hh := LinearMap.finrank_le_finrank_of_injective hf
    rw [Binary.finrank_field,Module.finrank_self] at hh
    omega
  obtain ⟨c,hc,hfc⟩ := hc
  have hf : ∃ t : Binary.F, f t ≠ 0 := by
    by_contra! hh
    have hz := hn.1 (entry 0 0 1) (fun M => (pairing_entry B hi M).trans (hh (M 1 1)))
    exact entry_ne 0 0 one_ne_zero hz
  obtain ⟨t,ht⟩ := hf
  have ht0 : t ≠ 0 := by intro h; exact ht (h ▸ f.map_zero)
  let a := t/c
  have ha : a ≠ 0 := div_ne_zero ht0 hc
  let g : Binary.G := (SpecialLinearGroup.diag2 a ha,1)
  have hg0 : Binary.action g (entry 0 0 1) = a • entry 0 0 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g,entry,Matrix.single_apply,SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hg1 : Binary.action g (entry 1 1 t) = entry 1 1 c := by
    have hca : a⁻¹*t = c := by dsimp [a]; field_simp
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g,entry,Matrix.single_apply,SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hca]
  refine ⟨entry 1 1 c,entry_ne 1 1 hc,?_,hfc,a,?_⟩
  · simp [entry,Matrix.det_fin_two,Matrix.single_apply]
  · have hh := hi g (entry 0 0 1) (entry 1 1 t)
    rw [hg0,hg1] at hh
    exact fun h => ht (hh.symm.trans h)

private theorem matrix_selection (B : LinearMap.BilinForm (ZMod 2) Binary.V)
    (hn : B.Nondegenerate)
    (hi : ∀ a : Binary.G, ∀ x y, B (Binary.action a x) (Binary.action a y) = B x y)
    (v : Binary.V) (hv : v ≠ 0) (hd : v.det = 0) :
    ∃ a : Binary.G, B v (Binary.action a v) = 0 ∧
      ∃ c : Binary.F, B (c • v) (Binary.action a v) ≠ 0 := by
  obtain ⟨p,hp⟩ := singular_transitive (entry 0 0 1) v
    (entry_ne 0 0 one_ne_zero) hv (by simp [entry,Matrix.det_fin_two,Matrix.single_apply]) hd
  obtain ⟨w,hw,hwd,hwB,c,hc⟩ := entry_selection B hn hi
  obtain ⟨a,ha⟩ := singular_transitive v (Binary.action p w) hv
    (fun hh => hw ((Binary.linearAction p).injective (hh.trans (map_zero _).symm))) hd
    ((matrixAction_det p w).trans hwd)
  refine ⟨a,?_,c,?_⟩
  · rw [ha,←hp,hi]
    exact hwB
  · have hsm : c • v = Binary.action p (c • entry 0 0 1) := by
      rw [←hp]
      exact ((matrixHom p).map_smul c _).symm
    rw [ha,hsm,hi]
    exact hc

end MatrixSelection

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry
open scoped IsMulCommutative commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

omit [Finite G] [IsMulCommutative V] in
private theorem commutator_form_zero (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1)
    (B : F.UhatCommutatorForm hcomm) (a b : F.U) :
    B.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
  rw [show B.form (hatElement F a) (hatElement F b) =
    (B.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
      from B.evaluation a b]
  change B.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff B.valueEquiv B.valueEquiv.injective,Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans (by
    change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg (fun t : F.U => (t:G)) h)

/-- Select a conjugate of the original zᵍ in W outside C_U(V), lifting
the actor from the literal residual and retaining the original g. -/
theorem source_orthogonal_hyperplane_selection (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z) ∈ F.W ∧
          MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z) ∉ centralizer (V : Set G) := by
  let := chosen.elementary
  obtain ⟨hcore,_,_,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hpoint,_⟩ :=
    source_orthogonal_seed_point d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let C := source_closure_geometry F d earlier hq chosen structural alternatives hne
  have hcomm := (source_commutator_squares d earlier hq chosen structural alternatives F).1
  let B := F.localKernel_markedForm (by decide) C.two C.frattini_point hcomm
  let E := e.trans Binary.binaryCoordinates
  let b := LinearMap.BilinForm.congr E B.form
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) :
      E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨a,ha⟩ := elementaryEquiv.surjective (κ k)
    have hκ : κm k = a := by
      change elementaryEquiv.symm (κ k) = a
      rw [←ha,elementaryEquiv.symm_apply_apply]
    rw [←ha,hκ]
    exact toOrthogonal_coordinates a (e w)
  have hinv (h : F.H) (w y : Additive F.Uhat) :
      B.form (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) w)
        (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) y) = B.form w y := by
    change F.uhatBilinearForm (by decide) C.two C.frattini_point
      (Additive.ofMul (F.uhatAction h w.toMul)) (Additive.ofMul (F.uhatAction h y.toMul)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) C.two C.frattini_point]
    rfl
  have hbi (a : Binary.G) (w y : Binary.V) :
      b (Binary.action a w) (Binary.action a y) = b w y := by
    obtain ⟨k,rfl⟩ := κm.surjective a
    obtain ⟨h,hh,heq⟩ := k.property
    have hew : E.symm (Binary.action (κm k) w) = D.representation k (E.symm w) := by
      apply E.injective
      rw [E.apply_symm_apply,hm,E.apply_symm_apply]
    have hey : E.symm (Binary.action (κm k) y) = D.representation k (E.symm y) := by
      apply E.injective
      rw [E.apply_symm_apply,hm,E.apply_symm_apply]
    change B.form (E.symm _) (E.symm _) = B.form (E.symm w) (E.symm y)
    rw [hew,hey,←heq]
    exact hinv h _ _
  obtain ⟨a,ha,c,hc⟩ := matrix_selection b (B.nondegenerate.congr E) hbi (E v)
    (fun hh => hv0 (Binary.binaryCoordinates.injective (hh.trans Binary.binaryCoordinates.map_zero.symm)))
    ((coordinates_det (e v)).trans hqv)
  obtain ⟨k,hka⟩ := κm.surjective a
  obtain ⟨h,hh,heq⟩ := k.property
  let t : F.U := subgroupOfEquivOfLe F.U_le_H
    (MulAut.conjNormal h ((subgroupOfEquivOfLe F.U_le_H).symm s))
  have ht : E (hatElement F t) = Binary.action a (E v) := by
    rw [←hka,←hm,←heq]
    exact congrArg E (D.conjugation h ((subgroupOfEquivOfLe F.U_le_H).symm s))
  have hzero : B.form v (hatElement F t) = 0 := by
    rw [←ht] at ha
    change B.form (E.symm (E v)) (E.symm (E (hatElement F t))) = 0 at ha
    simpa only [E.symm_apply_apply] using ha
  have htW : (t : G) ∈ F.W := by
    refine ⟨t.property,?_⟩
    apply (hat_orthogonal_iff F B.form (commutator_form_zero F hcomm B)
      (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) t).mp
    intro w hw
    have hew : e w ∈ Submodule.span (ZMod 2) {e v} := hline ▸ ⟨w,hw,rfl⟩
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hew
    have hrw : r • v = w := e.injective (by simpa using hr)
    rw [←hrw]
    simp [hzero]
  have htV : (t : G) ∉ centralizer (V : Set G) := by
    intro hh
    have ho := (hat_orthogonal_iff F B.form (commutator_form_zero F hcomm B)
      V (le_conjugateSpanBy V F.H) t).mpr hh
    have hmemb : E.symm (c • E v) ∈ hatSpace F V := by
      have hec : e (E.symm (c • E v)) = c • e v := by
        apply Binary.binaryCoordinates.injective
        change E (E.symm (c • E v)) = coordinates (c • e v)
        rw [E.apply_symm_apply,map_smul]
        rfl
      have hh : c • e v ∈ (hatSpace F V).map e.toLinearMap := by
        rw [hpoint]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
      rw [←hec] at hh
      obtain ⟨w,hw,hew⟩ := hh
      exact e.injective hew ▸ hw
    apply hc
    rw [←ht]
    change B.form (E.symm (c • E v)) (E.symm (E (hatElement F t))) = 0
    rw [E.symm_apply_apply]
    exact ho _ hmemb
  refine ⟨hcore,z,hzo,hzp,hH,(h:G)⁻¹,?_,?_,?_⟩
  · exact mem_map_of_mem _ ((pResidual 2 F.H).inv_mem hh)
  · change (h:G) * (MulAut.conj g⁻¹ z) * (h:G)⁻¹ ∈ F.W at htW
    simpa only [inv_inv,MulAut.conj_apply] using htW
  · change (h:G) * (MulAut.conj g⁻¹ z) * (h:G)⁻¹ ∉ centralizer (V : Set G) at htV
    simpa only [inv_inv,MulAut.conj_apply] using htV

/-- Transport the selected conjugate into the original Wᵍ, retaining its
explicit conjugator. It escapes U and still fails to centralize V. -/
theorem source_orthogonal_selected_involution (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := MulAut.conj x⁻¹ z
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          i ∉ centralizer (V : Set G) := by
  let := chosen.elementary
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hsW,hsV⟩ :=
    source_orthogonal_hyperplane_selection d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s := MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z)
  let i := MulAut.conj (g*k*g)⁻¹ z
  have hi : i = MulAut.conj g⁻¹ s := by
    simp [i,s,MulAut.conj_apply,mul_assoc]
  have hiX : i ∈ F.X g := hi ▸ mem_map_of_mem _ hsW
  have hiV : i ∉ centralizer (V : Set G) := by
    intro hv
    apply hsV
    have hnorm := normalizer_le_normalizer_centralizer V (chosen.normalizes hg)
    have hh := (mem_normalizer_iff.mp hnorm i).mp hv
    change s ∈ centralizer (V : Set G)
    simpa [hi,MulAut.conj_apply,mul_assoc] using hh
  let C := source_closure_geometry F d earlier hq chosen structural alternatives hne
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [C.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g
      (chosen.normalizes hg) hgH)
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g C.two hPhi hdis
  have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
  have hiU : i ∉ F.U := by
    intro hu
    have hiW : i ∈ F.W := ⟨hu,F.X_le_plane_centralizer g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX⟩
    have hiE : i ∈ F.E g := ⟨hiW,hiX⟩
    apply hiV
    intro v hv
    exact congrArg Subtype.val (mul_comm (⟨v,hVE hv⟩ : F.E g) ⟨i,hiE⟩)
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,?_,hiX,?_,hiU,hiV⟩
  · simpa only [MulEquiv.orderOf_eq] using hzo
  · exact (source_extraspecial_data d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH).1.Wg_le_T hiX

/-- A member of Wᵍ whose star image belongs to the marked residual fixes
V pointwise. Field linearity fixes its whole F₄-point, and the disjoint
commutator lines remove the central error in lifting back to V. -/
theorem source_orthogonal_residual_fixes_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hi : (i:G) ∈ F.X g)
    (hiK : QuotientGroup.mk' (pCore 2 F.H) i ∈
      (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) :
    (i:G) ∈ centralizer (V : Set G) := by
  let := chosen.elementary
  obtain ⟨_,_,_,z,_,_,_,hs,hs₂,_,_,_,hpoint,_⟩ :=
    source_orthogonal_seed_point d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  let k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H)) :=
    ⟨QuotientGroup.mk' (pCore 2 F.H) i,hiK⟩
  have hiconj : F.uAction i s = s := by
    apply Subtype.ext
    change (i:G)*(s:G)*(i:G)⁻¹ = (s:G)
    rw [←F.X_le_plane_centralizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hi s hs₂]
    exact mul_inv_cancel_right _ _
  have hfix : D.representation k v = v := by
    change Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) s)) = v
    rw [F.uhatAction_apply_mk,hiconj]
    rfl
  have hfixe : subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v) = e v := by
    rw [←he,hfix]
  have hfixV (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) :
      D.representation k w = w := by
    have hw' : e w ∈ (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) := hpoint ▸ ⟨w,hw,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw'
    apply e.injective
    rw [he,←hc]
    rw [map_smul,hfixe]
  let C := source_closure_geometry F d earlier hq chosen structural alternatives hne
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g
      (chosen.normalizes hg) hgH)
  have hcomm := (source_commutator_squares d earlier hq chosen structural alternatives F).1
  have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
  intro w hw
  let u : F.U := ⟨w,le_conjugateSpanBy V F.H hw⟩
  have hf := hfixV (hatElement F u) ⟨u,hw,rfl⟩
  change Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) u)) =
    Additive.ofMul (QuotientGroup.mk' (center F.U) u) at hf
  have hqeq := Additive.ofMul.injective hf
  rw [F.uhatAction_apply_mk] at hqeq
  have hc : F.uAction i u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hqeq
  have hd : ((F.uAction i u / u : F.U) : G) = ⁅(i:G),w⁆ := by
    change ((i:G)*w*(i:G)⁻¹)/w = _
    simp only [commutatorElement_def,div_eq_mul_inv]
  have hz : ⁅(i:G),w⁆ ∈ F.ZU := ⟨_,hc,hd⟩
  have hr := commutator_X_E_le_conjugate_point F g hcomm
    (commutator_mem_commutator hi (hVE hw))
  have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

/-- The source involution is selected in the original conjugate Wᵍ and
its literal star image escapes O²(H)*. All selection premises are derived
from the original marked orthogonal row. -/
theorem source_orthogonal_selected_star_escape (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := MulAut.conj x⁻¹ z
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          ∃ hiH : i ∈ F.H,
            QuotientGroup.mk' (pCore 2 F.H) ⟨i,hiH⟩ ∉
              (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H)) := by
  let := chosen.elementary
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  have hiH := F.invariant 1 hiT
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiH,?_⟩
  intro hiK
  exact hiV (source_orthogonal_residual_fixes_seed d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he ⟨_,hiH⟩ hiX hiK)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
