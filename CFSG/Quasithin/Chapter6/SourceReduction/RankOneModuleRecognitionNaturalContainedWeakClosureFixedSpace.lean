module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpaceMarking
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosure

/-!
# Natural A₂ actors fix the actual Sylow line

Transport the literal induced automizer through the given natural-module
coordinates. Its coefficient kernel has index at most two, so the A₂
fixed-space condition forces field-linearity. The image is elementary,
although the original actor need not be. Every resulting linear involution
preserves the actual Sylow fixed field-line and hence fixes it pointwise.

The weak-closure application supplies this control to E.3.10, retaining only
the independent source equality s(G,B)=n. No global rank assertion, contained
centralizer, 6.1.15 or later recognition result enters the local argument.
Source: Aschbacher--Smith, 6.1.12(2--3), printed pp.669--670.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {κ : CFSG.Quasithin.GroupClass}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Source 6.1.12's local A₂ control on the original layer and Sylow line.
Only the induced image is elementary; the original actor is arbitrary. -/
theorem natural_fixedSpace_control (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    letI := h.layer_elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer (layer L V) A ∈
        fixedSpaceFamily (automizerRepresentation (layer L V)) 2 →
      A ≤ centralizer (ZS (T : Subgroup G) L V : Set G) := by
  let := h.layer_elementary
  let B := layer L V
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨E, hE, hsemi⟩ := natural_binary_marking_semilinear e f hf
  let ρ : Representation (ZMod 2) (Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (automizerRepresentation B)
  have hcoord (a : Automizer B) (v : B) :
      ρ a (f v).toAdd = (f (a.val v)).toAdd := by
    rw [← hE]
    change E (automizerRepresentation B a (E.symm (E (Additive.ofMul v)))) = _
    rw [E.symm_apply_apply]
    exact hE _
  have hfix (D : Subgroup (Automizer B)) (v : Additive B) :
      E v ∈ fixedSpace ρ D ↔ v ∈ fixedSpace (automizerRepresentation B) D := by
    constructor
    · intro hv a
      apply E.injective
      change E (automizerRepresentation B (a : Automizer B) v) = E v
      have hh := hv a
      change E (automizerRepresentation B a (E.symm (E v))) = E v at hh
      simpa only [E.symm_apply_apply] using hh
    · intro hv a
      change E (automizerRepresentation B a (E.symm (E v))) = E v
      rw [E.symm_apply_apply]
      exact congrArg E (hv a)
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes_L
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hq
  obtain ⟨W, hWcard, hWfix, _, _⟩ :=
    Representation.SpecialLinearTwo.sylow_fixed_line_displacements 2 P
  have hline (v : B) : (f v).toAdd ∈ W ↔
      (v : G) ∈ centralizer ((T : Subgroup G) ⊓ L : Set G) := by
    rw [hWfix]
    constructor
    · intro hv
      apply mem_centralizer_iff.mpr
      intro s hs
      have hsS : (⟨s, hs.2⟩ : L) ∈ (S : Subgroup L) := hS.symm ▸ hs.1
      have hh := hf ⟨s,hs.2⟩ v
      have hhf := hv (q ⟨s,hs.2⟩) (mem_map.mpr ⟨_, hsS, rfl⟩)
      change (Representation.specialLinearNatural 2 (q ⟨s,hs.2⟩)) (f v).toAdd = (f v).toAdd at hhf
      rw [show e (QuotientGroup.mk' (pCore 2 L) ⟨s,hs.2⟩) = q ⟨s,hs.2⟩ from rfl,
        hhf, ofAdd_toAdd, f.symm_apply_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    · intro hv g hg
      obtain ⟨s, hs, rfl⟩ := hg
      have hsT : (s : G) ∈ (T : Subgroup G) := by
        have hh : s ∈ (T : Subgroup G).subgroupOf L := hS ▸ hs
        exact hh
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply Subtype.ext
      change (f.symm (Multiplicative.ofAdd
        (Representation.specialLinearNatural 2
          (e (QuotientGroup.mk' (pCore 2 L) s)) (f v).toAdd)) : G) =
        (f.symm (f v) : G)
      rw [hf, f.symm_apply_apply, mem_centralizer_iff.mp hv (s : G) ⟨hsT,s.property⟩,
        mul_inv_cancel_right]
  intro A hAT hA
  let I := inducedAutomizer B A
  have hI : I ∈ fixedSpaceFamily ρ 2 := by
    refine ⟨hA.1,hA.2.1,?_⟩
    intro D hDI hidx
    ext v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [hfix,hfix,hA.2.2 D hDI hidx]
  have hIsemi : ∀ a : I, ∃ σ : F ≃+* F, ∀ c v,
      ρ (a : Automizer B) (c • v) = σ c • ρ (a : Automizer B) v := by
    intro a
    obtain ⟨b,hb,he⟩ := a.property
    have hnL := h.sylow_normalizes_L (hAT hb)
    obtain ⟨σ,hσ⟩ := hsemi b hnL b.property
    refine ⟨σ,?_⟩
    intro c v
    rw [← he]
    exact hσ c v
  have hlin := fixedSpaceFamily_two_fieldLinear ρ hI hIsemi
  intro a ha z hz
  let t : Automizer B := B.normalizerMonoidHom.rangeRestrict
    ⟨a, h.sylow_normalizes_layer (hAT ha)⟩
  have ht : t ∈ I := mem_map.mpr ⟨_,ha,rfl⟩
  let d : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := ρ t
      map_add' := (ρ t).map_add
      map_smul' := hlin t ht }
  have hsq : ∀ v, d (d v) = v := by
    intro v
    let := hI.2.1.2
    have hh := congrArg ρ (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht)
    change ρ t (ρ t v) = v
    simpa only [pow_two,map_mul,map_one,Module.End.mul_apply,Module.End.one_apply]
      using LinearMap.congr_fun hh v
  have hnW : ∀ v ∈ W, d v ∈ W := by
    intro v hv
    obtain ⟨w,hw⟩ := f.surjective (Multiplicative.ofAdd v)
    have hw' : (f w).toAdd = v := congrArg Multiplicative.toAdd hw
    have hwZ : (w : G) ∈ ZS (T : Subgroup G) L V :=
      ⟨w.property, (hline w).mp (hw'.symm ▸ hv)⟩
    have haw : (t.val w : G) ∈ ZS (T : Subgroup G) L V :=
      (mem_normalizer_iff.mp (h.sylow_normalizes_ZS (hAT ha)) w).mp hwZ
    change ρ t v ∈ W
    rw [← hw',hcoord]
    exact (hline _).mpr haw.2
  have hzW : (f ⟨z,hz.1⟩).toAdd ∈ W := (hline _).mpr hz.2
  have hzfix := fieldLine_involution_fixes W hWcard d hsq hnW _ hzW
  change ρ t (f ⟨z,hz.1⟩).toAdd = (f ⟨z,hz.1⟩).toAdd at hzfix
  rw [hcoord] at hzfix
  have he := congrArg (fun w : B => (w : G))
    (f.injective (Multiplicative.toAdd.injective hzfix))
  change a * z * a⁻¹ = z at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Applying the local control to the proved E.3.10 weak-closure deduction.
The rank equality remains with its independent source producer. -/
theorem natural_weak_closure_bounds_of_globalS_eq
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hs : letI := h.layer_elementary; globalS (layer L V) = n) :
    (2 < n → ZS (T : Subgroup G) L V ≤ C (layer L V) (T : Subgroup G) 1) ∧
      W (layer L V) (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L V : Set G) :=
  weak_closure_bounds_of_fixedSpace_control h hs (natural_fixedSpace_control h hnatural)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
