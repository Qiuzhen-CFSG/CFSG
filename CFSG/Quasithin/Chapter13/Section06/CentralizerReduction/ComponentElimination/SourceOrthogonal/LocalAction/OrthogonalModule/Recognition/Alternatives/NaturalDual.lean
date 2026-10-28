module

public import Theory.Representation.BinaryOffender.CentralSectionAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.Seed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking

/-!
# Excluding the natural-plus-dual row on the actual upper module

Let C = K⁺, let R be the Sylow two-subgroup marked by (Tᵥ ∩ K)⁺, and
put J = C_C(C_U(R)). Clause (6) of the corrected B.5.1 conclusion gives
|O₂(J)| = 32 and J/O₂(J) ≃ PSL₂(2), hence |J| = 192. Since R ≤ J and
|R| = 64, the intrinsic index-three recognition makes J a minimal parabolic.

The literal Tᵥ⁺ action normalizes R and acts on the whole upper module,
so it normalizes J. It also normalizes the source P = Lᵥ(Tᵥ ∩ K).
An actual outer component automorphism cannot preserve two distinct minimal
parabolics over the same Sylow, even with different coordinate bases.
Thus J = P⁺. The moving Sylow-fixed upper vector constructed from the original
seed z contradicts this pointwise fixation. No central extension is split,
and the source application retains the A₅ marking and canonical moved section.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed p.99/PDF p.110, and the paragraph following 13.6.23,
printed p.933/PDF p.950. The full corrected B.5.1 conclusion and the actual
13.6.23 model, outer action, and middle-node parabolic remain inputs.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open scoped MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem normalizes_kernel {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) D V) (W : Submodule (ZMod 2) V) (C A : Subgroup D)
    (hC : A ≤ normalizer (C : Set D)) (hW : A ≤ subspaceStabilizer τ W) :
    A ≤ normalizer (subspaceKernel τ W C : Set D) := by
  have hconj (a : D) (ha : a ∈ A) (x : D) (hx : x ∈ subspaceKernel τ W C) :
      a * x * a⁻¹ ∈ subspaceKernel τ W C := by
    refine ⟨(mem_normalizer_iff.mp (hC ha) x).mp hx.1, ?_⟩
    intro w hw
    have hwi := (hW (A.inv_mem ha) w).mpr hw
    calc
      τ (a * x * a⁻¹) w = τ a (τ x (τ a⁻¹ w)) := by
        simp only [map_mul, Module.End.mul_apply]
      _ = τ a (τ a⁻¹ w) := congrArg (τ a) (hx.2 _ hwi)
      _ = w := by simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]
  intro a ha
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact hconj a ha x
  · intro hx
    have hh := hconj a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using hh

private theorem fixedSpace_restrict_image {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (τ : Representation (ZMod 2) D V) (C : Subgroup D)
    (R : Subgroup C) : fixedSpace (τ.comp C.subtype) R = fixedSpace τ (R.map C.subtype) := by
  ext u
  constructor
  · intro hu r
    obtain ⟨x, hx, he⟩ := r.property
    have hh := hu ⟨x, hx⟩
    change τ (x : D) u = u at hh
    change τ (r : D) u = u
    change (x : D) = (r : D) at he
    rwa [he] at hh
  · intro hu r
    exact hu ⟨(r.val : D), ⟨r.val, r.property, rfl⟩⟩

private theorem kernel_restrict_image {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (τ : Representation (ZMod 2) D V) (C : Subgroup D)
    (W : Submodule (ZMod 2) V) :
    (subspaceKernel (τ.comp C.subtype) W ⊤).map C.subtype = subspaceKernel τ W C := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha.2⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, ⟨mem_top _, hx.2⟩, rfl⟩

private theorem sylowFixedCentralizer_card {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] (σ : Representation (ZMod 2) D V)
    (R : Sylow 2 D) (c : SylowFixedCentralizer σ ⊤ 4 R) :
    Nat.card (subspaceKernel σ (fixedSpace σ R) ⊤) = 192 := by
  let J := subspaceKernel σ (fixedSpace σ R) ⊤
  have hq : Nat.card (J ⧸ pCore 2 J) = 6 := by
    rw [Nat.card_congr c.quotientEquiv.toEquiv,
      Nat.card_congr (projectiveEquivLinear (by decide : 0 < 2)).toEquiv,
      ← Nat.card_congr (matrixEquivLinear 2).toEquiv,
      Matrix.card_GL_field]
    decide
  have hc : Nat.card (pCore 2 J) = 32 := c.core_order
  have hh := (pCore 2 J).index_mul_card
  rw [index_eq_card, hq, hc] at hh
  exact hh.symm

private theorem sylow_four_card (R : Sylow 2 (LinearGroup 4)) : Nat.card R = 64 := by
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  let R₀ := CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardSylow
  rw [Nat.card_congr (R.equiv R₀).toEquiv]
  exact CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.standardBorel_card


variable {G : Type*} [Group G] [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Clause (6), the marked Sylow, and the outer action identify the actual
pointwise centralizer with the literal source parabolic. -/
theorem sylowFixedCentralizer_eq_sourceParabolic
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e4 : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K))
    (b : Basis 3)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e4.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic b (1 : Fin 3))
    (d : SylowFixedCentralizer
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤ 4 R) :
    subspaceKernel (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)
        (fixedSpace (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) R) ⊤ =
      (plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K) := by
  let C := plusImage K L T z v hL hz K
  let S := plusImage K L T z v hL hz (Tv T v)
  let P := plusImage K L T z v hL hz (sourceParabolic K L T v)
  let τ := s.space.toRepresentation
  let σ := τ.comp C.subtype
  let W := fixedSpace σ (R : Subgroup C)
  let J := subspaceKernel σ W ⊤
  let Q := J.map C.subtype
  let E := e4.trans (slEquivLinear 4)
  let U : Sylow 2 (LinearGroup 4) := R.mapSurjective (f := E.toMonoidHom) E.surjective
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  have hRJ : (R : Subgroup C) ≤ J := fun r hr => ⟨mem_top _, fun w hw => hw ⟨r, hr⟩⟩
  have hUJ : (U : Subgroup (LinearGroup 4)) ≤ J.map E.toMonoidHom := map_mono hRJ
  have hcard : Nat.card (J.map E.toMonoidHom) = 192 := by
    rw [card_map_of_injective E.injective]
    exact sylowFixedCentralizer_card σ R d
  have hi : (U : Subgroup (LinearGroup 4)).relIndex (J.map E.toMonoidHom) = 3 := by
    have hh := ((U : Subgroup (LinearGroup 4)).subgroupOf (J.map E.toMonoidHom)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv, sylow_four_card U, hcard] at hh
    change (U : Subgroup (LinearGroup 4)).relIndex (J.map E.toMonoidHom) * 64 = 192 at hh
    omega
  obtain ⟨b', i, hJ, _⟩ := Selection.ParabolicConstruction.FlagRecognition.exists_minimalParabolic
    (Or.inl rfl : 3 = 3 ∨ 3 = 4) U _ hUJ hi
  have hPC : P ≤ C := map_mono (comap_mono (sourceParabolic_le K L T v hLK))
  have hSP : S ≤ normalizer (P : Set _) :=
    normalizes_plusImage K L T _ _ z v hL hz
      ((sourceParabolic_le K L T v hLK).trans (K_le_plusActor K L T v))
      (normalizes_sourceParabolic K L T v hL hK)
  have hSR : S ≤ normalizer (plusImage K L T z v hL hz (Tv T v ⊓ K) : Set _) :=
    normalizes_plusImage K L T _ _ z v hL hz
      (inf_le_right.trans (K_le_plusActor K L T v))
      (le_normalizer_inf (Tv T v).le_normalizer hK)
  have hSW : S ≤ subspaceStabilizer τ W := by
    change S ≤ subspaceStabilizer τ (fixedSpace (τ.comp C.subtype) (R : Subgroup C))
    rw [fixedSpace_restrict_image, hR]
    exact fixedSpace_stable_of_normalizes τ hSR
  have hSQ : S ≤ normalizer (Q : Set _) := by
    rw [show Q = subspaceKernel τ W C from kernel_restrict_image τ C W]
    exact normalizes_kernel τ W C S le_normalizer_of_normal hSW
  have hRP : (R : Subgroup C) ≤ P.subgroupOf C := by
    intro r hr
    have hm : (r : Gplus K L T z v hL hz) ∈ plusImage K L T z v hL hz (Tv T v ⊓ K) :=
      hR ▸ (show (r : Gplus K L T z v hL hz) ∈ (R : Subgroup C).map C.subtype from
        ⟨r, hr, rfl⟩)
    exact map_mono (comap_mono (show Tv T v ⊓ K ≤ sourceParabolic K L T v from le_sup_right)) hm
  have hUP : (U : Subgroup (LinearGroup 4)) ≤ minimalParabolic b (1 : Fin 3) := by
    rw [← hP]
    exact map_mono hRP
  obtain ⟨t, ht, htC⟩ : ∃ t, t ∈ S ∧ t ∉ C := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hout
  let a := componentAction C E t
  have hc := Selection.plusComponent_centralizer_eq_bot K L T z v hL hz hLK hK hT hcore
    (by decide : 0 < 4) e4
  have ha : a ∉ MulAut.innerSubgroup _ := fun ha => htC ((componentAction_mem_inner C E hc t).mp ha)
  have hfixP := componentAction_map_subgroup C E P hPC t (hSP ht)
  change ((P.subgroupOf C).map E.toMonoidHom).map a.toMonoidHom = _ at hfixP
  change (P.subgroupOf C).map E.toMonoidHom = minimalParabolic b (1 : Fin 3) at hP
  rw [hP] at hfixP
  have hfixJ := componentAction_map_subgroup C E Q (map_subtype_le J) t (hSQ ht)
  have hQ : Q.subgroupOf C = J := comap_map_eq_self_of_injective C.subtype_injective J
  change ((Q.subgroupOf C).map E.toMonoidHom).map a.toMonoidHom = _ at hfixJ
  rw [hQ, hJ] at hfixJ
  have he : minimalParabolic b (1 : Fin 3) = minimalParabolic b' i := by
    by_contra hne
    apply ha
    exact preserving_two_minimalParabolics_is_inner (by decide) (by decide) b b' 1 i U
      hUP (hJ ▸ hUJ) hne a hfixP hfixJ
  apply map_injective (f := E.toMonoidHom) E.injective
  exact hJ.trans (he.symm.trans hP.symm)

/-- The source parabolic would fix every Sylow-fixed upper vector in the
natural-plus-dual row, contradicting movement of the original seed. -/
theorem classified_not_naturalDual
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (e4 : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K))
    (b : Basis 3)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e4.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic b (1 : Fin 3))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) :
    ¬ IsNaturalPlusDual
      (show Representation (ZMod 2) (⊤ : Subgroup (plusImage K L T z v hL hz K))
        c.sectionData.space.toSubmodule from c.sectionData.space.toRepresentation.comp
          (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype) 4 := by
  intro hn
  obtain ⟨d⟩ := c.clause_six 4 (Or.inl rfl) rfl hn R
  have he := sylowFixedCentralizer_eq_sourceParabolic K L T z v hL hz hK hLK e4
    hT hcore hout s R hR b hP d
  apply sourceParabolic_not_fix_upper_sylow K L T z v hL hz hLK hmove s R hR
  intro u hu g hg
  have hj : g ∈ subspaceKernel
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)
      (fixedSpace (s.space.toRepresentation.comp
        (plusImage K L T z v hL hz K).subtype) R) ⊤ := he.symm ▸ hg
  exact hj.2 u hu

section Source
variable (V : Subgroup G) (a5 : A5Module.Marking L V)
    (hzmark : z = A5Module.markedZ a5) (hvmark : v = A5Module.markedV a5)
include hzmark hvmark

/-- Application on the canonical U_K section with the actual A₅ marking and
its source seed. Earlier source data and the corrected B.5.1 conclusion
remain inputs; no recognition assumption or splitting is introduced. -/
theorem source_classified_not_naturalDual
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (e4 : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K))
    (b : Basis 3)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e4.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic b (1 : Fin 3))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      ((movedSection K L T z v hL hz hK hLK).space.toRepresentation.comp
        (plusImage K L T z v hL hz K).subtype) ⊤) :
    ¬ IsNaturalPlusDual
      (show Representation (ZMod 2) (⊤ : Subgroup (plusImage K L T z v hL hz K))
        c.sectionData.space.toSubmodule from c.sectionData.space.toRepresentation.comp
          (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype) 4 := by
  subst z
  subst v
  exact classified_not_naturalDual K L T _ _ hL hz hK hLK hmove e4 hT hcore hout
    (movedSection K L T _ _ hL hz hK hLK) R hR b hP c
end Source
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
