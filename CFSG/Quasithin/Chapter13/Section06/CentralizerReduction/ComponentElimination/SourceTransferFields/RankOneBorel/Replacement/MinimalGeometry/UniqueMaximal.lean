module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.LocalHypotheses
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal.PerfectCover

/-!
# Unique maximal overgroups for the minimal rank-one replacement

Full local-family minimality excludes a proper Sylow overgroup supplementing
any solvable normal subgroup: its residual would be a smaller local C-component.
The ambient two-core remains nontrivial in that overgroup because it lies in
the prescribed Sylow. This uses the full family, not an equal-image subfamily.

For the rank-one step, the actual surjection has proper kernel, hence its kernel
lies in the component's solvable radical. Borel uniqueness lifts after adjoining
this radical, first inside the component and then to its Sylow extension.
The supplement argument removes the radical from the lower endpoint.
All normality is relative to the actual local join.

The source application uses H = K₀ ⊔ Tᵥ and D = K₀.subgroupOf H, transporting the
native plus-image map itself. It discharges uniqueness in the existing B.6.1 and
C.1.26 consumers. Nonnormality, local SQTK and characteristic two come from
`LocalHypotheses`; the latter uses `local_join_characteristic_two`. The native
model, full minimality, 13.6.16(2), and the C.1.26 implication remain inputs for
the enclosing source-theorem owner. No field exclusion is required for uniqueness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948); Definition B.6.1, p.112 (PDF p.123).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
open Subgroup Theory.GroupTheory ComponentSelection
open scoped MatrixGroups
variable {H : Type*} [Group H] [Finite H]

private theorem component_eq_residual (D : Subgroup H) [D.Normal] (hD : D.IsCComponent)
    (P : Sylow 2 H) (hgen : D ⊔ (P : Subgroup H) = ⊤) : solvableResidual H = D := by
  let := hD.perfect
  let := P.isPGroup'.isNilpotent
  have he := map_residual_sup_eq_of_perfect_of_solvable D (P : Subgroup H)
    (show (P : Subgroup H) ≤ normalizer (D : Set H) from le_normalizer_of_normal)
  rw [hgen] at he
  rwa [map_solvableResidual_eq _ (show Function.Surjective (⊤ : Subgroup H).subtype from
    fun x => ⟨⟨x, mem_top x⟩, rfl⟩)] at he

private theorem eq_top_of_solvable_supplement (D : Subgroup H) [D.Normal] (hD : D.IsCComponent)
    (P : Sylow 2 H) (hgen : D ⊔ (P : Subgroup H) = ⊤)
    (hmin : Minimal (fun E => E ∈ Chapter1.L H (P : Subgroup H)) D)
    (R : Subgroup H) [R.Normal] [Group.IsSolvable R]
    (M : Subgroup H) (hPM : (P : Subgroup H) ≤ M) (hRM : R ⊔ M = ⊤) : M = ⊤ := by
  have hres := component_eq_residual D hD P hgen
  have hE : (solvableResidual M).IsCComponent :=
    residual_isCComponent_of_solvable_supplement R M hRM (hres.symm ▸ hD)
  let E := (solvableResidual M).map M.subtype
  have hED : E ≤ D := (map_solvableResidual_le M.subtype).trans_eq hres
  have hEM : E ≤ M := map_subtype_le _
  have hSyl : Chapter1.IsSylowIn 2 (P : Subgroup H) M :=
    ⟨P.subtype hPM, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPM]⟩
  have hcore : M.pCoreIn 2 ≠ ⊥ := by
    have hcoreD := hmin.1.2.2
    have hcoreP : (D ⊔ (P : Subgroup H)).pCoreIn 2 ≤ (P : Subgroup H) := by
      obtain ⟨S, hS⟩ := hmin.1.2.1
      exact (pCoreIn_le_sylow _ S).trans_eq hS
    have hle : (D ⊔ (P : Subgroup H)).pCoreIn 2 ≤ M.pCoreIn 2 :=
      (le_inf (hcoreP.trans hPM) le_rfl).trans (inf_pCoreIn_le_of_le 2 (by rw [hgen]; exact le_top))
    exact fun he => hcoreD (bot_unique (he ▸ hle))
  have hlocal : E ∈ Chapter1.L H (P : Subgroup H) := by
    apply Chapter1.mem_L_of_cComponent (H := M) hcore hSyl hEM
    simpa only [E, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective] using hE
  apply top_unique
  rw [← hgen]
  exact sup_le ((hmin.2 hlocal hED).trans hEM) hPM

private theorem radical_unique {F : Type*} [Field F] [Finite F] [CharP F 2]
    (D : Subgroup H) (hD : D.IsCComponent) (f : D →* SL(2, F))
    (hf : Function.Surjective f) (S : Sylow 2 D) :
    Order.HasUniqueMaximalOver ((S : Subgroup D) ⊔ solvableRadical D) ⊤ := by
  let := hD.perfect
  have hk : f.ker ≤ solvableRadical D := by
    apply hD.le_solvableRadical_of_subnormal_proper (inferInstance : f.ker.Normal).isSubnormal
    intro he
    have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.mp he
    let t := Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F)
    obtain ⟨x, hx⟩ := hf t
    have ht : t = 1 := hx.symm.trans (by simp [hf1])
    have hh := congrArg (fun g : SL(2, F) => g.val 0 1) ht
    simp [t, Matrix.SpecialLinearGroup.transvection_coe] at hh
  exact Matrix.SpecialLinearGroup.sylow_sup_solvable_hasUniqueMaximalOver_of_perfect_cover
    f hf (solvableRadical D) hk S

/-- A minimal local C-component with an actual rank-one image has a unique
maximal Sylow overgroup in its normal Sylow extension. The nontrivial two-core
needed here is already part of full local-family membership, so the conclusion
also holds without a separate characteristic-two hypothesis on H. -/
theorem unique_maximal_of_minimal_rankOne_image {F : Type*} [Field F] [Finite F] [CharP F 2]
    (D : Subgroup H) [D.Normal] (hD : D.IsCComponent)
    (P : Sylow 2 H) (hgen : D ⊔ (P : Subgroup H) = ⊤)
    (hmin : Minimal (fun E => E ∈ Chapter1.L H (P : Subgroup H)) D)
    (f : D →* SL(2, F)) (hf : Function.Surjective f) :
    ∃! M : Subgroup H, IsCoatom M ∧ (P : Subgroup H) ≤ M := by
  let R := (solvableRadical D).map D.subtype
  let : R.Normal := inferInstanceAs (((solvableRadical D).map D.subtype).Normal)
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (D.subtype.subgroupMap_surjective (solvableRadical D))
  have hRD : R ≤ D := map_subtype_le _
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal D
  have he : (((S : Subgroup D) ⊔ solvableRadical D).map D.subtype) =
      D ⊓ ((P : Subgroup H) ⊔ R) := by
    rw [Subgroup.map_sup, hS, subgroupOf_map_subtype]
    change (P : Subgroup H) ⊓ D ⊔ R = D ⊓ ((P : Subgroup H) ⊔ R)
    apply le_antisymm
    · exact sup_le (le_inf inf_le_right (inf_le_left.trans le_sup_left))
        (le_inf hRD le_sup_right)
    · rintro x ⟨hxD, hx⟩
      obtain ⟨p, hp, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hx
      have hpD : p ∈ D := by
        have hh := D.mul_mem hxD (D.inv_mem (hRD hr))
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem_sup ⟨hp, hpD⟩ hr
  have huD := hasUniqueMaximalOver_map_subtype (radical_unique D hD f hf S)
  rw [he] at huD
  have hu := hasUniqueMaximalOver_sup_of_normalizes
    (show (P : Subgroup H) ⊔ R ≤ normalizer (D : Set H) from le_normalizer_of_normal) huD
  have hjoin : D ⊔ ((P : Subgroup H) ⊔ R) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le_sup_left le_sup_left D
  rw [hjoin] at hu
  obtain ⟨M, hM, _⟩ := hu.2
  refine ⟨M, ⟨hM.2.isCoatom, le_sup_left.trans hM.1⟩, ?_⟩
  intro N hN
  have hproper : N ⊔ R ≠ ⊤ := by
    intro hn
    exact hN.1.ne_top (eq_top_of_solvable_supplement D hD P hgen hmin R N hN.2 (sup_comm N R ▸ hn))
  have hNM : N ≤ M := le_sup_left.trans (hu.le_maximal hM
    (sup_le_sup_right hN.2 R) (lt_top_iff_ne_top.mpr hproper))
  exact ((hN.1.covBy_top.eq_or_eq hNM le_top).resolve_right hM.2.ne).symm

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal uniqueness witness for H = K₀Tᵥ, for every Sylow whose
embedded subgroup is Tᵥ. The input model uses the native plus quotient. -/
theorem local_join_unique_maximal
    (K₀ K L T : Subgroup G) (z v : G)
    (hK₀K : K₀ ≤ K)
    (hmin : Minimal (fun E => E ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F))
    (P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map
      (K₀ ⊔ Tv T v).subtype = Tv T v) :
    ∃! M : Subgroup (K₀ ⊔ Tv T v : Subgroup G), IsCoatom M ∧ (P : Subgroup _) ≤ M := by
  let H := K₀ ⊔ Tv T v
  let D := K₀.subgroupOf H
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le K₀.le_normalizer hn)
  have hD : D.IsCComponent := hmin.1.2.1
  have hmin' : Minimal (fun E => E ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀ :=
    ⟨⟨hK₀K.trans le_sup_left, hmin.1.2⟩, hmin.2⟩
  have hgen : D ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K₀ ≤ H from le_sup_left),
      hP, ← MonoidHom.range_eq_map, range_subtype]
  let i : D ≃* K₀ := subgroupOfEquivOfLe le_sup_left
  let f := e.toMonoidHom.comp ((componentMap K₀ L T z v hL hz).comp i.toMonoidHom)
  exact unique_maximal_of_minimal_rankOne_image D hD P hgen (minimal_local_in_join K₀ K T v hmin' P hP)
    f (e.surjective.comp ((componentMap_surjective K₀ L T z v hL hz).comp i.surjective))

/-- Discharge the remaining B.6.1 hypothesis using full minimality and the
native rank-one model; nonnormality is supplied by `LocalHypotheses`. -/
theorem local_minimalParabolic_of_rankOne_image
    (K₀ K L T : Subgroup G) (z v : G)
    (hK₀K : K₀ ≤ K)
    (hmin : Minimal (fun E => E ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F)) :
    ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
        ChapterB.IsMinimalParabolicOver P ⊤ :=
  local_minimalParabolic_of_unique_maximal K₀ L T z v hL hz hn e
    (local_join_unique_maximal K₀ K L T z v hK₀K hmin hL hz hn e)

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open HigherFieldParabolics

/-- The actual C.1.26 application with unique maximality discharged. The
independent source implication and 13.6.16(2) remain explicit inputs. -/
theorem block_alternatives_of_minimal_rankOne {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G)
    (K₀ K L T : Subgroup G) (z v : G)
    (hK₀K : K₀ ≤ K) (hK : K ≤ Gv v)
    (hmin : Minimal (fun E => E ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hv : orderOf v = 2)
    (hn : Tv T v ≤ normalizer (K₀ : Set G))
    (hpush : CharacteristicNormalizerObstruction (Tv T v) K₀)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F)) :
    ChapterC.IsBlock (K₀.subgroupOf (K₀ ⊔ Tv T v)) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K₀ n) ∨ ChapterC.IsAlternatingBlock K₀ 5) :=
  block_alternatives_of_unique_maximal choices source hG K₀ L T z v hL hz hv
    ⟨hK₀K.trans hK, hmin.1.2⟩ hn hpush hSylow hf e
    (local_join_unique_maximal K₀ K L T z v hK₀K hmin hL hz hn e)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry

end
