module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Omega
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SylowFixer
public import Theory.Frattini.OmegaProducts

/-!
# The central Omega inclusions of Lemma 16.4(b)

The involutions of the local circle are precisely the distinguished
involutions in it. Thus the first Omega subgroup of T₁∩B° is the literal
circle T₁°. Pointwise Sylow innerness puts every central element of T₁
inside B°C_B(B°); the proved involution-product identity then bounds the
central Omega subgroup by T₁°⟨u⟩. The selected marks give the lower inclusion.

Source: GLS IV, Chapter 2, Lemma 16.4(b).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The involution-generated intersection with the distinguished circle is
exactly the distinguished circle of the smaller subgroup. -/
public theorem source16_omega_intersection_eq_localCircle
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) (T : Subgroup G) (hTF : T ≤ F) :
    omegaOneAmbient (T ⊓ localCircleIn Z F) = localCircleIn Z T := by
  let C := localCircle Z F
  let f := localCircleHom Z F
  have hf := localCircleHom_injective Z F
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    obtain ⟨xF,hxC,rfl⟩ := hx.2
    let xC : C := ⟨xF,hxC⟩
    have hxi : PFAppendixIII.IsInvolution xC := by
      refine ⟨fun he => hx1 (congrArg f he),?_⟩
      apply hf
      change (f xC) ^ 2 = 1 at hx2
      simpa only [map_pow,map_one] using hx2
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨localCircle_involution_mem h r F hF hFM hne hxi,hx.1⟩
  · rw [localCircleIn_eq_closure]
    apply (closure_le _).mpr
    rintro x ⟨hxZ,hxT⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl x
    · refine ⟨hxT,?_⟩
      rw [localCircleIn_eq_closure]
      exact subset_closure ⟨hxZ,hTF hxT⟩
    · exact (h.involutions x hxZ).sq_eq_one

/-- The circle Sylow supplied by normal intersection has exactly T₁° as
its mapped Omega subgroup. This is the intrinsic source identity Q=T₁°. -/
public theorem source16_sylow_omega_map_eq_localCircle
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) (T : Subgroup G) (hTF : T ≤ F)
    (P : Sylow 2 (localCircle Z F))
    (hP : (P : Subgroup (localCircle Z F)).map (localCircleHom Z F) =
      T ⊓ localCircleIn Z F) :
    (omegaOneAmbient (P : Subgroup (localCircle Z F))).map (localCircleHom Z F) =
      localCircleIn Z T := by
  rw [map_omegaOneAmbient_injective _ (localCircleHom_injective Z F),hP]
  exact source16_omega_intersection_eq_localCircle h r F hF hFM hne T hTF

/-- Lemma 16.4(b), with the actual mapped Sylow center and the literal
circle of T₁. The circle Sylow intersection is the normal-restriction output. -/
public theorem source16_central_omega_bounds
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (T : Subgroup G) (hTB : T ≤ centralizer ({u} : Set G))
    (huT : u ∈ T) (hzT : z ∈ T) (hTz : T ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (localCircle Z (centralizer ({u} : Set G))))
    (hP : (P : Subgroup (localCircle Z (centralizer ({u} : Set G)))).map
      (localCircleHom Z (centralizer ({u} : Set G))) =
      T ⊓ localCircleIn Z (centralizer ({u} : Set G))) :
    let B := centralizer ({u} : Set G)
    let L := localCircleIn Z B
    let J := B ⊓ centralizer (L : Set G)
    zpowers u ⊔ zpowers z ≤ omegaOneAmbient ((center T).map T.subtype) ∧
      omegaOneAmbient ((center T).map T.subtype) ≤ localCircleIn Z T ⊔ zpowers u ∧
      localCircleIn Z T ⊔ zpowers u = omegaOneAmbient (T ⊓ (L ⊔ J)) := by
  let B := centralizer ({u} : Set G)
  let L := localCircleIn Z B
  let J := B ⊓ centralizer (L : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  have hBM : ¬ B ≤ M := fun hh => htM (hh (mem_centralizer_singleton_iff.mpr htu.eq))
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩
  have hOmega := source16_omega_intersection_circle_centralizer h r ha hg hz hzM ht htM
    hu huD hzu htu hmax T huT
  have hQ := source16_omega_intersection_eq_localCircle h.disconnected r B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne T hTB
  change omegaOneAmbient (T ⊓ (L ⊔ J)) = omegaOneAmbient (T ⊓ L) ⊔ zpowers u at hOmega
  rw [hQ] at hOmega
  refine ⟨?_,?_,hOmega.symm⟩
  · apply sup_le
    · apply zpowers_le.mpr
      apply (omegaOneAmbient_le_iff _ _).mp le_rfl u _ hu.sq_eq_one
      refine ⟨⟨u,huT⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hTB x.property)
    · apply zpowers_le.mpr
      apply (omegaOneAmbient_le_iff _ _).mp le_rfl z _ (h.disconnected.involutions z hz).sq_eq_one
      refine ⟨⟨z,hzT⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hTz x.property)
  · rw [← hOmega]
    apply (omegaOneAmbient_le_iff _ _).mpr
    rintro x ⟨xT,hxC,rfl⟩ hx2
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl (xT : G) _ hx2
    refine ⟨xT.property,?_⟩
    have hxfix : (xT : G) ∈ B ⊓ centralizer ((P : Subgroup C).map f : Set G) := by
      refine ⟨hTB xT.property,?_⟩
      intro y hy
      have hyT := (hP ▸ hy).1
      exact congrArg Subtype.val (mem_center_iff.mp hxC (⟨y,hyT⟩ : T))
    have hh := source16_circle_sylow_centralizer_le h r ha hu huD.1 hBM
      (source16_centralizer_nonsolvable h r ha ht htM hu huD) P hxfix
    apply (sup_le_sup_right (show (omegaOneAmbient (P : Subgroup C)).map f ≤ L from ?_) J) hh
    intro y hy
    obtain ⟨c,_,rfl⟩ := hy
    exact mem_map_of_mem B.subtype c.property

end BenderSuzuki.ZD
