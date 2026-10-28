module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals

/-!
# Constructed G₂ parabolics in the literal plus quotient

Pull back both standard root parabolics through the actual map K → K⁺ and
an isomorphism K⁺ ≃ G₂(F). The full parabolics are maximal inside K. Their
residual images generate K⁺, so the parent's plus-generation theorem selects
one moving z. Sylow conjugacy aligns the genuine two-subgroup Tᵥ ∩ K with
the standard positive roots, yielding the required parabolic containment.

The plus residual has its literal PSL₂ core quotient. If the relative action
kernel C_K(W_K) is a two-group, the intrinsic residual has the same core
quotient, and the two explicit root triples prove non-shortness in its actual
ambient embedding. No non-shortness or moving-parabolic witness is assumed.

These are conditional construction results, not the full 13.6.19 branch.
The source assembly still must obtain a marked octonion quotient action and
control its kernel from the genuine B.5 and earlier local hypotheses. It also
must prove Tᵥ-invariance, Chapter 1 local-family membership, and minimal
parabolicity inside P∞Tᵥ, with the SQTK and characteristic-two inputs to C.1.26.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.14,
13.6.16 and 13.6.19, printed pp.929–931.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2
open ComponentSelection
open Atlas.G2.HigherFieldResiduals
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

private theorem le_actor : K ≤ plusActor K L T v :=
  (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)

/-- The actual quotient action restricted to K, with codomain exactly K⁺. -/
def componentMap : K →* plusImage K L T z v hL hz K :=
  ((plusMk K L T z v hL hz).comp (inclusion (by exact le_actor K L T v))).codRestrict _
    (fun x => mem_map.mpr ⟨inclusion (by exact le_actor K L T v) x, x.property, rfl⟩)

theorem componentMap_surjective : Function.Surjective (componentMap K L T z v hL hz) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The kernel retains the literal relative centralizer of W_K. -/
theorem componentMap_ker : (componentMap K L T z v hL hz).ker =
    (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext x
  change componentMap K L T z v hL hz x = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion (le_actor K L T v) x ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

variable {F : Type*} [Field F] [CharP F 2]
variable (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)

/-- The model marking is on the actual plus image, never an unrelated family tag. -/
def modelMap : K →* Atlas.G2.Model F :=
  e.toMonoidHom.comp (componentMap K L T z v hL hz)

omit [CharP F 2] in
theorem modelMap_surjective : Function.Surjective (modelMap K L T z v hL hz e) :=
  e.surjective.comp (componentMap_surjective K L T z v hL hz)

omit [CharP F 2] in
theorem modelMap_ker : (modelMap K L T z v hL hz e).ker =
    (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  rw [modelMap, MonoidHom.ker_comp_of_injective _ _ e.injective, componentMap_ker]

/-- The full root parabolic pulled back to K and then embedded in G. -/
def liftedParabolic (i : Fin 2) : Subgroup G :=
  ((parabolicAt i).comap (modelMap K L T z v hL hz e)).map K.subtype

omit [CharP F 2] in
theorem liftedParabolic_le (i : Fin 2) : liftedParabolic K L T z v hL hz e i ≤ K :=
  map_subtype_le _

omit [CharP F 2] in
theorem liftedParabolic_subgroupOf (i : Fin 2) :
    (liftedParabolic K L T z v hL hz e i).subgroupOf K =
      (parabolicAt i).comap (modelMap K L T z v hL hz e) :=
  comap_map_eq_self_of_injective K.subtype_injective _

/-- Maximality is relative to K, as in the source. -/
theorem liftedParabolic_maximal (i : Fin 2) :
    IsCoatom ((liftedParabolic K L T z v hL hz e i).subgroupOf K) := by
  rw [liftedParabolic_subgroupOf]
  exact isCoatom_comap_of_surjective (modelMap_surjective K L T z v hL hz e)
    (parabolicAt_isCoatom i)

omit [CharP F 2] in
theorem sylow_intersection_le_liftedParabolic (i : Fin 2)
    (hmark : ((Tv T v ⊓ K).subgroupOf K).map (modelMap K L T z v hL hz e) ≤
      Atlas.G2.unipotent) : Tv T v ⊓ K ≤ liftedParabolic K L T z v hL hz e i := by
  intro x hx
  refine ⟨⟨x,hx.2⟩, ?_, rfl⟩
  exact unipotent_le_parabolicAt i (hmark (mem_map_of_mem _ hx))

private theorem residualIn_map {X Y : Type*} [Group X] [Group Y] [Finite X]
    (P : Subgroup X) (f : X →* Y) :
    (residualIn P).map f = residualIn (P.map f) := by
  have h := congrArg (fun S => S.map (P.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap P) (f.subgroupMap_surjective P))
  have hf : (P.map f).subtype.comp (f.subgroupMap P) = f.comp P.subtype := by
    ext x
    rfl
  simpa only [residualIn, map_map, hf] using h

private theorem residualIn_subgroupOf [Finite G] (P : Subgroup G) (hP : P ≤ K) :
    residualIn (P.subgroupOf K) = (residualIn P).subgroupOf K := by
  apply map_injective K.subtype_injective
  rw [residualIn_map, map_subgroupOf_eq_of_le hP,
    map_subgroupOf_eq_of_le ((map_subtype_le _).trans hP)]

/-- Each lifted residual has exactly the designated root-local image. -/
theorem lifted_residual_image [Finite G] [Finite F] (hq : 2 < Nat.card F) (i : Fin 2) :
    ((residualIn (liftedParabolic K L T z v hL hz e i)).subgroupOf K).map
      (modelMap K L T z v hL hz e) = localAt i := by
  rw [← residualIn_subgroupOf K _ (liftedParabolic_le K L T z v hL hz e i),
    liftedParabolic_subgroupOf]
  exact preimage_residual_image _ (modelMap_surjective K L T z v hL hz e) hq i

private theorem plusImage_of_le (A : Subgroup G) (hA : A ≤ K) :
    plusImage K L T z v hL hz A =
      ((A.subgroupOf K).map (componentMap K L T z v hL hz)).map
        (plusImage K L T z v hL hz K).subtype := by
  have he : (plusImage K L T z v hL hz K).subtype.comp
      (componentMap K L T z v hL hz) =
      (plusMk K L T z v hL hz).comp (inclusion (le_actor K L T v)) := rfl
  rw [map_map, he, ← map_map]
  have ha : (A.subgroupOf K).map (inclusion (le_actor K L T v)) =
      A.subgroupOf (plusActor K L T v) := by
    apply map_injective (plusActor K L T v).subtype_injective
    rw [map_map, subtype_comp_inclusion, map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le (hA.trans (le_actor K L T v))]
  rw [ha]
  rfl

/-- The two lifted residual images generate the literal plus image of K. -/
theorem lifted_residuals_plus_generate [Finite G] [Finite F] (hq : 2 < Nat.card F) :
    plusImage K L T z v hL hz K =
      plusImage K L T z v hL hz (residualIn (liftedParabolic K L T z v hL hz e 0)) ⊔
        plusImage K L T z v hL hz (residualIn (liftedParabolic K L T z v hL hz e 1)) := by
  have hqgen :
      ((residualIn (liftedParabolic K L T z v hL hz e 0)).subgroupOf K).map
          (componentMap K L T z v hL hz) ⊔
        ((residualIn (liftedParabolic K L T z v hL hz e 1)).subgroupOf K).map
          (componentMap K L T z v hL hz) = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_map, map_map]
    change ((residualIn (liftedParabolic K L T z v hL hz e 0)).subgroupOf K).map
        (modelMap K L T z v hL hz e) ⊔
      ((residualIn (liftedParabolic K L T z v hL hz e 1)).subgroupOf K).map
        (modelMap K L T z v hL hz e) = _
    rw [lifted_residual_image K L T z v hL hz e hq 0,
      lifted_residual_image K L T z v hL hz e hq 1,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
    exact Atlas.G2.HigherFieldResiduals.locals_generate
  rw [plusImage_of_le K L T z v hL hz _
      ((map_subtype_le _).trans (liftedParabolic_le K L T z v hL hz e 0)),
    plusImage_of_le K L T z v hL hz _
      ((map_subtype_le _).trans (liftedParabolic_le K L T z v hL hz e 1)),
    ← Subgroup.map_sup, hqgen, ← MonoidHom.range_eq_map, range_subtype]

/-- Source 13.6.19's moving choice, obtained from the two constructed maximal
parabolics by the parent's literal plus-generation argument. The marked
Sylow arrangement is retained explicitly for the remaining local geometry. -/
theorem exists_moving_maximal_parabolic [Finite G] [Finite F] (hq : 2 < Nat.card F)
    (hK : K ∈ Yz L T z v)
    (hmark : ((Tv T v ⊓ K).subgroupOf K).map (modelMap K L T z v hL hz e) ≤
      Atlas.G2.unipotent)
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    ∃ i : Fin 2, let P := liftedParabolic K L T z v hL hz e i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) := by
  obtain ⟨P, hP, hPK, hmove⟩ := moving_residual_of_plus_generation K L T
    (liftedParabolic K L T z v hL hz e 0) (liftedParabolic K L T z v hL hz e 1)
    z v hL hz (liftedParabolic_le K L T z v hL hz e 0)
    (liftedParabolic_le K L T z v hL hz e 1)
    (lifted_residuals_plus_generate K L T z v hL hz e hq).le hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · exact ⟨0, hPK.trans hK.1.1, hPK,
      sylow_intersection_le_liftedParabolic K L T z v hL hz e 0 hmark,
      liftedParabolic_maximal K L T z v hL hz e 0, hmove⟩
  · exact ⟨1, hPK.trans hK.1.1, hPK,
      sylow_intersection_le_liftedParabolic K L T z v hL hz e 1 hmark,
      liftedParabolic_maximal K L T z v hL hz e 1, hmove⟩



open scoped MatrixGroups

/-- The intrinsic residual of the preimage and its actual ambient embedding. -/
noncomputable def liftedResidualEquiv [Finite G] :
    (i : Fin 2) →
      solvableResidual ((parabolicAt i).comap (modelMap K L T z v hL hz e)) ≃*
        residualIn (liftedParabolic K L T z v hL hz e i) := fun i =>
  (((parabolicAt i).comap (modelMap K L T z v hL hz e)).equivMapOfInjective
    K.subtype K.subtype_injective).solvableResidualEquiv.trans
      ((solvableResidual (liftedParabolic K L T z v hL hz e i)).equivMapOfInjective
        (liftedParabolic K L T z v hL hz e i).subtype
        (liftedParabolic K L T z v hL hz e i).subtype_injective)

/-- The intrinsic two-core quotient of the actual lifted residual is PSL₂.
This is a different quotient from its plus image, and the two-group kernel
is an essential explicit premise of this lifting theorem. -/
noncomputable def liftedResidualCoreQuotientEquivPSL [Finite G] [Finite F]
    (hq : 2 < Nat.card F)
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) (i : Fin 2) :
    (residualIn (liftedParabolic K L T z v hL hz e i) ⧸
      pCore 2 (residualIn (liftedParabolic K L T z v hL hz e i))) ≃*
      PSL(2,F) :=
  (QuotientGroup.congr _ _ (liftedResidualEquiv K L T z v hL hz e i).symm
    (pCore_map_iso 2 (liftedResidualEquiv K L T z v hL hz e i).symm)).trans
      (preimageResidualCoreQuotientEquivPSL (modelMap K L T z v hL hz e)
        (modelMap_surjective K L T z v hL hz e) hq
        (by rwa [modelMap_ker]) i)

/-- The highest-root commutator witnesses non-shortness in the actual extension,
by lifting the core and transporting to its original ambient embedding. -/
theorem lifted_residual_not_short [Finite G] [Finite F]
    (hq : 2 < Nat.card F)
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) (i : Fin 2) :
    ¬ ChapterC.IsShort (residualIn (liftedParabolic K L T z v hL hz e i)) := by
  let R := residualIn (liftedParabolic K L T z v hL hz e i)
  let R₀ := solvableResidual ((parabolicAt i).comap (modelMap K L T z v hL hz e))
  let a := liftedResidualEquiv K L T z v hL hz e i
  have h₀ : ⁅⁅pCore 2 R₀, (⊤ : Subgroup R₀)⁆, pCore 2 R₀⁆ ≠ ⊥ :=
    preimage_residual_core_triple (modelMap K L T z v hL hz e)
      (modelMap_surjective K L T z v hL hz e) hq (by rwa [modelMap_ker]) i
  have hr : ⁅⁅pCore 2 R, (⊤ : Subgroup R)⁆, pCore 2 R⁆ ≠ ⊥ := by
    intro h
    apply h₀
    have hm := congrArg (Subgroup.map a.symm.toMonoidHom) h
    rw [map_commutator, map_commutator, pCore_map_iso, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr a.symm.surjective, Subgroup.map_bot] at hm
    exact hm
  apply not_short_of_core_triple R (R.pCoreIn 2) (R.pCoreIn 2) le_rfl le_rfl
  intro h
  apply hr
  apply map_injective R.subtype_injective
  rw [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot]
  exact h

/-- The literal plus image of the lifted residual, identified with its root local.
The equivalence follows from the original quotient map on K and the proved
residual image; it makes no claim about the action kernel upstairs. -/
noncomputable def plusResidualEquivLocal [Finite G] [Finite F]
    (hq : 2 < Nat.card F) (i : Fin 2) :
    plusImage K L T z v hL hz (residualIn (liftedParabolic K L T z v hL hz e i)) ≃*
      localAt (F := F) i := by
  let R := residualIn (liftedParabolic K L T z v hL hz e i)
  let Q := (R.subgroupOf K).map (componentMap K L T z v hL hz)
  have hR : R ≤ K := (map_subtype_le _).trans (liftedParabolic_le K L T z v hL hz e i)
  have hQ : Q.map e.toMonoidHom = localAt i := by
    rw [map_map]
    exact lifted_residual_image K L T z v hL hz e hq i
  exact ((MulEquiv.subgroupCongr (by exact plusImage_of_le K L T z v hL hz R hR)).trans
    (Q.equivMapOfInjective (plusImage K L T z v hL hz K).subtype
      (plusImage K L T z v hL hz K).subtype_injective).symm).trans
        ((Q.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hQ))

/-- The literal K₁⁺/O₂(K₁⁺) quotient in 13.6.19. -/
noncomputable def plusResidualCoreQuotientEquivPSL [Finite G] [Finite F]
    (hq : 2 < Nat.card F) (i : Fin 2) :
    (plusImage K L T z v hL hz (residualIn (liftedParabolic K L T z v hL hz e i)) ⧸
      pCore 2 (plusImage K L T z v hL hz
        (residualIn (liftedParabolic K L T z v hL hz e i)))) ≃* PSL(2,F) :=
  (QuotientGroup.congr _ _ (plusResidualEquivLocal K L T z v hL hz e hq i)
    (pCore_map_iso 2 (plusResidualEquivLocal K L T z v hL hz e hq i))).trans
      (localCoreQuotientEquivPSL i)

/-- A conjugate of the model marking places the actual two-subgroup T_v∩K
in the standard positive roots. The quotient marking itself is retained. -/
theorem exists_aligned_marking [Finite G] [Finite F]
    (hK : K ∈ Yz L T z v) :
    ∃ g : Atlas.G2.Model F,
      ((Tv T v ⊓ K).subgroupOf K).map
        (modelMap K L T z v hL hz (e.trans (MulAut.conj g))) ≤ Atlas.G2.unipotent := by
  have hp : IsPGroup 2 (Tv T v) := (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1
  have hi : IsPGroup 2 ((Tv T v ⊓ K).subgroupOf K) :=
    (hp.to_le inf_le_left).comap_subtype
  obtain ⟨S,hS⟩ := (hi.map (modelMap K L T z v hL hz e)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) S
    (Atlas.G2.LieParabolicSetup.sylow (F := F))
  refine ⟨g, ?_⟩
  have hm : (S : Subgroup (Atlas.G2.Model F)).map (MulAut.conj g).toMonoidHom =
      Atlas.G2.unipotent := by
    rw [← Atlas.G2.LieParabolicSetup.sylow_coe, ← hg,
      Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have he : modelMap K L T z v hL hz (e.trans (MulAut.conj g)) =
      (MulAut.conj g).toMonoidHom.comp (modelMap K L T z v hL hz e) := rfl
  rw [he, ← map_map]
  exact (map_mono hS).trans_eq hm


/-- Construct the moving maximal parabolic from the actual component and plus
model. Its non-shortness and both PSL₂ core quotients are proved, with only the
relative action-kernel condition still explicit. Local-family membership and
minimal-parabolic geometry in P∞T_v are subsequent source obligations. -/
theorem exists_moving_nonshort_parabolic [Finite G] [Finite F]
    (hq : 2 < Nat.card F) (hK : K ∈ Yz L T z v)
    (hm : ¬ K ≤ centralizer ({z} : Set G))
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) :
    ∃ (g : Atlas.G2.Model F) (i : Fin 2),
      let e' := e.trans (MulAut.conj g)
      let P := liftedParabolic K L T z v hL hz e' i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((residualIn P ⧸ pCore 2 (residualIn P)) ≃* PSL(2,F)) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2,F)) := by
  obtain ⟨g,hg⟩ := exists_aligned_marking K L T z v hL hz e hK
  let e' := e.trans (MulAut.conj g)
  obtain ⟨i,hv,hPK,hT,hmax,hmove⟩ :=
    exists_moving_maximal_parabolic K L T z v hL hz e' hq hK hg hm
  exact ⟨g,i,hv,hPK,hT,hmax,hmove,
    lifted_residual_not_short K L T z v hL hz e' hq hk i,
    ⟨liftedResidualCoreQuotientEquivPSL K L T z v hL hz e' hq hk i⟩,
    ⟨plusResidualCoreQuotientEquivPSL K L T z v hL hz e' hq i⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2

end
