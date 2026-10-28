module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.Reduction
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PCoreSurjective

/-!
# Held quotient, action, and local-subgroup transport

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.3.9(7), printed p.526; GLS, volume 3, Table 5.3p, printed p.277.

The quotient map lands in the actual degree-2058 Held carrier. Its kernel
is the entire two-core of the component. Perfectness makes the induced
map on automorphisms faithful even when that central kernel is nontrivial.
The component Sylow subgroup is exactly the intersection with the supplied
Sylow subgroup, and its image is the model Sylow subgroup.

Fixed points lift exactly in this setup. On the preimage of the model's
fixed subgroup, displacement is a homomorphism into the central two-kernel.
It kills the component Sylow subgroup, hence its whole two-group image.
Consequently model generation with the fixed subgroup lifts to generation
with the actual ambient centralizer of z.

`componentPreimage` and `localOvergroup` give explicit subgroup constructions,
including preimage membership, normalizers, the central kernel, and the
intrinsic two-core. The actor group is the image of N_S(L); the full S is
adjoined only in `localOvergroup`. No normality of L under S is assumed.

`localGeometryOfPair` is conditional: construction of the concrete model
pair and self-centralization after adjoining S remain separate obligations.
In particular this module does not construct `heldLocalGeometry`. The two
E64 normalizer classes in Table 5.3p are fused by automorphisms; invariance
of a selected subgroup is a hypothesis here, never inferred from that table.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The specified quotient, followed by its actual Held model isomorphism. -/
def modelMap (d : SporadicQuotientInput L z .he) : L →* Held.He :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem modelMap_surjective (d : SporadicQuotientInput L z .he) :
    Function.Surjective (modelMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- No central two-kernel is discarded by the model map. -/
theorem modelMap_ker (d : SporadicQuotientInput L z .he) :
    (modelMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
  rw [map_eq_one_iff _ d.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

/-- Quasisimplicity is inherited from the source component, rather than separately certified for the carrier. -/
theorem model_quasisimple (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : IsQuasisimple Held.He := by
  let : IsQuasisimple L := h.quasisimple
  exact IsQuasisimple.of_surjective (modelMap d) (modelMap_surjective d)

/-- The model two-core is trivial because the source quotient removes the whole two-core. -/
theorem model_twoCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : pCore 2 Held.He = ⊥ := by
  let := h.finite
  have hk : IsPGroup 2 (modelMap d).ker := (modelMap_ker d).symm ▸ pCore_isPGroup
  apply comap_injective (modelMap_surjective d)
  rw [(modelMap d).comap_pCore_of_ker_isPGroup (modelMap_surjective d) hk]
  exact (modelMap_ker d).symm

/-- The genuine automorphism action on the characteristic two-core quotient. -/
def modelAut (d : SporadicQuotientInput L z .he) : MulAut L →* MulAut Held.He :=
  (MulAut.congr d.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

theorem modelAut_apply (d : SporadicQuotientInput L z .he) (a : MulAut L) (x : L) :
    modelAut d a (modelMap d x) = modelMap d (a x) := by
  change d.quotientIso (quotientAut (pCore 2 L) a
    (d.quotientIso.symm (d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [d.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Perfectness detects an automorphism from its action modulo the central two-kernel. -/
theorem modelAut_injective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : Function.Injective (modelAut d) := by
  let : IsQuasisimple L := h.quasisimple
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  apply MulAut.eq_one_of_central_displacement a
  intro x
  apply twoCore_le_center h d
  rw [← modelMap_ker d]
  change modelMap d (x⁻¹ * a x) = 1
  rw [map_mul, map_inv, ← modelAut_apply]
  change modelAut d a = 1 at ha
  rw [ha, MulAut.one_apply, inv_mul_cancel]

theorem modelAut_conj (d : SporadicQuotientInput L z .he) (x : L) :
    modelAut d (MulAut.conj x) = MulAut.conj (modelMap d x) := by
  ext y
  obtain ⟨y, rfl⟩ := modelMap_surjective d y
  rw [modelAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem modelAction_order (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : orderOf (modelAut d d.action) = 2 := by
  rw [orderOf_injective (modelAut d) (modelAut_injective h d)]
  exact h.action_order d.action d.conjugation

theorem modelAction_inner (d : SporadicQuotientInput L z .he) :
    modelAut d d.action ∈ (MulAut.conj (G := Held.He)).range := by
  obtain ⟨x, hx⟩ := d.inner
  exact ⟨modelMap d x, by rw [← hx, modelAut_conj]⟩

/-- The restricted Sylow subgroup; its underlying subgroup is uniquely determined by `componentSylow_map`. -/
def componentSylow (h : LocalSetup H L M S z) : Sylow 2 L :=
  h.exists_component_sylow.choose

theorem componentSylow_map (h : LocalSetup H L M S z) :
    (componentSylow h : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype := h.exists_component_sylow.choose_spec

/-- Membership is the actual intersection with the supplied S, independent of the existential presentation. -/
theorem mem_componentSylow (h : LocalSetup H L M S z) (x : L) :
    x ∈ (componentSylow h : Subgroup L) ↔
      (x : G) ∈ (S : Subgroup H).map H.subtype := by
  rw [← mem_map_iff_mem L.subtype_injective, componentSylow_map h]
  exact and_iff_right x.property

theorem componentSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (x : L)
    (hx : x ∈ (componentSylow h : Subgroup L)) : d.action x = x := by
  apply Subtype.ext
  rw [d.conjugation, ← h.central (x : G) ((mem_componentSylow h x).mp hx),
    mul_inv_cancel_right]

/-- The image of the actual component Sylow subgroup under the specified quotient. -/
def modelSylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : Sylow 2 Held.He := by
  let := h.finite
  exact (componentSylow h).mapSurjective (modelMap_surjective d)

theorem modelSylow_coe (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (modelSylow h d : Subgroup Held.He) = (componentSylow h).map (modelMap d) := rfl

theorem modelSylow_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (modelSylow h d : Subgroup Held.He).comap (modelMap d) = componentSylow h := by
  rw [modelSylow_coe, comap_map_eq_self]
  rw [modelMap_ker]
  exact pCore_isPGroup.le_sylow_of_normal _

theorem modelSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (x : Held.He)
    (hx : x ∈ (modelSylow h d : Subgroup Held.He)) : modelAut d d.action x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [modelAut_apply, componentSylow_fixed h d y hy]

/-- A central two-displacement vanishing on a Sylow subgroup vanishes everywhere in the fixed preimage. -/
theorem modelFixed_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (modelAut d d.action).fixedSubgroup.comap (modelMap d) = d.action.fixedSubgroup := by
  let := h.finite
  let V := (modelAut d d.action).fixedSubgroup.comap (modelMap d)
  have hdiff (x : V) : (x : L)⁻¹ * d.action x ∈ pCore 2 L := by
    rw [← modelMap_ker d]
    change modelMap d ((x : L)⁻¹ * d.action x) = 1
    rw [map_mul, map_inv, ← modelAut_apply]
    have hx : modelAut d d.action (modelMap d x) = modelMap d x :=
      (MulAut.mem_fixedSubgroup _ _).mp x.property
    rw [hx, inv_mul_cancel]
  let delta : V →* pCore 2 L := {
    toFun x := ⟨(x : L)⁻¹ * d.action x, hdiff x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change ((x : L) * y)⁻¹ * d.action ((x : L) * y) =
        ((x : L)⁻¹ * d.action x) * ((y : L)⁻¹ * d.action y)
      rw [mul_inv_rev, map_mul]
      have hc := mem_center_iff.mp (twoCore_le_center h d (hdiff x)) (y : L)⁻¹
      calc
        _ = ((y : L)⁻¹ * ((x : L)⁻¹ * d.action x)) * d.action y := by group
        _ = (((x : L)⁻¹ * d.action x) * (y : L)⁻¹) * d.action y := by rw [hc]
        _ = _ := by group }
  have hRV : (componentSylow h : Subgroup L) ≤ V := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [modelAut_apply, componentSylow_fixed h d x hx]
  let T := (componentSylow h).subtype hRV
  let U := T.mapSurjective delta.rangeRestrict_surjective
  have hU : (U : Subgroup delta.range) = ⊤ := by
    apply (U.is_maximal' (pCore_isPGroup.to_subgroup delta.range |>.to_subgroup ⊤) le_top).symm
  have hUbot : (U : Subgroup delta.range) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro y ⟨x, hx, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change (x : L)⁻¹ * d.action x = 1
    rw [componentSylow_fixed h d x hx, inv_mul_cancel]
  have hd (x : V) : delta x = 1 := by
    have hx : delta.rangeRestrict x ∈ (U : Subgroup delta.range) := hU.symm ▸ mem_top _
    rw [hUbot, mem_bot] at hx
    exact congrArg Subtype.val hx
  apply le_antisymm
  · intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hd' := congrArg Subtype.val (hd ⟨x, hx⟩)
    change x⁻¹ * d.action x = 1 at hd'
    exact (inv_mul_eq_one.mp hd').symm
  · intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [modelAut_apply, (MulAut.mem_fixedSubgroup _ _).mp hx]

/-- Pull a specified model subgroup back through the quotient and embed it in G. -/
def componentPreimage (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) : Subgroup G :=
  (P.comap (modelMap d)).map L.subtype

theorem mem_componentPreimage (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) (x : G) :
    x ∈ componentPreimage d P ↔ ∃ hx : x ∈ L, modelMap d ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

theorem componentPreimage_le (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) : componentPreimage d P ≤ L := map_subtype_le _

theorem componentPreimage_subgroupOf (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) :
    (componentPreimage d P).subgroupOf L = P.comap (modelMap d) :=
  comap_map_eq_self_of_injective L.subtype_injective _

theorem twoCore_le_componentPreimage (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) : L.pCoreIn 2 ≤ componentPreimage d P := by
  apply map_mono
  rw [← modelMap_ker d]
  exact MonoidHom.ker_le_comap _ _

theorem componentPreimage_sup (d : SporadicQuotientInput L z .he)
    (P Q : Subgroup Held.He) :
    componentPreimage d (P ⊔ Q) = componentPreimage d P ⊔ componentPreimage d Q := by
  unfold componentPreimage
  rw [← comap_sup_eq _ P Q (modelMap_surjective d), Subgroup.map_sup]

theorem componentPreimage_top (d : SporadicQuotientInput L z .he) :
    componentPreimage d ⊤ = L := by
  rw [componentPreimage, comap_top, ← MonoidHom.range_eq_map, range_subtype]

/-- Normalizer transport is relative to L, rather than an assertion of ambient normality. -/
theorem componentPreimage_normalizer (d : SporadicQuotientInput L z .he)
    (U : Subgroup Held.He) :
    componentPreimage d (normalizer U) = L ⊓ normalizer (componentPreimage d U) := by
  change ((normalizer U).comap (modelMap d)).map L.subtype = _
  rw [comap_normalizer_eq_of_surjective U (modelMap_surjective d),
    ← componentPreimage_subgroupOf d U,
    ← subgroupOf_normalizer_eq (componentPreimage_le d U), subgroupOf_map_subtype,
    inf_comm]

/-- The actual surjection from the intrinsic preimage onto its specified model subgroup. -/
def preimageMap (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He) :
    P.comap (modelMap d) →* P where
  toFun x := ⟨modelMap d x, x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

theorem preimageMap_surjective (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) : Function.Surjective (preimageMap d P) := by
  intro y
  obtain ⟨x, hx⟩ := modelMap_surjective d y
  exact ⟨⟨x, show modelMap d x ∈ P from hx.symm ▸ y.property⟩, Subtype.ext hx⟩

theorem preimageMap_ker (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He) :
    (preimageMap d P).ker = (pCore 2 L).subgroupOf (P.comap (modelMap d)) := by
  ext x
  change (⟨modelMap d x, _⟩ : P) = 1 ↔ (x : L) ∈ pCore 2 L
  rw [Subtype.ext_iff, ← modelMap_ker d]
  rfl

theorem preimageMap_ker_isPGroup (d : SporadicQuotientInput L z .he)
    (P : Subgroup Held.He) : IsPGroup 2 (preimageMap d P).ker := by
  rw [preimageMap_ker]
  exact pCore_isPGroup.comap_subtype

theorem preimageMap_ker_le_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He) :
    (preimageMap d P).ker ≤ center (P.comap (modelMap d)) := by
  rw [preimageMap_ker]
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp (twoCore_le_center h d hx) y

/-- The intrinsic local two-core is exactly the preimage of the model local two-core. -/
theorem preimageMap_pCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He) :
    (pCore 2 P).comap (preimageMap d P) = pCore 2 (P.comap (modelMap d)) := by
  let := h.finite
  exact (preimageMap d P).comap_pCore_of_ker_isPGroup
    (preimageMap_surjective d P) (preimageMap_ker_isPGroup d P)

/-- A self-centralizing model two-core lifts through the retained two-group kernel. -/
theorem preimage_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (P.comap (modelMap d)) : Set (P.comap (modelMap d))) ≤
      pCore 2 (P.comap (modelMap d)) := by
  intro x hx
  rw [← preimageMap_pCore h d P]
  apply hP
  intro y hy
  obtain ⟨y, rfl⟩ := preimageMap_surjective d P y
  have hy' : y ∈ pCore 2 (P.comap (modelMap d)) := by
    rwa [← preimageMap_pCore h d P]
  simpa only [map_mul] using congrArg (preimageMap d P) (hx y hy')

/-- The lifted fixed subgroup is exactly the component intersection with the ambient centralizer. -/
theorem componentPreimage_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    componentPreimage d (modelAut d d.action).fixedSubgroup =
      L ⊓ centralizer ({z} : Set G) := by
  rw [componentPreimage, modelFixed_preimage h d]
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := d.conjugation x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply (MulAut.mem_fixedSubgroup d.action ⟨x, hx⟩).mpr
    apply Subtype.ext
    rw [d.conjugation, ← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

/-- Adjoin the entire supplied subgroup to the actual preimage; it may permute components. -/
def localOvergroup (d : SporadicQuotientInput L z .he) (A : Subgroup G)
    (P : Subgroup Held.He) : Subgroup G := componentPreimage d P ⊔ A

theorem le_localOvergroup (d : SporadicQuotientInput L z .he) (A : Subgroup G)
    (P : Subgroup Held.He) : A ≤ localOvergroup d A P := le_sup_right

theorem localOvergroup_le (d : SporadicQuotientInput L z .he) (A : Subgroup G)
    (P : Subgroup Held.He) : localOvergroup d A P ≤ L ⊔ A :=
  sup_le_sup_right (componentPreimage_le d P) A

/-- The same overgroup contains every actual conjugate of its preimage under the adjoined subgroup. -/
theorem localOvergroup_orbit (d : SporadicQuotientInput L z .he) (A : Subgroup G)
    (P : Subgroup Held.He) :
    componentOrbit (componentPreimage d P) A ⊔ A = localOvergroup d A P :=
  componentOrbit_sup _ _

/-- The source involution makes the self-centralizing two-core nontrivial. -/
theorem localOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P : Subgroup Held.He)
    (he : localOvergroup d ((S : Subgroup H).map H.subtype) P ∈ Chapter1.He G) :
    localOvergroup d ((S : Subgroup H).map H.subtype) P ∈
      Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) := by
  refine ⟨he, ?_, le_localOvergroup d _ P⟩
  change (localOvergroup d ((S : Subgroup H).map H.subtype) P).pCoreIn 2 ≠ ⊥
  intro hb
  change _ ⊓ centralizer _ ≤ _ at he
  rw [hb] at he
  have hz := le_localOvergroup d ((S : Subgroup H).map H.subtype) P h.mem_sylow
  have hz1 : z = 1 := he ⟨hz, by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]⟩
  simpa [hz1] using h.involution

/-- Generation in the concrete quotient lifts with the actual centralizer, including central two-kernels. -/
theorem centralizer_localOvergroup_generation (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P Q : Subgroup Held.He)
    (hgen : (modelAut d d.action).fixedSubgroup ⊔ (P ⊔ Q) = ⊤) :
    L ≤ centralizer ({z} : Set G) ⊔
      (localOvergroup d ((S : Subgroup H).map H.subtype) P ⊔
        localOvergroup d ((S : Subgroup H).map H.subtype) Q) := by
  have he := congrArg (componentPreimage d) hgen
  rw [componentPreimage_top, componentPreimage_sup, componentPreimage_sup,
    componentPreimage_fixed h d] at he
  exact he.ge.trans (sup_le_sup inf_le_right (sup_le_sup le_sup_left le_sup_left))

/-- Conditional pair assembly. Both the model generation premise and the two ambient core conditions must still be discharged. -/
def localGeometryOfPair (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (P Q : Subgroup Held.He)
    (hgen : (modelAut d d.action).fixedSubgroup ⊔ (P ⊔ Q) = ⊤)
    (hP : localOvergroup d ((S : Subgroup H).map H.subtype) P ∈ Chapter1.He G)
    (hQ : localOvergroup d ((S : Subgroup H).map H.subtype) Q ∈ Chapter1.He G) :
    LocalGeometry L ((S : Subgroup H).map H.subtype) z where
  locals := {localOvergroup d ((S : Subgroup H).map H.subtype) P,
    localOvergroup d ((S : Subgroup H).map H.subtype) Q}
  generated := by
    simpa only [sSup_insert, sSup_singleton] using
      centralizer_localOvergroup_generation h d P Q hgen
  within := by
    intro K hK
    rcases Set.mem_insert_iff.mp hK with rfl | hK
    · exact localOvergroup_le d _ P
    · obtain rfl := Set.mem_singleton_iff.mp hK
      exact localOvergroup_le d _ Q
  even := by
    intro K hK
    rcases Set.mem_insert_iff.mp hK with rfl | hK
    · exact localOvergroup_mem_HeOver h d P hP
    · obtain rfl := Set.mem_singleton_iff.mp hK
      exact localOvergroup_mem_HeOver h d Q hQ

/-- Only N_A(L) acts on L; no action of all of A on L is asserted. -/
def normalizerModelAction (d : SporadicQuotientInput L z .he) (A : Subgroup G) :
    (A ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut Held.He :=
  (modelAut d).comp (L.normalizerMonoidHom.comp (inclusion inf_le_right))

theorem normalizerModelAction_apply (d : SporadicQuotientInput L z .he)
    (A : Subgroup G) (a : (A ⊓ normalizer (L : Set G) : Subgroup G)) (x : L) :
    normalizerModelAction d A a (modelMap d x) =
      modelMap d ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩ :=
  modelAut_apply d _ x

/-- The actual image of the normalizer action, including any outer automorphisms. -/
def modelActors (d : SporadicQuotientInput L z .he) (A : Subgroup G) :
    Subgroup (MulAut Held.He) := (normalizerModelAction d A).range

theorem modelActors_isPGroup (d : SporadicQuotientInput L z .he) :
    IsPGroup 2 (modelActors d ((S : Subgroup H).map H.subtype)) :=
  (S.isPGroup'.map H.subtype |>.to_inf_left (K := normalizer (L : Set G))).of_surjective
    (normalizerModelAction d ((S : Subgroup H).map H.subtype)).rangeRestrict
    (normalizerModelAction d ((S : Subgroup H).map H.subtype)).rangeRestrict_surjective

theorem normalizerModelAction_z (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    normalizerModelAction d ((S : Subgroup H).map H.subtype)
      ⟨z, h.mem_sylow, h.normalizes⟩ = modelAut d d.action := by
  apply congrArg (modelAut d)
  apply MulEquiv.ext
  intro x
  exact Subtype.ext (d.conjugation x).symm

theorem modelAction_mem_actors (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    modelAut d d.action ∈ modelActors d ((S : Subgroup H).map H.subtype) :=
  ⟨⟨z, h.mem_sylow, h.normalizes⟩, normalizerModelAction_z h d⟩

theorem modelAction_centralizes_actors (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    modelAut d d.action ∈ centralizer
      (modelActors d ((S : Subgroup H).map H.subtype) : Set (MulAut Held.He)) := by
  rintro a ⟨s, rfl⟩
  rw [← normalizerModelAction_z h d, ← map_mul, ← map_mul]
  apply congrArg (normalizerModelAction d ((S : Subgroup H).map H.subtype))
  exact Subtype.ext (h.central s s.property.1)

/-- The model actor group contains the inner action of the supplied model Sylow subgroup. -/
theorem modelActors_contains_inner_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (modelSylow h d : Subgroup Held.He).map MulAut.conj ≤
      modelActors d ((S : Subgroup H).map H.subtype) := by
  rintro a ⟨r, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨⟨(x : G), (mem_componentSylow h x).mp hx, L.le_normalizer x.property⟩, ?_⟩
  rw [← modelAut_conj]
  apply congrArg (modelAut d)
  ext y
  rfl

/-- Elements of N_S(L) preserve the actual component Sylow subgroup and its model image. -/
theorem modelActors_preserve_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (a : MulAut Held.He)
    (ha : a ∈ modelActors d ((S : Subgroup H).map H.subtype)) :
    (modelSylow h d : Subgroup Held.He).map a.toMonoidHom = modelSylow h d := by
  obtain ⟨s, rfl⟩ := ha
  have hstable (s : (((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) : Subgroup G))
      (r : Held.He) (hr : r ∈ (modelSylow h d : Subgroup Held.He)) :
      normalizerModelAction d ((S : Subgroup H).map H.subtype) s r ∈
        (modelSylow h d : Subgroup Held.He) := by
    obtain ⟨x, hx, rfl⟩ := hr
    rw [normalizerModelAction_apply]
    apply mem_map_of_mem
    apply (mem_componentSylow h _).mpr
    exact ((S : Subgroup H).map H.subtype).mul_mem
      (((S : Subgroup H).map H.subtype).mul_mem s.property.1
        ((mem_componentSylow h x).mp hx))
      (((S : Subgroup H).map H.subtype).inv_mem s.property.1)
  apply le_antisymm
  · rintro r ⟨x, hx, rfl⟩
    exact hstable s x hx
  · intro r hr
    refine ⟨normalizerModelAction d ((S : Subgroup H).map H.subtype) s⁻¹ r,
      hstable s⁻¹ r hr, ?_⟩
    rw [map_inv]
    exact MulEquiv.apply_symm_apply _ _

/-- Proved model invariance lifts to N_A(L)-normalization of the full preimage. -/
theorem componentPreimage_normalized (d : SporadicQuotientInput L z .he)
    (A : Subgroup G) (P : Subgroup Held.He)
    (hP : ∀ a ∈ modelActors d A, P.map a.toMonoidHom = P) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (componentPreimage d P) := by
  have hstable (s : (A ⊓ normalizer (L : Set G) : Subgroup G))
      (x : G) (hx : x ∈ componentPreimage d P) :
      (s : G) * x * (s : G)⁻¹ ∈ componentPreimage d P := by
    obtain ⟨x, hx, rfl⟩ := hx
    apply (mem_componentPreimage d P _).mpr
    refine ⟨(mem_normalizer_iff.mp s.property.2 x).mp x.property, ?_⟩
    have hm : normalizerModelAction d A s (modelMap d x) ∈ P := by
      rw [← hP _ ⟨s, rfl⟩]
      exact mem_map_of_mem _ hx
    exact (normalizerModelAction_apply d A s x) ▸ hm
  intro s hs
  apply mem_normalizer_iff.mpr
  intro x
  refine ⟨hstable ⟨s, hs⟩ x, ?_⟩
  intro hx
  have hi := hstable (⟨s, hs⟩ : (A ⊓ normalizer (L : Set G) : Subgroup G))⁻¹ _ hx
  simpa only [coe_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_assoc, inv_mul_cancel, mul_one] using hi

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
