module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.SubnormalBlocks
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.Quasithin.EvenCharacteristic

/-!
# The actual Rudvalis central quotient and fixed lifts

The specified quotient map is always `quotientMap d : L →* Rudvalis.Model`,
with kernel O₂(L). Perfectness makes its induced automorphism action faithful.
The fixed-subgroup two-residual lifts through the central two-kernel, while the
original component Sylow subgroup is fixed pointwise and supplies the Sylow
supplement. Thus the full fixed subgroup is the image of the original C_L(z).

The model center embeds in the two-group center of its actual max6 subgroup;
triviality of the model two-core then makes that center trivial. Consequently
Z(L) = O₂(L), and the source quasisimplicity supplies model simplicity. None
of these steps discards the central kernel of L. Only N_S(L) acts on L.

The preimage and action transport follows the existing M₁₂ central-cover
transport, with its actual maps retained for Rudvalis. Source: Aschbacher–Smith,
2.3.9(7), printed p.526; GLS3 Table 5.3r, printed p.279.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry
open Subgroup Theory.GroupTheory Rudvalis
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Surjectivity is inherited from the source quotient identification. -/
theorem quotientMap_surjective (d : SporadicQuotientInput L z .ru) :
    Function.Surjective (quotientMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)



/-- The image of genuinely centralizing elements in the component. -/
noncomputable def centralizerImage (d : SporadicQuotientInput L z .ru) : Subgroup Model :=
  ((centralizer ({z} : Set G)).subgroupOf L).map (quotientMap d)

/-- The full inverse image, embedded in G without removing its central kernel. -/
noncomputable def componentPreimage (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : Subgroup G := (P.comap (quotientMap d)).map L.subtype

/-- Adjoin the supplied subgroup; it may permute conjugate components of H. -/
noncomputable def localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : Subgroup G := componentPreimage d P ⊔ A

/-- The lifted parabolic stays in the distinguished component. -/
theorem componentPreimage_le (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : componentPreimage d P ≤ L := map_subtype_le _

/-- The construction contains the actual supplied subgroup. -/
theorem le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : A ≤ localOvergroup A d P := le_sup_right

/-- The construction lies in the required join LS. -/
theorem localOvergroup_le (A : Subgroup G) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : localOvergroup A d P ≤ L ⊔ A :=
  sup_le_sup (componentPreimage_le d P) le_rfl

/-- The whole embedded two-kernel survives in every constructed overgroup. -/
theorem pCoreIn_le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : L.pCoreIn 2 ≤ localOvergroup A d P := by
  apply le_trans (map_mono (f := L.subtype) ?_) le_sup_left
  rw [← quotientMap_ker d]
  exact MonoidHom.ker_le_comap _ _

/-- Generation lifts because the full kernel is already in the lifted parabolic. -/
theorem generated_of_model_join (A : Subgroup G) (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) (hg : centralizerImage d ⊔ P = ⊤) :
    L ≤ centralizer ({z} : Set G) ⊔ localOvergroup A d P := by
  let U := centralizer ({z} : Set G) ⊔ localOvergroup A d P
  have hP : P ≤ (U.subgroupOf L).map (quotientMap d) := by
    intro x hx
    obtain ⟨y, rfl⟩ := quotientMap_surjective d x
    refine ⟨y, ?_, rfl⟩
    exact (show localOvergroup A d P ≤ U from le_sup_right)
      ((show componentPreimage d P ≤ localOvergroup A d P from le_sup_left) ⟨y, hx, rfl⟩)
  have hC : centralizerImage d ≤ (U.subgroupOf L).map (quotientMap d) :=
    map_mono (comap_mono le_sup_left)
  have htop : (U.subgroupOf L).map (quotientMap d) = ⊤ :=
    top_unique (hg ▸ sup_le hC hP)
  have hk : (quotientMap d).ker ≤ U.subgroupOf L := by
    intro x hx
    apply (show localOvergroup A d P ≤ U from le_sup_right)
    apply (show componentPreimage d P ≤ localOvergroup A d P from le_sup_left)
    exact ⟨x, MonoidHom.ker_le_comap _ _ hx, rfl⟩
  have he := congrArg (Subgroup.comap (quotientMap d)) htop
  have hU : U.subgroupOf L = ⊤ := by
    simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using he
  exact subgroupOf_eq_top.mp hU



/-- The genuine automorphism action on the characteristic two-core quotient. -/
def modelAut (d : SporadicQuotientInput L z .ru) : MulAut L →* MulAut Model :=
  (MulAut.congr d.quotientIso).toMonoidHom.comp (quotientAut (pCore 2 L))

theorem modelAut_apply (d : SporadicQuotientInput L z .ru) (a : MulAut L) (x : L) :
    modelAut d a (quotientMap d x) = quotientMap d (a x) := by
  change d.quotientIso (quotientAut (pCore 2 L) a
    (d.quotientIso.symm (d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)))) = _
  rw [d.quotientIso.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Perfectness detects an automorphism from its action modulo the central two-kernel. -/
theorem modelAut_injective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : Function.Injective (modelAut d) := by
  let : IsQuasisimple L := h.quasisimple
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  apply MulAut.eq_one_of_central_displacement a
  intro x
  apply twoCore_le_center h d
  rw [← quotientMap_ker d]
  change quotientMap d (x⁻¹ * a x) = 1
  rw [map_mul, map_inv, ← modelAut_apply]
  change modelAut d a = 1 at ha
  rw [ha, MulAut.one_apply, inv_mul_cancel]

theorem modelAut_conj (d : SporadicQuotientInput L z .ru) (x : L) :
    modelAut d (MulAut.conj x) = MulAut.conj (quotientMap d x) := by
  ext y
  obtain ⟨y, rfl⟩ := quotientMap_surjective d y
  rw [modelAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem modelAction_order (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : orderOf (modelAut d d.action) = 2 := by
  rw [orderOf_injective (modelAut d) (modelAut_injective h d)]
  exact h.action_order d.action d.conjugation

theorem modelAction_inner (d : SporadicQuotientInput L z .ru) :
    modelAut d d.action ∈ (MulAut.conj (G := Model)).range := by
  obtain ⟨x, hx⟩ := d.inner
  exact ⟨quotientMap d x, by rw [← hx, modelAut_conj]⟩

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
    (d : SporadicQuotientInput L z .ru) (x : L)
    (hx : x ∈ (componentSylow h : Subgroup L)) : d.action x = x := by
  obtain ⟨R, hR, hfix⟩ := h.exists_fixed_component_sylow d.action d.conjugation
  have he : (componentSylow h : Subgroup L) = R :=
    (Subgroup.map_injective L.subtype_injective) ((componentSylow_map h).trans hR.symm)
  exact hfix x (he ▸ hx)

/-- The image of the actual component Sylow subgroup under the specified quotient. -/
def modelSylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : Sylow 2 Model := by
  let := h.finite
  exact (componentSylow h).mapSurjective (quotientMap_surjective d)

theorem modelSylow_coe (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    (modelSylow h d : Subgroup Model) = (componentSylow h).map (quotientMap d) := rfl

theorem modelSylow_preimage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    (modelSylow h d : Subgroup Model).comap (quotientMap d) = componentSylow h := by
  rw [modelSylow_coe, comap_map_eq_self]
  rw [quotientMap_ker]
  exact pCore_isPGroup.le_sylow_of_normal _

theorem modelSylow_fixed (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (x : Model)
    (hx : x ∈ (modelSylow h d : Subgroup Model)) : modelAut d d.action x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [modelAut_apply, componentSylow_fixed h d y hy]

theorem mem_componentPreimage (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) (x : G) :
    x ∈ componentPreimage d P ↔ ∃ hx : x ∈ L, quotientMap d ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

/-- The actual surjection from the intrinsic preimage onto its specified model subgroup. -/
def preimageMap (d : SporadicQuotientInput L z .ru) (P : Subgroup Model) :
    P.comap (quotientMap d) →* P where
  toFun x := ⟨quotientMap d x, x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

theorem preimageMap_surjective (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : Function.Surjective (preimageMap d P) := by
  intro y
  obtain ⟨x, hx⟩ := quotientMap_surjective d y
  exact ⟨⟨x, show quotientMap d x ∈ P from hx.symm ▸ y.property⟩, Subtype.ext hx⟩

theorem preimageMap_ker (d : SporadicQuotientInput L z .ru) (P : Subgroup Model) :
    (preimageMap d P).ker = (pCore 2 L).subgroupOf (P.comap (quotientMap d)) := by
  ext x
  change (⟨quotientMap d x, _⟩ : P) = 1 ↔ (x : L) ∈ pCore 2 L
  rw [Subtype.ext_iff, ← quotientMap_ker d]
  rfl

theorem preimageMap_ker_isPGroup (d : SporadicQuotientInput L z .ru)
    (P : Subgroup Model) : IsPGroup 2 (preimageMap d P).ker := by
  rw [preimageMap_ker]
  exact pCore_isPGroup.comap_subtype

theorem preimageMap_ker_le_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (P : Subgroup Model) :
    (preimageMap d P).ker ≤ center (P.comap (quotientMap d)) := by
  rw [preimageMap_ker]
  intro x hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp (twoCore_le_center h d hx) y

/-- The intrinsic local two-core is exactly the preimage of the model local two-core. -/
theorem preimageMap_pCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (P : Subgroup Model) :
    (pCore 2 P).comap (preimageMap d P) = pCore 2 (P.comap (quotientMap d)) := by
  let := h.finite
  exact (preimageMap d P).comap_pCore_of_ker_isPGroup
    (preimageMap_surjective d P) (preimageMap_ker_isPGroup d P)

/-- A self-centralizing model two-core lifts through the retained two-group kernel. -/
theorem preimage_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (P : Subgroup Model)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 (P.comap (quotientMap d)) : Set (P.comap (quotientMap d))) ≤
      pCore 2 (P.comap (quotientMap d)) := by
  intro x hx
  rw [← preimageMap_pCore h d P]
  apply hP
  intro y hy
  obtain ⟨y, rfl⟩ := preimageMap_surjective d P y
  have hy' : y ∈ pCore 2 (P.comap (quotientMap d)) := by
    rwa [← preimageMap_pCore h d P]
  simpa only [map_mul] using congrArg (preimageMap d P) (hx y hy')

/-- Only N_A(L) acts on L; no action of all of A on L is asserted. -/
def normalizerModelAction (d : SporadicQuotientInput L z .ru) (A : Subgroup G) :
    (A ⊓ normalizer (L : Set G) : Subgroup G) →* MulAut Model :=
  (modelAut d).comp (L.normalizerMonoidHom.comp (inclusion inf_le_right))

theorem normalizerModelAction_apply (d : SporadicQuotientInput L z .ru)
    (A : Subgroup G) (a : (A ⊓ normalizer (L : Set G) : Subgroup G)) (x : L) :
    normalizerModelAction d A a (quotientMap d x) =
      quotientMap d ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp a.property.2 x).mp x.property⟩ :=
  modelAut_apply d _ x

/-- The image of the component stabilizer's actual quotient action. -/
def modelActors (d : SporadicQuotientInput L z .ru) (A : Subgroup G) :
    Subgroup (MulAut Model) := (normalizerModelAction d A).range

/-- Elements of N_S(L) preserve the actual component Sylow subgroup and its model image. -/
theorem modelActors_preserve_sylow (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) (a : MulAut Model)
    (ha : a ∈ modelActors d ((S : Subgroup H).map H.subtype)) :
    (modelSylow h d : Subgroup Model).map a.toMonoidHom = modelSylow h d := by
  obtain ⟨s, rfl⟩ := ha
  have hstable (s : (((S : Subgroup H).map H.subtype) ⊓ normalizer (L : Set G) : Subgroup G))
      (r : Model) (hr : r ∈ (modelSylow h d : Subgroup Model)) :
      normalizerModelAction d ((S : Subgroup H).map H.subtype) s r ∈
        (modelSylow h d : Subgroup Model) := by
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
theorem componentPreimage_normalized (d : SporadicQuotientInput L z .ru)
    (A : Subgroup G) (P : Subgroup Model)
    (hP : ∀ a ∈ modelActors d A, P.map a.toMonoidHom = P) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (componentPreimage d P) := by
  have hstable (s : (A ⊓ normalizer (L : Set G) : Subgroup G))
      (x : G) (hx : x ∈ componentPreimage d P) :
      (s : G) * x * (s : G)⁻¹ ∈ componentPreimage d P := by
    obtain ⟨x, hx, rfl⟩ := hx
    apply (mem_componentPreimage d P _).mpr
    refine ⟨(mem_normalizer_iff.mp s.property.2 x).mp x.property, ?_⟩
    have hm : normalizerModelAction d A s (quotientMap d x) ∈ P := by
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




/-- The actual fixed subgroup in L embeds in the ambient involution centralizer. -/
theorem fixedSubgroup_eq_centralizer (d : SporadicQuotientInput L z .ru) :
    d.action.fixedSubgroup = (centralizer ({z} : Set G)).subgroupOf L := by
  ext x
  rw [MulAut.mem_fixedSubgroup]
  change d.action x = x ↔ (x : G) ∈ centralizer ({z} : Set G)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have he := d.conjugation x
    rw [hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hx
    apply Subtype.ext
    rw [d.conjugation, ← hx, mul_inv_cancel_right]

/-- The fixed-subgroup two-residual has genuine centralizing lifts. -/
theorem fixedResidual_le_centralizerImage (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    (pResidual 2 (modelAut d d.action).fixedSubgroup).map
      (modelAut d d.action).fixedSubgroup.subtype ≤ centralizerImage d := by
  let := h.finite
  have hc : (quotientMap d).ker ≤ center L := by
    rw [quotientMap_ker]
    exact twoCore_le_center h d
  have hp : IsPGroup 2 (quotientMap d).ker := by
    rw [quotientMap_ker]
    exact pCore_isPGroup
  rw [← MulAut.map_embedded_fixedResidual_of_central_pgroup_ker 2
    d.action (modelAut d d.action) (quotientMap d) (quotientMap_surjective d)
    hc hp (fun x => (modelAut_apply d d.action x).symm)]
  apply map_mono
  exact (map_subtype_le _).trans (fixedSubgroup_eq_centralizer d).le


/-- Every quotient fixed point has a lift fixed by the original actor: the
fixed residual lifts through the central two-kernel, and the original Sylow
subgroup supplies the remaining two-group quotient. -/
theorem centralizerImage_eq_fixedSubgroup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) :
    centralizerImage d = (modelAut d d.action).fixedSubgroup := by
  let := h.finite
  let C := (modelAut d d.action).fixedSubgroup
  have hRC : (modelSylow h d : Subgroup Model) ≤ C := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (modelSylow_fixed h d x hx)
  let T : Sylow 2 C := (modelSylow h d).subtype hRC
  have ht := congrArg (Subgroup.map C.subtype) (pResidual_sup_sylow_eq_top T)
  have hT : (T : Subgroup C).map C.subtype = modelSylow h d :=
    map_subgroupOf_eq_of_le hRC
  rw [Subgroup.map_sup, hT, ← MonoidHom.range_eq_map, range_subtype] at ht
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [modelAut_apply]
    exact congrArg (quotientMap d)
      ((MulAut.mem_fixedSubgroup _ _).mp ((fixedSubgroup_eq_centralizer d).symm ▸ hy))
  · change C ≤ centralizerImage d
    rw [← ht]
    refine sup_le (fixedResidual_le_centralizerImage h d) ?_
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [← fixedSubgroup_eq_centralizer d]
    exact (MulAut.mem_fixedSubgroup _ _).mpr (componentSylow_fixed h d y hy)

/-- The intrinsic two-core quotient has trivial two-core on the actual model. -/
theorem model_twoCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : pCore 2 Model = ⊥ := by
  let := h.finite
  let e : (L ⧸ pCore 2 L) ≃* Model := d.quotientIso
  have he := pCore_map_iso 2 e
  rw [pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at he
  exact he.symm

/-- The model center embeds in the two-group center of its actual max6
centralizer. Thus the trivial two-core forces the model center to be trivial. -/
theorem model_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : center Model = ⊥ := by
  have hle : center Model ≤ SylowOvergroups.max6 := by
    rw [LowCentralizers.max6_eq_centralizer]
    exact center_le_centralizer _
  let f : center Model →* center SylowOvergroups.max6 := {
    toFun x := ⟨⟨x, hle x.property⟩, mem_center_iff.mpr (fun y =>
      Subtype.ext (mem_center_iff.mp x.property y))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun t : center SylowOvergroups.max6 => t.val.val) he)
  have hp : IsPGroup 2 (center Model) := LowCentralizers.max6_center_isPGroup.of_injective f hf
  exact le_bot_iff.mp ((show center Model ≤ pCore 2 Model from
    le_sSup ⟨inferInstance, hp⟩).trans (model_twoCore h d).le)

/-- The center of the source component is exactly its retained two-kernel. -/
theorem center_eq_twoCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : center L = pCore 2 L := by
  apply le_antisymm ?_ (twoCore_le_center h d)
  intro x hx
  rw [← quotientMap_ker d]
  apply MonoidHom.mem_ker.mpr
  have hc : quotientMap d x ∈ center Model := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := quotientMap_surjective d y
    simpa only [map_mul] using congrArg (quotientMap d) (mem_center_iff.mp hx y)
  simpa only [model_center h d, mem_bot] using hc

/-- Simplicity is inherited from the component's genuine central quotient. -/
theorem model_simple (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .ru) : IsSimpleGroup Model := by
  let : IsQuasisimple L := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let e : (L ⧸ center L) ≃* Model :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_twoCore h d)).trans d.quotientIso
  exact (MulEquiv.isSimpleGroup_congr e).mp inferInstance

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry

end
