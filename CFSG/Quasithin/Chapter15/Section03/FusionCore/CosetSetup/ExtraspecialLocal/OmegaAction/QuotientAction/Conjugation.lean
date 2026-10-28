module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.Center
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction.WreathCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Faithful conjugation on the actual extraspecial quotient

Conjugation by T acts on Y/O₂(Y). The earlier identity O₂(YT) = C_T(V)
shows that the kernel of the natural orthogonal action acts trivially on
this quotient. Conversely, a trivial quotient action centralizes the
orthogonal image of Y, namely O² of the full orthogonal actor; its
centralizer has no nonidentity two-elements. Conjugation therefore descends
to an injective action of the actual image of T.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
printed p.1122, and the calculation after 15.3.49(b), printed p.1143.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G]

/-- The specified natural actor, restricted to T and its actual image. -/
def sylowProjection {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) : T →* d.image (T : Subgroup G) :=
  (d.actor.comp (inclusion hTM)).codRestrict _ (fun t => ⟨⟨t, hTM t.property⟩, t.property, rfl⟩)

/-- Every member of the Sylow image has a representative in the specified T. -/
theorem sylowProjection_surjective {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) :
    Function.Surjective (sylowProjection d T hTM) := by
  rintro ⟨a, m, hm, rfl⟩
  exact ⟨⟨m, hm⟩, rfl⟩

/-- Conjugation on the intrinsic two-core quotient, using relative normalization. -/
def sylowQuotientConjugation (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    T →* MulAut (Y ⧸ pCore 2 Y) :=
  (quotientAut (pCore 2 Y)).comp (Y.normalizerMonoidHom.comp (inclusion hn))

/-- On quotient representatives, the action is conjugation in the ambient group. -/
theorem sylowQuotientConjugation_apply (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) (t : T) (y : Y) :
    sylowQuotientConjugation T Y hn t (QuotientGroup.mk' (pCore 2 Y) y) =
      QuotientGroup.mk' (pCore 2 Y) (Y.normalizerMonoidHom ⟨t, hn t.property⟩ y) := by
  exact quotientAut_apply_mk _ _ _

/-- Fixing a quotient element means its commutator lies in the intrinsic core. -/
theorem quotient_conjugation_fixes_iff (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) (t : T) (y : Y) :
    sylowQuotientConjugation T Y hn t (QuotientGroup.mk' (pCore 2 Y) y) =
      QuotientGroup.mk' (pCore 2 Y) y ↔ ⁅(t : G), (y : G)⁆ ∈ Y.pCoreIn 2 := by
  rw [sylowQuotientConjugation_apply]
  let c := Y.normalizerMonoidHom ⟨t, hn t.property⟩ y * y⁻¹
  have hc : (c : G) = ⁅(t : G), (y : G)⁆ := rfl
  have hmem : c ∈ pCore 2 Y ↔ (c : G) ∈ Y.pCoreIn 2 := by
    constructor
    · intro h; exact ⟨c, h, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact (Subtype.ext he : z = c) ▸ hz
  rw [← hc, ← hmem, ← QuotientGroup.eq_one_iff c]
  change _ = _ ↔ QuotientGroup.mk' (pCore 2 Y) (_ * y⁻¹) = 1
  rw [map_mul, map_inv, mul_inv_eq_one]

/-- The earlier O₂(YT) identity makes the orthogonal kernel act trivially on Y/O₂(Y). -/
theorem sylowProjection_kernel_le {M V Y : Subgroup G} (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hMY : M ≤ normalizer (Y : Set G)) (hYM : Y ≤ M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    (sylowProjection d T hTM).ker ≤ (sylowQuotientConjugation T Y (hTM.trans hMY)).ker := by
  intro t ht
  have htc : (t : G) ∈ centralizer (V : Set G) := by
    have ha : (⟨t, hTM t.property⟩ : M) ∈ d.actor.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    rwa [d.ker_actor] at ha
  have htcore : (t : G) ∈ (Y ⊔ (T : Subgroup G)).pCoreIn 2 := hcore.ge ⟨t.property, htc⟩
  have hcomm := (commutator_core_le (Y ⊔ (T : Subgroup G))
    ((Y ⊔ (T : Subgroup G)).pCoreIn 2) Y le_sup_left
    ((Y ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    ((pCoreIn_le 2 _).trans ((sup_le hYM hTM).trans hMY))
    (isPGroup_pCoreIn 2 _)).2
  apply MulEquiv.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
  exact (quotient_conjugation_fixes_iff T Y (hTM.trans hMY) t y).mpr
    (hcomm (commutator_mem_commutator htcore y.property))

private theorem twoCore_le_twoCenter (Y : Subgroup G) : Y.pCoreIn 2 ≤ twoCenter Y := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  change QuotientGroup.mk' (pCore 2 Y) y ∈ center (Y ⧸ pCore 2 Y)
  have hq : QuotientGroup.mk' (pCore 2 Y) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [hq]
  exact one_mem _

/-- A trivial quotient action centralizes the orthogonal residual and has trivial image. -/
theorem sylowQuotientConjugation_kernel_le [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hMY : M ≤ normalizer (Y : Set G))
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    (sylowQuotientConjugation T Y (hTM.trans hMY)).ker ≤ (sylowProjection d T hTM).ker := by
  intro t ht
  apply orthogonal_two_centralizer _ (T.isPGroup'.comap_subtype.map d.actor) (sylowProjection d T hTM t)
  intro a ha
  obtain ⟨y, hy, rfl⟩ := himage.ge ha
  have hcomm : ⁅(t : G), (y : G)⁆ ∈ Y.pCoreIn 2 :=
    (quotient_conjugation_fixes_iff T Y (hTM.trans hMY) t ⟨y, hy⟩).mp
      (DFunLike.congr_fun (MonoidHom.mem_ker.mp ht) _)
  have hcentral := (hc.ge (twoCore_le_twoCenter Y hcomm)).2
  have hk : ⁅(⟨t, hTM t.property⟩ : M), y⁆ ∈ d.actor.ker := by
    rw [d.ker_actor]
    exact hcentral
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    ((map_commutatorElement d.actor _ _).symm.trans (MonoidHom.mem_ker.mp hk))).symm

/-- The quotient conjugation action descended to the actual orthogonal image of T. -/
noncomputable def extraspecialQuotientAction {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hYM : Y ≤ M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    d.image (T : Subgroup G) →* MulAut (Y ⧸ pCore 2 Y) :=
  (sylowProjection d T hTM).liftOfSurjective (sylowProjection_surjective d T hTM)
    ⟨sylowQuotientConjugation T Y (hTM.trans hMY), sylowProjection_kernel_le d T hTM hMY hYM hcore⟩

/-- Descent retains conjugation by every representative in T. -/
theorem extraspecialQuotientAction_projection {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hYM : Y ≤ M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)) (t : T) :
    extraspecialQuotientAction d T hTM hMY hYM hcore (sylowProjection d T hTM t) =
      sylowQuotientConjugation T Y (hTM.trans hMY) t :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The descended action is faithful; both kernel inclusions have been proved. -/
theorem extraspecialQuotientAction_injective [Finite G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hYM : Y ≤ M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hc : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Function.Injective (extraspecialQuotientAction d T hTM hMY hYM hcore) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  obtain ⟨t, rfl⟩ := sylowProjection_surjective d T hTM a
  have ht : t ∈ (sylowQuotientConjugation T Y (hTM.trans hMY)).ker := by
    rw [MonoidHom.mem_ker, ← extraspecialQuotientAction_projection d T hTM hMY hYM hcore]
    exact ha
  exact sylowQuotientConjugation_kernel_le d T hTM hMY hc himage ht
end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
