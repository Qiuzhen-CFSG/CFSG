module

public import Theory.GroupTheory.SimpleSectionAction
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Core sections and their local normalizer extensions

For a subnormal J with simple core quotient, the section stabilizer in T is
exactly N_T(J): the core is characteristic. On quotient representatives the
section action is the existing pCoreJoinAction of J N_T(J). The image of J
is the inner subgroup, so the entire action image is exactly the section
extension. For a p-group T and centerless section, the established kernel
calculation identifies this extension with J N_T(J) modulo its p-core.

This is the literal local-normalizer comparison used in Aschbacher--Smith,
E.1.11, printed p.213. It does not assume a full automorphism group action.
-/

@[expose] public section
open Subgroup
namespace ChiefFactor.SimpleSection
variable {G : Type*} [Group G]

/-- The core quotient of a subnormal subgroup, with its actual carrier. -/
def coreSection (p : ℕ) (J : Subgroup G) (hJ : J.IsSubnormal)
    [IsSimpleGroup (J ⧸ pCore p J)] : SimpleSection G (J ⧸ pCore p J) where
  simple := inferInstance
  subgroup := J
  subnormal := hJ
  kernel := pCore p J
  normal := inferInstance
  equiv := MulEquiv.refl _

private theorem normalizer_le_coreImage_normalizer (p : ℕ) (J : Subgroup G) :
    normalizer J ≤ normalizer (((pCore p J).map J.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have he : (MulAut.conj g : G →* G).comp J.subtype =
      J.subtype.comp (J.normalizerMonoidHom ⟨g, hg⟩ : J →* J) := by ext; rfl
  rw [he, ← Subgroup.map_map]
  exact congrArg (Subgroup.map J.subtype)
    (characteristic_iff_map_eq.mp inferInstance (J.normalizerMonoidHom ⟨g, hg⟩))

/-- Characteristic core kernels impose no extra restriction on the actor. -/
theorem coreSection_stabilizer (p : ℕ) (J T : Subgroup G) (hJ : J.IsSubnormal)
    [IsSimpleGroup (J ⧸ pCore p J)] :
    (coreSection p J hJ).stabilizer T = T ⊓ normalizer J := by
  change T ⊓ (normalizer J ⊓ normalizer (((pCore p J).map J.subtype : Subgroup G) : Set G)) = _
  rw [inf_eq_left.mpr (normalizer_le_coreImage_normalizer p J)]

/-- The inner join is exactly the literal core-quotient action image of J N_T(J). -/
theorem coreSection_extension (p : ℕ) (J T : Subgroup G) (hJ : J.IsSubnormal)
    [IsSimpleGroup (J ⧸ pCore p J)] :
    (coreSection p J hJ).extension T =
      (pCoreJoinAction p (show T ⊓ normalizer J ≤ normalizer J from inf_le_right)).range := by
  let U := T ⊓ normalizer J
  let f := pCoreJoinAction p (show U ≤ normalizer J from inf_le_right)
  let s := coreSection p J hJ
  have hleft : (f.comp (inclusion (show J ≤ J ⊔ U from le_sup_left))).range =
      MulAut.innerSubgroup (J ⧸ pCore p J) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore p J) x,
        (pCoreJoinAction_on_component p inf_le_right x).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore p J) x
      exact ⟨y, pCoreJoinAction_on_component p inf_le_right y⟩
  let e : s.stabilizer T ≃* U := MulEquiv.subgroupCongr (coreSection_stabilizer p J T hJ)
  have he : f.comp (inclusion (show U ≤ J ⊔ U from le_sup_right)) =
      (s.action T).comp e.symm.toMonoidHom := by
    ext g x
    induction x using Quotient.inductionOn with | h x =>
      change pCoreJoinAction p inf_le_right (inclusion le_sup_right g)
        (QuotientGroup.mk' (pCore p J) x) = s.action T (e.symm g) (s.projection x)
      rw [pCoreJoinAction_mk]
      exact (s.action_projection T (e.symm g) x).symm
  have hright : (f.comp (inclusion (show U ≤ J ⊔ U from le_sup_right))).range =
      (s.action T).range := by
    rw [he, MonoidHom.range_comp, (e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective), ← MonoidHom.range_eq_map]
  have hgen : J.subgroupOf (J ⊔ U) ⊔ U.subgroupOf (J ⊔ U) = ⊤ := by
    apply map_injective (J ⊔ U).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  calc
    s.extension T = (f.comp (inclusion (show J ≤ J ⊔ U from le_sup_left))).range ⊔
        (f.comp (inclusion (show U ≤ J ⊔ U from le_sup_right))).range := by
      rw [hleft, hright]; rfl
    _ = f.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, inclusion_range,
        inclusion_range, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map]

/-- The extension really is J N_T(J) modulo its p-core when the core section
is centerless and the actor is a p-group. -/
noncomputable def coreSectionExtensionEquiv (p : ℕ) (J T : Subgroup G)
    (hJ : J.IsSubnormal) [IsSimpleGroup (J ⧸ pCore p J)]
    (hT : IsPGroup p T) (hc : center (J ⧸ pCore p J) = ⊥) :
    ((J ⊔ (T ⊓ normalizer J) : Subgroup G) ⧸
      pCore p (J ⊔ (T ⊓ normalizer J) : Subgroup G)) ≃*
      (coreSection p J hJ).extension T :=
  (pCoreJoinQuotientEquivRange p inf_le_right (hT.to_le inf_le_left) hc).trans
    (MulEquiv.subgroupCongr (coreSection_extension p J T hJ).symm)

end ChiefFactor.SimpleSection
