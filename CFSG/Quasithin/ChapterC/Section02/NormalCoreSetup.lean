module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# Pushing-up setup from a normal perfect subgroup

Inside the literal local group H, apply A.4.2(7) to a normal two-perfect
subgroup of M and the given Sylow subgroup. Characteristic-normalizer
control supplies the normalizer hypothesis. The resulting core is radical
in H and Sylow in its normal closure under M, giving C.2.3. Both conclusions
are transported through the original inclusions, retaining the same core.

Source: Aschbacher--Smith, A.4.2(7) and C.2.3, printed pp.57 and144.
The fixed-coset application is source 3.3.22, printed p.597.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
open Chapter1 Chapter1.RadicalExclusions ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem embedded_normalClosure_subgroupOf {H M R : Subgroup G} (hMH : M ≤ H) :
    ((normalClosure ((R.subgroupOf H).subgroupOf (M.subgroupOf H) : Set (M.subgroupOf H))).map
      (M.subgroupOf H).subtype).map H.subtype =
        (normalClosure (R.subgroupOf M : Set M)).map M.subtype := by
  let e := subgroupOfEquivOfLe hMH
  have he : ((R.subgroupOf H).subgroupOf (M.subgroupOf H)).map e.toMonoidHom =
      R.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hn := map_normalClosure
    ((R.subgroupOf H).subgroupOf (M.subgroupOf H) : Set (M.subgroupOf H))
    e.toMonoidHom e.surjective
  rw [← coe_map, he] at hn
  rw [← hn, map_map, map_map]
  rfl

/-- A.4.2(7) constructs C.2.3 on a literal local group from a normal
perfect subgroup, the actual common core and characteristic-normalizer control. -/
theorem pushingUpSetup_of_normal_core
    {κ : GroupClass.{u}} {H M X R : Subgroup G} (S : Sylow 2 H)
    (hH : IsSQTK κ H) (hXM : X ≤ M) (hMH : M ≤ H)
    (hMX : M ≤ normalizer (X : Set G)) (hp : IsPPerfect 2 X)
    (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hR : R = (X ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2)
    (hne : R ≠ ⊥)
    (hcontrol : (R.subgroupOf H).characteristicNormalizerClosure ≤ M.subgroupOf H) :
    PushingUpSetup κ H R M := by
  let X₀ := X.subgroupOf H
  let M₀ := M.subgroupOf H
  let R₀ := R.subgroupOf H
  have hXH := hXM.trans hMH
  have hRH : R ≤ H := hR ▸ (pCoreIn_le 2 _).trans
    (sup_le hXH (map_subtype_le _))
  have hSM₀ : (S : Subgroup H) ≤ M₀ := fun x hx => hSM (mem_map_of_mem _ hx)
  let S₀ : Sylow 2 M₀ := S.subtype hSM₀
  have hS₀ : (S₀ : Subgroup M₀).map M₀.subtype = (S : Subgroup H) := by
    simp only [S₀, Sylow.coe_subtype, map_subgroupOf_eq_of_le hSM₀]
  have hR₀ : (X₀ ⊔ (S₀ : Subgroup M₀).map M₀.subtype).pCoreIn 2 = R₀ := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      Subgroup.map_sup, hS₀, map_subgroupOf_eq_of_le hXH,
      map_subgroupOf_eq_of_le hRH, hR]
  have hne₀ : R₀ ≠ ⊥ := by
    intro he
    apply hne
    simpa only [R₀, map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using congrArg (map H.subtype) he
  have hMX₀ : M₀ ≤ normalizer (X₀ : Set H) := by
    rw [← subgroupOf_normalizer_eq hXH]
    exact comap_mono hMX
  have hNM₀ : normalizer
      ((X₀ ⊔ (S₀ : Subgroup M₀).map M₀.subtype).pCoreIn 2 : Set H) ≤ M₀ := by
    rw [hR₀]
    exact (normalizer_le_characteristicNormalizerClosure_self R₀ hne₀).trans hcontrol
  have hpc : IsPPerfect 2 X₀ := hp.of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hh := normal_sylow_core_conclusions X₀ M₀ (comap_mono hXM) hMX₀ hpc S₀ hNM₀
  dsimp only at hh
  rw [hR₀] at hh
  refine ⟨hH, hRH, hMH, ⟨hne₀, hh.2.2.2.2.2.1.symm⟩, hcontrol, ?_⟩
  have hs : IsSylowIn 2 R₀
      ((normalClosure (R₀.subgroupOf M₀ : Set M₀)).map M₀.subtype) := hh.2.2.2.2.2.2
  have hm := (IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  rw [map_subgroupOf_eq_of_le hRH, embedded_normalClosure_subgroupOf hMH] at hm
  exact hm
end CFSG.Quasithin.ChapterC
