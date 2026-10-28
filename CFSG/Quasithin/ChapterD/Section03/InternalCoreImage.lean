module

public import CFSG.Quasithin.ChapterD.Section03.InternalImage
public import Theory.GroupTheory.PCoreResidualFrattiniImage
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The two-core in the internal faithful image

Restrict the original map to X T. The source residual hypothesis identifies
its two-residual with the literal copy of X. Transport the actor kernel
bound through this inclusion and apply the residual Frattini lifting
lemma. Thus the two-core of the image of X T is exactly the image of its
two-core, which preserves the original seed's invariance.

Source: Aschbacher–Smith, Lemma D.3.3, combined manuscript of
1 March 2004, printed p.193.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- The literal copy of the core–Frattini subgroup inside an overgroup. -/
theorem coreFrattiniIn_subgroupOf (X A : Subgroup G) (hXA : X ≤ A) :
    (coreFrattiniIn X).comap (subgroupOfEquivOfLe hXA).toMonoidHom =
      coreFrattiniIn (X.subgroupOf A) := by
  let e := subgroupOfEquivOfLe hXA
  exact e.toMonoidHom.comap_frattini_pCore_of_pKernel e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)

/-- The actor kernel bound suffices for exact two-core transfer on X T. -/
theorem map_join_twoCore_of_internal_kernel
    (f : G →* H) (X T : Subgroup G) (hTX : T ≤ normalizer (X : Set G))
    (hX : pResidual 2 X = ⊤) (hT : IsPGroup 2 T)
    (hk : X ⊓ f.ker ≤ (coreFrattiniIn X).map X.subtype) :
    ((X ⊔ T).pCoreIn 2).map f = (X.map f ⊔ T.map f).pCoreIn 2 := by
  let A := X ⊔ T
  let R := X.subgroupOf A
  have hXA : X ≤ A := le_sup_left
  have hTA : T ≤ A := le_sup_right
  let e := subgroupOfEquivOfLe hXA
  let : R.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer hTX)
  have hpR : IsPPerfect 2 R := ((pResidual_eq_top_iff 2 X).mp hX).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hsup : R ⊔ T.subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXA,
      map_subgroupOf_eq_of_le hTA, ← MonoidHom.range_eq_map, range_subtype]
  have hR : pResidual 2 A = R :=
    pResidual_eq_of_isPPerfect_sup R (T.subgroupOf A) hpR hT.comap_subtype hsup
  let g := f.subgroupMap A
  have hkR : R ⊓ g.ker ≤ (coreFrattiniIn R).map R.subtype := by
    rintro a ⟨haX, haK⟩
    have hfa : (a : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp haK)
    obtain ⟨x, hx, he⟩ := hk ⟨haX, hfa⟩
    let r : R := ⟨a, haX⟩
    have her : e r = x := Subtype.ext he.symm
    refine ⟨r, ?_, rfl⟩
    rw [← coreFrattiniIn_subgroupOf X A hXA]
    change e r ∈ coreFrattiniIn X
    rwa [her]
  have hmap : (pCore 2 A).map g = pCore 2 (A.map f) := by
    apply g.map_pCore_of_residual_frattini_kernel (f.subgroupMap_surjective A)
    change pResidual 2 A ⊓ g.ker ≤
      (coreFrattiniIn (pResidual 2 A)).map (pResidual 2 A).subtype
    rw [hR]
    exact hkR
  calc
    _ = ((pCore 2 A).map g).map (A.map f).subtype := by
      rw [pCoreIn, map_map, map_map]
      rfl
    _ = (A.map f).pCoreIn 2 := by rw [hmap]; rfl
    _ = _ := by rw [show A.map f = X.map f ⊔ T.map f from Subgroup.map_sup X T f]

end CFSG.Quasithin.ChapterD.Section03
