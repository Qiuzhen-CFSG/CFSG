module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.SourceCompletion
public import Theory.GroupTheory.PCoreImage

/-!
Construct the paired Sylow quotient coordinates from the literal action and
quotient homomorphisms. Equal kernels supply compatible first-isomorphism
coordinates, while the two-group action kernel identifies the image of the
whole two-core with the concrete block core. These are the map identifications
used by the original end-node branch of [AS, 15.3.25].
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient
variable {G H : Type*} [Group G] [Group H]

/-- First-isomorphism coordinates retain the literal two surjections. -/
private theorem equiv_of_surjective_ker_eq {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : ∃ e : B ≃* C, ∀ a, e (f a) = g a := by
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective g hg
  let e := e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hk).trans e₂)
  refine ⟨e,?_⟩
  intro a
  have h : e₁ (QuotientGroup.mk' f.ker a) = f a := rfl
  rw [←h]
  change e₂ ((QuotientGroup.quotientMulEquivOfEq hk) (e₁.symm (e₁ (QuotientGroup.mk' f.ker a)))) = _
  rw [e₁.symm_apply_apply]
  rfl

/-- Matching kernels construct the concrete quotient coordinates, rather than
assuming an abstract isomorphism unrelated to the action. -/
theorem exists_sylowCoordinates (S : Subgroup G) (f : G →* Perm) (q : G →* H)
    (hS : S.map f = canonicalSylow) (hcore : q.ker.map f = blockCore)
    (hker : f.ker ≤ q.ker) : Nonempty (SylowCoordinates S f q) := by
  let r : S →* SylowGroup := (f.comp S.subtype).codRestrict canonicalSylow
    (fun s => hS.le (mem_map_of_mem f s.property))
  have hr : Function.Surjective r := by
    intro x
    have hx : (x : Perm) ∈ S.map f := hS.symm ▸ x.property
    obtain ⟨s,hs,he⟩ := hx
    exact ⟨⟨s,hs⟩,Subtype.ext he⟩
  let a := quotientMap.comp r
  let b := q.subgroupMap S
  have hk : b.ker = a.ker := by
    have hpre : blockCore.comap f = q.ker := by
      rw [←hcore,comap_map_eq,sup_eq_left.mpr hker]
    ext s
    change s ∈ (q.subgroupMap S).ker ↔ s ∈ (quotientMap.comp r).ker
    rw [ker_subgroupMap,←MonoidHom.comap_ker]
    change (s : G) ∈ q.ker ↔ r s ∈ (QuotientGroup.mk' sylowCore).ker
    rw [QuotientGroup.ker_mk']
    change (s : G) ∈ q.ker ↔ f (s : G) ∈ blockCore
    exact Iff.symm (show f (s : G) ∈ blockCore ↔ (s : G) ∈ q.ker from SetLike.ext_iff.mp hpre (s : G))
  obtain ⟨e,he⟩ := equiv_of_surjective_ker_eq b a (q.subgroupMap_surjective S)
    ((QuotientGroup.mk'_surjective _).comp hr) hk
  exact ⟨⟨hS.le,e,he⟩⟩

/-- Two-group kernels send the entire intrinsic core to the model block core. -/
theorem map_core_eq_blockCore [Finite G] (f : G →* Perm)
    (hf : f.range = parabolic) (hk : IsPGroup 2 f.ker) :
    (pCore 2 G).map f = blockCore := by
  let r : G →* parabolic := f.codRestrict parabolic (fun x => hf.le ⟨x,rfl⟩)
  have hr : Function.Surjective r := by
    intro x
    have hx : (x : Perm) ∈ f.range := hf.symm ▸ x.property
    obtain ⟨y,hy⟩ := hx
    exact ⟨y,Subtype.ext hy⟩
  have hkr : IsPGroup 2 r.ker := by
    have he : r.ker = f.ker := MonoidHom.ker_codRestrict _ _ _
    exact he.symm ▸ hk
  have hc := r.comap_pCore_of_ker_isPGroup hr hkr
  have hmap : (pCore 2 G).map r = pCore 2 parabolic := by
    rw [←hc,map_comap_eq_self_of_surjective hr]
  calc
    _ = ((pCore 2 G).map r).map parabolic.subtype := by rw [map_map]; rfl
    _ = (pCore 2 parabolic).map parabolic.subtype := by rw [hmap]
    _ = blockCore := parabolic_pCoreIn

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient