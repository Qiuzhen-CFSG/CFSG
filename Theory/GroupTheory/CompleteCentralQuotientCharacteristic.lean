module
public import Theory.GroupTheory.LowerCentralCenterLift
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Theory.GroupTheory.AutomorphismTowerSimple
/-!
# Characteristic subgroups from a complete central quotient

An ambient normal perfect subgroup with a complete central quotient admits
an actual ambient projection to that quotient. Its covering center remains
central in the ambient group. The image of a specified ambient Sylow equals
the image of its intersection with the perfect subgroup. Consequently the
lower-central lifting theorem applies to the full Sylow and retains the
entire covering center.

Source application: the Rudvalis exclusion in Aschbacher--Smith 15.1.22,
printed p.1100. No centerless-cover hypothesis or MS classification is used.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Group D]

/-- The projection onto a complete central quotient of a perfect normal subgroup. -/
theorem normal_complete_central_projection
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* D)
    (hZ : center D = ⊥)
    (hi : Function.Surjective (MulAut.conj : D →* MulAut D)) :
    ∃ f : G →* D, Function.Surjective f ∧
      (∀ l : L, f l = e (QuotientGroup.mk' (center L) l)) ∧
      (center L).map L.subtype ≤ center G := by
  let c : D ≃* MulAut D := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot hZ,hi⟩
  let a : G →* MulAut D := (MulAut.centralQuotientAction e).comp MulAut.conjNormal
  let f := c.symm.toMonoidHom.comp a
  have hfL (l : L) : f l = e (QuotientGroup.mk' (center L) l) := by
    apply c.injective
    change c (c.symm (a l)) = MulAut.conj (e (QuotientGroup.mk' (center L) l))
    rw [c.apply_symm_apply]
    change (MulAut.centralQuotientAction e) ((MulAut.conjNormal : G →* MulAut L) l) = _
    rw [MulAut.conjNormal_val]
    exact MulAut.centralQuotientAction_conj e l
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z,hz⟩ := e.surjective y
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (center L) z
    exact ⟨l,(hfL l).trans hz⟩
  refine ⟨f,hf,hfL,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  apply mem_center_iff.mpr
  intro g
  obtain ⟨v,hv⟩ := hi (a g)
  obtain ⟨l,hl⟩ := (MulAut.centralQuotientAction_inner_iff e
    (MulAut.conjNormal g : MulAut L)).mp ⟨v,hv.symm⟩
  have he := congrArg (fun b : MulAut L => (b z : G)) hl
  change g * (z : G) * g⁻¹ = ((l * z * l⁻¹ : L) : G) at he
  have hfix : l * z * l⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hz l)
  rw [hfix] at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- In an overgroup of a perfect central cover of a complete group, the
center-saturated lower-central term of the full Sylow is normalized by every
subgroup whose marked image normalizes the corresponding model term. -/
theorem characteristic_of_normal_complete_quotient [Finite G] [Finite D]
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* D) (hZ : IsPGroup 2 (center L))
    (hzD : center D = ⊥)
    (hi : Function.Surjective (MulAut.conj : D →* MulAut D))
    (S : Sylow 2 G) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L)
    (n : ℕ) (B : Subgroup G) (hBL : B ≤ L)
    (hc : (center ((P : Subgroup L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L))))).map
        ((P : Subgroup L).map (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))).subtype ≤
      ((P : Subgroup L).map (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))).lowerCentralSeries n)
    (hn : (B.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) ≤
      normalizer (((P : Subgroup L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))).lowerCentralSeries n : Set D))
    (hne : ((P : Subgroup L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))).lowerCentralSeries n ≠ ⊥) :
    ∃ C : Subgroup (S : Subgroup G), C.Characteristic ∧ C ≠ ⊥ ∧
      B ≤ normalizer (C.map (S : Subgroup G).subtype : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  obtain ⟨f,hf,hfL,hZambient⟩ := normal_complete_central_projection L e hzD hi
  have hfq : f.comp L.subtype = q := MonoidHom.ext hfL
  have hmap : ((S : Subgroup G) ⊓ L).map f = Q := by
    rw [←hP,map_map,hfq]
    rfl
  have hS : (S : Subgroup G).map f = Q := by
    apply Q.is_maximal' (S.isPGroup'.map f)
    rw [←hmap]
    exact map_mono inf_le_left
  let Z := (center L).map L.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZS : Z ≤ (S : Subgroup G) := (hZ.map L.subtype).le_sylow_of_normal S
  have hZcenter : Z ≤ (center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    intro z hz
    refine ⟨⟨z,hZS hz⟩,mem_center_iff.mpr (fun t => ?_),rfl⟩
    exact Subtype.ext (mem_center_iff.mp (hZambient hz) t)
  have hkernel : L ⊓ f.ker ≤ (center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    rintro z ⟨hz,hzf⟩
    apply hZcenter
    refine ⟨⟨z,hz⟩,?_,rfl⟩
    apply (QuotientGroup.eq_one_iff (N := center L) (⟨z,hz⟩ : L)).mp
    apply e.injective
    change e (QuotientGroup.mk' (center L) (⟨z,hz⟩ : L)) = e 1
    rw [←hfL,e.map_one]
    exact hzf
  have hcenter : ((center (S : Subgroup G)).map (S : Subgroup G).subtype).map f ≤
      ((S : Subgroup G).map f).lowerCentralSeries n := by
    rw [hS]
    apply le_trans _ hc
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hfx : f x ∈ (Q : Subgroup D) := hS ▸ mem_map_of_mem f x.property
    refine ⟨⟨f x,hfx⟩,mem_center_iff.mpr (fun y => ?_),rfl⟩
    obtain ⟨z,hz,he⟩ := hS.symm ▸ (show (y : D) ∈ (Q : Subgroup D) from y.property)
    apply Subtype.ext
    change (y : D) * f x = f x * y
    rw [←he,←map_mul,←map_mul]
    exact congrArg f (congrArg Subtype.val (mem_center_iff.mp hx ⟨z,hz⟩))
  have hB : B.map f = (B.subgroupOf L).map q := by
    rw [←hfq,←map_map,map_subgroupOf_eq_of_le hBL]
  apply exists_characteristic_lowerCentral_center (S : Subgroup G) L B f n hBL
    (hmap.trans hS.symm) hkernel hcenter
  · rwa [hB,hS]
  · rwa [hS]

end Theory.GroupTheory
