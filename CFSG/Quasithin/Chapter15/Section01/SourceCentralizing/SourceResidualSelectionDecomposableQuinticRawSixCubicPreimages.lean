module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicSplit
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Canonical cubic preimages of the same two parabolics

Take the three-residual inside the full preimage of an S₄ subgroup.
It maps isomorphically onto that subgroup, retains every two-subgroup of
the preimage, and is preserved by every automorphism preserving the preimage.
Two such subgroups generate a perfect central cover when their images do.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
variable {X Y : Type*} [Group X] [Group Y] [Finite X]

/-- The original central covering map restricts to an isomorphism on the
canonical three-residual of each full S₄ preimage. -/
theorem preimage_residual (f : X →* Y) (hf : Function.Surjective f)
    (hc : f.ker ≤ center X) (hp : IsPGroup 3 f.ker)
    (J : Subgroup Y) (e : J ≃* Equiv.Perm (Fin 4)) :
    let B := J.comap f
    let R := (pResidual 3 B).map B.subtype
    R.map f = J ∧ Nonempty (R ≃* J) ∧
      (∀ P : Subgroup X, IsPGroup 2 P → P ≤ B → P ≤ R) ∧
      normalizer (B : Set X) ≤ normalizer (R : Set X) := by
  let B := J.comap f
  let D := pResidual 3 B
  let R := D.map B.subtype
  let g : B →* J := f.subgroupComap J
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hxy⟩ := hf y
    exact ⟨⟨x,show f x ∈ J from hxy ▸ y.property⟩,Subtype.ext hxy⟩
  let k := e.toMonoidHom.comp g
  have hkc : k.ker ≤ center B := by
    intro x hx
    change e (g x) = 1 at hx
    have hxg : f x = 1 := congrArg Subtype.val
      (e.injective (hx.trans (map_one e).symm))
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxg) y)
  have hkp : IsPGroup 3 k.ker := by
    have hk : k.ker = f.ker.comap B.subtype := by
      ext x
      change e (g x) = 1 ↔ f (x : X) = 1
      rw [←map_one e,e.injective.eq_iff]
      exact Subtype.ext_iff
    rw [hk]
    exact hp.comap_of_injective B.subtype B.subtype_injective
  have hb := residual_bijective k (e.surjective.comp hg) hkc hkp
  have hgD : Function.Bijective (g.comp D.subtype) := by
    refine ⟨fun x y hxy => hb.1 (congrArg e hxy),?_⟩
    intro y
    obtain ⟨x,hxy⟩ := hb.2 (e y)
    exact ⟨x,e.injective hxy⟩
  let a : R ≃* J := (D.equivMapOfInjective B.subtype B.subtype_injective).symm.trans
    (MulEquiv.ofBijective (g.comp D.subtype) hgD)
  have hmap : R.map f = J := by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact map_subtype_le D hx
    · intro y hy
      obtain ⟨x,hxy⟩ := hgD.2 ⟨y,hy⟩
      exact ⟨x,mem_map_of_mem B.subtype x.property,congrArg Subtype.val hxy⟩
  refine ⟨hmap,⟨a⟩,?_,normalizer_le_normalizer_characteristic_image B D⟩
  intro P hP hPB x hx
  have hxD : (⟨x,hPB hx⟩ : B) ∈ D := by
    apply mem_pResidual_of_orderOf_coprime
    have hh := hP.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hx⟩ : P)
    simpa only [←orderOf_coe] using hh.symm
  exact ⟨⟨x,hPB hx⟩,hxD,rfl⟩

/-- In the same perfect central cover, generating images force the two
canonical residual preimages to generate the full original group. -/
theorem preimage_residuals_generate [Group.IsPerfect X]
    (f : X →* Y) (hf : Function.Surjective f)
    (hc : f.ker ≤ center X) (hp : IsPGroup 3 f.ker)
    (J K : Subgroup Y) (eJ : J ≃* Equiv.Perm (Fin 4))
    (eK : K ≃* Equiv.Perm (Fin 4)) (hgen : J ⊔ K = ⊤) :
    (pResidual 3 (J.comap f)).map (J.comap f).subtype ⊔
      (pResidual 3 (K.comap f)).map (K.comap f).subtype = ⊤ := by
  let A := (pResidual 3 (J.comap f)).map (J.comap f).subtype
  let B := (pResidual 3 (K.comap f)).map (K.comap f).subtype
  have ha : A.map f = J := (preimage_residual f hf hc hp J eJ).1
  have hb : B.map f = K := (preimage_residual f hf hc hp K eK).1
  have hm : (A ⊔ B).map f = ⊤ := by rw [Subgroup.map_sup,ha,hb,hgen]
  have hh := congrArg (Subgroup.comap f) hm
  rw [comap_map_eq,comap_top] at hh
  exact eq_top_of_sup_center_eq_top _
    (top_unique (hh.symm.le.trans (sup_le_sup_left hc (A ⊔ B))))

end CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
