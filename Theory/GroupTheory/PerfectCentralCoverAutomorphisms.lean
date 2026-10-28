module

public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Faithful descent of automorphisms of a perfect central cover

Automorphisms descend through a covering whose kernel is the whole center.
Uniqueness of maps from a perfect group into a central extension makes this
map on automorphism groups injective. A pointwise fixer therefore embeds in
the pointwise fixer of its projected subgroup. In particular, this bounds the
actual conjugation image of an ambient subgroup centralizer.

This is the descent step for the automorphism-centralizer calculation in
Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript). It leaves
the calculation in the projective model explicit. No assertion that the
centralizer has total order two is used.
-/

public section

namespace PerfectCentralCovering
variable {E B : Type*} [Group E] [Group B]

/-- The automorphism induced on the specified quotient by the actual cover map. -/
noncomputable def Cover.autMap (f : Cover E B)
    (hk : f.toMonoidHom.ker = Subgroup.center E) : MulAut E →* MulAut B where
  toFun a := Classical.choose (f.exists_descended_aut hk a)
  map_one' := by
    ext b
    obtain ⟨x, rfl⟩ := f.surjective b
    exact Classical.choose_spec (f.exists_descended_aut hk 1) x
  map_mul' a b := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    change Classical.choose (f.exists_descended_aut hk (a * b)) (f.toMonoidHom x) =
      Classical.choose (f.exists_descended_aut hk a)
        (Classical.choose (f.exists_descended_aut hk b) (f.toMonoidHom x))
    rw [Classical.choose_spec (f.exists_descended_aut hk (a * b)),
      Classical.choose_spec (f.exists_descended_aut hk b),
      Classical.choose_spec (f.exists_descended_aut hk a)]
    rfl

/-- Descent commutes with the covering projection. -/
theorem Cover.autMap_apply (f : Cover E B)
    (hk : f.toMonoidHom.ker = Subgroup.center E) (a : MulAut E) (x : E) :
    f.autMap hk a (f.toMonoidHom x) = f.toMonoidHom (a x) :=
  Classical.choose_spec (f.exists_descended_aut hk a) x

/-- Perfectness rules out nonidentity automorphisms acting trivially on the quotient. -/
theorem Cover.autMap_injective (f : Cover E B)
    (hk : f.toMonoidHom.ker = Subgroup.center E) : Function.Injective (f.autMap hk) := by
  let := f.isPerfect
  intro a b hab
  apply MulEquiv.toMonoidHom_injective
  apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
  ext x
  change f.toMonoidHom (a x) = f.toMonoidHom (b x)
  rw [← f.autMap_apply hk a, ← f.autMap_apply hk b, hab]

/-- The cover pointwise fixer has order dividing that of the quotient pointwise fixer. -/
theorem Cover.card_fixing_dvd (f : Cover E B)
    (hk : f.toMonoidHom.ker = Subgroup.center E) (P : Subgroup E) :
    Nat.card (fixingSubgroup (MulAut E) (P : Set E)) ∣
      Nat.card (fixingSubgroup (MulAut B) (P.map f.toMonoidHom : Set B)) := by
  let A := fixingSubgroup (MulAut E) (P : Set E)
  let D := fixingSubgroup (MulAut B) (P.map f.toMonoidHom : Set B)
  have hle : A.map (f.autMap hk) ≤ D := by
    rintro _ ⟨a, ha, rfl⟩
    intro b
    obtain ⟨x, hx, hb⟩ := b.property
    change f.autMap hk a (b : B) = (b : B)
    rw [← hb]
    rw [f.autMap_apply hk a x]
    exact congrArg f.toMonoidHom (ha ⟨x, hx⟩)
  have hd := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective (f.autMap_injective hk)] at hd

/-- The actual ambient conjugation image is bounded by the quotient pointwise fixer. -/
theorem Cover.card_centralizerImage_dvd_quotientFixer
    {G : Type*} [Group G] (L F : Subgroup G) (f : Cover L B)
    (hk : f.toMonoidHom.ker = Subgroup.center L) :
    Nat.card (((Subgroup.centralizer (F : Set G)).subgroupOf
      (Subgroup.normalizer (L : Set G))).map L.normalizerMonoidHom) ∣
      Nat.card (fixingSubgroup (MulAut B)
        ((F.subgroupOf L).map f.toMonoidHom : Set B)) := by
  let A := ((Subgroup.centralizer (F : Set G)).subgroupOf
    (Subgroup.normalizer (L : Set G))).map L.normalizerMonoidHom
  have hle : A ≤ fixingSubgroup (MulAut L) (F.subgroupOf L : Set L) := by
    rintro _ ⟨n, hn, rfl⟩ x
    apply Subtype.ext
    change (n : G) * ((x : L) : G) * (n : G)⁻¹ = ((x : L) : G)
    have hn' : ((x : L) : G) * (n : G) = (n : G) * ((x : L) : G) :=
      hn ((x : L) : G) x.property
    rw [← hn', mul_inv_cancel_right]
  exact (Subgroup.card_dvd_of_le hle).trans (f.card_fixing_dvd hk (F.subgroupOf L))
end PerfectCentralCovering
