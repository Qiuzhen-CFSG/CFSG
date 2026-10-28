module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ConjugatePairInternalLift

/-!
# Returning actors in maximal Sylow overgroups

Let B be a maximal subgroup containing a Sylow p-subgroup. In an action
whose kernel is O_p(G), an actor filling the nontrivial image of O_p(B)
can be conjugated back into O_p(B) only by an element of B. Equal finite
image orders give equality of radical images, and the retained kernel
lifts that equality. Maximality then identifies the radical normalizer.

The original plane-parabolic application is in Chapter13 Section04,
FixedCoreSource/Nonsolvable/MixedPlaneReturn. This is the group-theoretic
return step in Aschbacher--Smith 13.4.15, printed p.912.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G Y : Type*} [Group G] [Group Y] [Finite Y]
variable {p : ℕ}

/-- A subgroup filling the nontrivial radical image of a maximal Sylow
 overgroup can return into that radical only under its own overgroup. -/
theorem mem_of_radical_image_return (S : Sylow p G) (B : Subgroup G)
    (hSB : (S : Subgroup G) ≤ B) (hB : IsCoatom B)
    (f : G →* Y) (hk : f.ker = pCore p G)
    (A : Subgroup G) (hAR : A ≤ B.pCoreIn p)
    (n : ℕ) (hn : 1 < n) (hA : Nat.card (A.map f) = n)
    (hR : Nat.card ((B.pCoreIn p).map f) ≤ n)
    (g : G) (hg : A.conjBy g ≤ B.pCoreIn p) : g ∈ B := by
  let R := B.pCoreIn p
  have hBR : B ≤ normalizer (R : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore p B))
  have hkR : f.ker ≤ R := by
    rw [hk]
    exact le_pCoreIn_of_normalizes pCore_isPGroup
      ((pCore_isPGroup.le_sylow_of_normal S).trans hSB) le_normalizer_of_normal
  change Nat.card (R.map f) ≤ n at hR
  have he : A.map f = R.map f := eq_of_le_of_card_ge (map_mono hAR) (by omega)
  have hRc : Nat.card (R.map f) = n := he ▸ hA
  have heg : (A.conjBy g).map f = R.map f := by
    apply eq_of_le_of_card_ge (map_mono hg)
    rw [map_conjBy_hom]
    change Nat.card (R.map f) ≤ Nat.card ((A.map f).map (MulAut.conj (f g)).toMonoidHom)
    rw [card_map_of_injective (f := (MulAut.conj (f g)).toMonoidHom) (MulAut.conj (f g)).injective,hA,hRc]
  have hRg : (R.conjBy g).map f = R.map f := by
    calc
      (R.conjBy g).map f = (A.map f).conjBy (f g) := by rw [map_conjBy_hom,he]
      _ = R.map f := by rw [←map_conjBy_hom,heg]
  have hkernel : f.ker.conjBy g = f.ker :=
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (f.ker : Set G) from by
      rw [normalizer_eq_top]; exact mem_top g)
  have hkRg : f.ker ≤ R.conjBy g := hkernel ▸ map_mono hkR
  have hgR : R.conjBy g = R := by
    have hh := congrArg (comap f) hRg
    rwa [comap_map_eq_self hkRg,comap_map_eq_self hkR] at hh
  have hnR : normalizer (R : Set G) ≠ ⊤ := by
    intro htop
    let : R.Normal := normalizer_eq_top_iff.mp htop
    have hRp : R ≤ pCore p G := le_sSup ⟨inferInstance,isPGroup_pCoreIn p B⟩
    have hzero : R.map f = ⊥ := (Subgroup.map_eq_bot_iff R).mpr (by simpa [hk] using hRp)
    rw [hzero,card_bot] at hRc
    omega
  have heN : normalizer (R : Set G) = B := by
    by_contra hh
    exact hnR (hB.2 _ (lt_of_le_of_ne hBR (Ne.symm hh)))
  exact heN ▸ mem_normalizer_iff_map_conj_eq.mpr hgR
end Theory.GroupTheory
