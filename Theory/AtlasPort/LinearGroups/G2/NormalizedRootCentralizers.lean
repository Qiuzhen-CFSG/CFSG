module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter

/-!
# Uniform highest-root centralizers in the G₂ Borel

The full center of the positive-root Sylow in characteristic two is the
highest-root subgroup `rootA`, as proved from the six root coordinates in
`LieSylowCenter`. The unipotent factor of the Borel centralizes this root
subgroup. Its torus factor acts on its parameter by the character `(l,m) ↦ l*m`.
Fixing a nonzero parameter forces that character to be one, and hence fixes
the entire subgroup. This proves the Borel centralizer equality for every
nonidentity element of the full Sylow center, in particular over fields of
order `2^n` with `n > 1`.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927. The root product,
commutator and torus formulas are from the licensed ATLAS octonion model;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.NormalizedRootCentralizers
open Subgroup LieParabolicSetup
variable {F : Type*} [Field F]

private theorem unipotent_commute_rootA {u : Model F}
    (hu : u ∈ unipotent) (a : F) : Commute u (rootA a) := by
  rw [unipotent_eq_range] at hu
  obtain ⟨t, rfl⟩ := hu
  exact unipotentProduct_commute_rootA t a

/-- A torus element fixes a nonzero highest-root parameter exactly when its
highest-root character is one. -/
theorem torus_commute_rootA_iff (l m : Fˣ) {a : F} (ha : a ≠ 0) :
    Commute (torus l m) (rootA a) ↔ (l : F) * (m : F) = 1 := by
  constructor
  · intro h
    have he := h.mul_inv_cancel
    rw [torus_rootA] at he
    exact mul_right_cancel₀ ha ((rootA_injective he).trans (one_mul a).symm)
  · intro h
    apply (mul_inv_eq_iff_eq_mul).mp
    rw [torus_rootA, h, one_mul]

/-- In the concrete Borel, centralizing one nonzero highest-root element
is equivalent to centralizing the entire highest-root subgroup. -/
theorem borel_centralizer_rootA {a : F} (ha : a ≠ 0) :
    borel ⊓ centralizer ({rootA a} : Set (Model F)) =
      borel ⊓ centralizer (highestRoot (F := F) : Set (Model F)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨u, t⟩, hgt⟩ := borelProductEquiv.surjective ⟨g, hg.1⟩
    have hge : (u : Model F) * t = g := congrArg Subtype.val hgt
    obtain ⟨⟨l, m⟩, hlm⟩ := t.property
    have hte : (t : Model F) = torus l m := hlm.symm
    rw [hte] at hge
    have hga : Commute ((u : Model F) * torus l m) (rootA a) := by
      rw [hge]
      exact mem_centralizer_singleton_iff.mp hg.2
    have hta : Commute (torus l m) (rootA a) := by
      simpa only [inv_mul_cancel_left] using
        (unipotent_commute_rootA u.property a).inv_left.mul_left hga
    have hchar := (torus_commute_rootA_iff l m ha).mp hta
    refine ⟨hg.1, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, rfl⟩
    change rootA b.toAdd * g = g * rootA b.toAdd
    have htb : Commute (torus l m) (rootA b.toAdd) := by
      apply (mul_inv_eq_iff_eq_mul).mp
      rw [torus_rootA, hchar, one_mul]
    rw [← hge]
    exact ((unipotent_commute_rootA u.property b.toAdd).mul_left htb).eq.symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      (show rootA a ∈ highestRoot from ⟨Multiplicative.ofAdd a, rfl⟩)))

/-- Uniform centralizers for every nonidentity element of the full Sylow
center in characteristic two. -/
theorem uniform [CharP F 2] (r : Model F)
    (hr : r ∈ (center (unipotent (K := F))).map unipotent.subtype) (hne : r ≠ 1) :
    borel ⊓ centralizer ({r} : Set (Model F)) =
      borel ⊓ centralizer
        (((center (unipotent (K := F))).map unipotent.subtype :
          Subgroup (Model F)) : Set (Model F)) := by
  rw [unipotent_center] at hr ⊢
  obtain ⟨a, rfl⟩ := hr
  apply borel_centralizer_rootA
  intro ha
  apply hne
  change rootA a.toAdd = 1
  rw [ha, rootA_zero]

end Atlas.G2.NormalizedRootCentralizers
