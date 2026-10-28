module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.Inputs
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.PrimeNormalExtension
public import Theory.SpecificGroups.PSL2.PGL2SylowNormalizedFive
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import GorensteinWalter.PSL2PerfectOfCard
public import FeitThompson.FinalTheorem
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.PrimeAutomizer.Geometry

/-!
# Proper Sylow overgroups of faithful prime-field automizers

Dickson's classification makes a nonsolvable proper intersection an actual
A₅ subgroup. In a proper faithful extension, the ambient group is PGL₂;
its full Sylow two-subgroup cannot normalize that A₅ when p ≥ 7.
Thus all proper Sylow intersections are solvable. Two distinct maximal
overgroups give the invariant cover, and uniqueness gives a genuine
minimal parabolic.

Source application: Aschbacher--Smith E.1.12 and 10.3.3, pp.214 and 756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
variable {G : Type*} [Group G]

/-- Dickson's only nonsolvable proper prime-field alternative, with its divisibility. -/
theorem nonsolvable_proper_prime_model
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (e : G ≃* PSL(2,F))
    (A : Subgroup G) (hne : A ≠ ⊤) (hns : ¬ Group.IsSolvable A) :
    5 ∣ p ^ 2 - 1 ∧ Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  let B := A.map e.toMonoidHom
  let d : A ≃* B := A.equivMapOfInjective e.toMonoidHom e.injective
  have hB : B ≠ ⊤ := by
    intro h
    exact hne ((Subgroup.map_injective e.injective) (h.trans
      (map_top_of_surjective e.toMonoidHom e.surjective).symm))
  have hsB : ¬ Group.IsSolvable B := by
    intro h
    let := h
    exact hns (Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective)
  obtain ⟨_, hd, ⟨a⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five ho hF B hB hsB
  exact ⟨hd, ⟨d.trans a⟩⟩

/-- A full Sylow in a faithful proper prime-field extension cannot normalize A₅. -/
theorem no_five_in_proper_extension [Finite G]
    (L : Subgroup G) [L.Normal] (hC : centralizer (L : Set G) = ⊥)
    (hL : L ≠ ⊤) (R : Sylow 2 G)
    (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 7 ≤ p) (hF : Nat.card F = p) (e : L ≃* PSL(2,F))
    (A : Subgroup G) (hA : Nonempty (A ≃* alternatingGroup (Fin 5)))
    (hn : (R : Subgroup G) ≤ normalizer (A : Set G)) : False := by
  obtain ⟨d, _⟩ := Theory.PSL2.exists_pgl_equiv_of_proper_normal_prime_psl L hC hL F
    (by omega) hF e
  obtain ⟨a⟩ := hA
  let B := A.map d.toMonoidHom
  let R' := R.mapSurjective (f := d.toMonoidHom) d.surjective
  have hn' : (R' : Subgroup (GorensteinWalter.PGL2 F)) ≤
      normalizer (B : Set (GorensteinWalter.PGL2 F)) := by
    change (R : Subgroup G).map d.toMonoidHom ≤
      normalizer (A.map d.toMonoidHom : Set (GorensteinWalter.PGL2 F))
    exact (map_mono hn).trans (A.le_normalizer_map d.toMonoidHom)
  have he := Theory.PSL2.pgl2_prime_eq_five_of_sylow_normalizes_alternating_five
    ho hF R' B ⟨(A.equivMapOfInjective d.toMonoidHom d.injective).symm.trans a⟩ hn'
  omega

/-- A full Sylow cannot be normal in a faithful extension of a nonabelian simple group. -/
theorem sylow_not_normal_of_faithful_simple [Finite G]
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] [Group.IsPerfect L]
    (hC : centralizer (L : Set G) = ⊥) (R : Sylow 2 G) :
    ¬ (R : Subgroup G).Normal := by
  intro hn
  let := hn
  have heven : 2 ∣ Nat.card L := by
    by_contra h
    have ho : Odd (Nat.card L) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using h)
    exact Group.IsPerfect.not_isSolvable L (odd_order_theorem L ho)
  have hRne := R.ne_bot_of_dvd_card (heven.trans L.card_subgroup_dvd_card)
  have hLR := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot L
    (Group.IsPerfect.not_isMulCommutative L) hC (R : Subgroup G) hRne
  let : Group.IsNilpotent L := (R.isPGroup'.to_le hLR).isNilpotent
  exact Group.IsPerfect.not_isSolvable L inferInstance

/-- If all maximal Sylow intersections are solvable, either uniqueness or a pair gives the dichotomy. -/
theorem dichotomy_of_solvable_intersections [Finite G]
    (L : Subgroup G) [L.Normal] (R : Sylow 2 G)
    (hgen : L ⊔ (R : Subgroup G) = ⊤) (hn : ¬ (R : Subgroup G).Normal)
    (hs : ∀ M : Subgroup G, IsCoatom M → (R : Subgroup G) ≤ M →
      Group.IsSolvable (M ⊓ L : Subgroup G)) :
    ChapterB.IsMinimalParabolicOver R ⊤ ∨ HasSolvableNormalizedCover L R := by
  classical
  have hR : (R : Subgroup G) ≠ ⊤ := by
    intro h
    exact hn (h ▸ inferInstanceAs ((⊤ : Subgroup G).Normal))
  obtain ⟨M, hM, hRM⟩ := (eq_top_or_exists_le_coatom (R : Subgroup G)).resolve_left hR
  by_cases hu : ∀ N : Subgroup G, IsCoatom N ∧ (R : Subgroup G) ≤ N → N = M
  · exact Or.inl ((ChapterB.isMinimalParabolicOver_top_iff R).mpr
      ⟨⟨M, ⟨hM, hRM⟩, hu⟩, hn⟩)
  · push Not at hu
    obtain ⟨N, ⟨hN, hRN⟩, hne⟩ := hu
    exact Or.inr (cover_of_two_solvable_intersections L R M N hgen hRM hRN hM hN
      hne.symm (hs M hM hRM) (hs N hN hRN))

/-- Proper faithful outer extensions have solvable intersections with every proper Sylow overgroup. -/
theorem proper_extension_solvable_intersection [Finite G]
    (L : Subgroup G) [L.Normal] (hC : centralizer (L : Set G) = ⊥)
    (hL : L ≠ ⊤) (R : Sylow 2 G) (hgen : L ⊔ (R : Subgroup G) = ⊤)
    (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 7 ≤ p) (hF : Nat.card F = p) (e : L ≃* PSL(2,F))
    (M : Subgroup G) (hM : M ≠ ⊤) (hRM : (R : Subgroup G) ≤ M) :
    Group.IsSolvable (M ⊓ L : Subgroup G) := by
  classical
  by_contra hns
  let A := M ⊓ L
  let A' := A.subgroupOf L
  let a : A' ≃* A := subgroupOfEquivOfLe (show A ≤ L from inf_le_right)
  have hA' : A' ≠ ⊤ := by
    intro h
    have hLM : L ≤ M := (subgroupOf_eq_top.mp h).trans inf_le_left
    exact hM (top_unique (hgen ▸ sup_le hLM hRM))
  have hns' : ¬ Group.IsSolvable A' := by
    intro h
    let := h
    exact hns (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)
  obtain ⟨_, ⟨b⟩⟩ := nonsolvable_proper_prime_model ho hF e A' hA' hns'
  have hnA : (R : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (hRM.trans M.le_normalizer) le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  exact no_five_in_proper_extension L hC hL R F ho hp hF e A ⟨a.symm.trans b⟩ hnA

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
