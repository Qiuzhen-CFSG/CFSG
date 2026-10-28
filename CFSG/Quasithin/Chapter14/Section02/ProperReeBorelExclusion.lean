module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.SolvableSylowThreeFree

/-!
# The proper-completion Ree Borel exclusion

Restrict the supplied ambient Sylow subgroup to the actual subnormal
component L, then map the solvable intersection (YS)∩L through the marked
Ree quotient. The native Borel theorem excludes a factor of three in its
order, even with a two-group kernel. Since Y lies in that intersection,
three cannot divide |Y|. The central-quotient specialization uses the
literal quotient map and the model equivalence of the Ree input.

For the original 14.2.15 completion X=K₁YS and its canonical solvable
residual L, the final theorem proves the Sylow restriction, solvability,
and the factor of three in |Y| from the source prefix. The cubic image of
Y is the actual image in the local action quotient. Only the source
placement Y≤L and the marked Ree quotient remain explicit: this module
does not assert the A.3.12 containing-family comparison or A.3.18.

Source: Aschbacher--Smith, 14.2.15, printed pp.985--986; F.1.12.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A solvable full-Sylow overgroup excludes the marked Ree quotient of L. -/
theorem proper_ree_borel_exclusion
    (X L Y S : Subgroup G) (hLX : L ≤ X)
    (hL : (L.subgroupOf X).IsSubnormal) (hYL : Y ≤ L)
    (hS : Chapter1.IsSylowIn 2 S X) (hsolv : Group.IsSolvable (Y ⊔ S : Subgroup G))
    (hthree : 3 ∣ Nat.card Y)
    {m : ℕ} (hm : 1 ≤ m) (q : L →* ReeF4.Model m)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) : False := by
  obtain ⟨P, hP⟩ := hS
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf X) hL
  let e := subgroupOfEquivOfLe hLX
  let U : Sylow 2 L := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let K := (Y ⊔ S).subgroupOf L
  have hUK : (U : Subgroup L) ≤ K := by
    rintro x ⟨a, ha, rfl⟩
    have hp : (a : X) ∈ (P : Subgroup X) := by
      change a ∈ (P : Subgroup X).subgroupOf (L.subgroupOf X)
      rwa [← hQ]
    have hs : ((a : X) : G) ∈ S := hP ▸ mem_map_of_mem X.subtype hp
    change ((a : X) : G) ∈ Y ⊔ S
    exact mem_sup_right hs
  let _ := hsolv
  let j : K →* (Y ⊔ S : Subgroup G) := {
    toFun x := ⟨((x : L) : G), x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (Y ⊔ S : Subgroup G) => (z : G)) h
  have hc := ReeF4.Parabolics.coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    hm q hq hk U K (Group.isSolvable_of_isSolvable_injective hj) hUK
  have hY : Y.subgroupOf L ≤ K := comap_mono le_sup_left
  have hcY := hc.of_dvd_right (card_dvd_of_le hY)
  rw [Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv] at hcY
  exact Nat.prime_three.coprime_iff_not_dvd.mp hcY hthree

/-- The literal central quotient gives the same obstruction for a central two-kernel. -/
theorem proper_ree_center_quotient_exclusion
    (X L Y S : Subgroup G) (hLX : L ≤ X)
    (hL : (L.subgroupOf X).IsSubnormal) (hYL : Y ≤ L)
    (hS : Chapter1.IsSylowIn 2 S X) (hsolv : Group.IsSolvable (Y ⊔ S : Subgroup G))
    (hthree : 3 ∣ Nat.card Y) (hc : IsPGroup 2 (center L))
    {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At (L ⧸ center L) m) : False := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let f := (e.trans d.modelEquiv).toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f :=
    (e.trans d.modelEquiv).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    ext x
    change (e.trans d.modelEquiv) (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [← map_one (e.trans d.modelEquiv), (e.trans d.modelEquiv).injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  exact proper_ree_borel_exclusion X L Y S hLX hL hYL hS hsolv hthree hm f hf
    (hk ▸ hc)

/-- The original residual supplies the nontrivial three-part internally. Only
its placement and the actual Ree quotient with a two-kernel remain explicit. -/
theorem source_proper_completion_ree_borel_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥)
    {m : ℕ} (hm : 1 ≤ m) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    sourceResidual M Mc ≤ L → ∀ q : L →* ReeF4.Model m,
      Function.Surjective q → IsPGroup 2 q.ker → False := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let Y := sourceResidual M Mc
  change Y ≤ L → ∀ q : L →* ReeF4.Model m,
    Function.Surjective q → IsPGroup 2 q.ker → False
  intro hYL q hq hk
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e
    H hH K S hST hi hN hplacement hcore
  have hLE : L.subgroupOf X = solvableResidual X :=
    comap_map_eq_self_of_injective X.subtype_injective _
  have hnormal : (L.subgroupOf X).Normal := by rw [hLE]; infer_instance
  let : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G) :=
    source_residualSylow_solvable hG T hempty hM hu hmany hcard e
  have hsolv : Group.IsSolvable (Y ⊔ S : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (sup_le_sup_left hST Y))
  obtain ⟨_,_,_,_,heY,_,_,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hc : Nat.card (localActionImage (centralInvolutions T) M Y) = 3 :=
    (Nat.card_congr heY.some.toEquiv).trans (Nat.card_zmod 3)
  have hd := card_map_dvd (Y.subgroupOf M) (localActionMap (centralInvolutions T) M)
  rw [Nat.card_congr (subgroupOfEquivOfLe (sourceResidual_le M Mc)).toEquiv] at hd
  change Nat.card (localActionImage (centralInvolutions T) M Y) ∣ Nat.card Y at hd
  rw [hc] at hd
  exact proper_ree_borel_exclusion X L Y S (map_subtype_le _) hnormal.isSubnormal
    hYL hs hsolv hd hm q hq hk

end CFSG.Quasithin.Chapter14.Section02
