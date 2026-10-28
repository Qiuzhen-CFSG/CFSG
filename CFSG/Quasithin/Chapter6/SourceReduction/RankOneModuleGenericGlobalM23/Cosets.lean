module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Marking
public import Theory.GroupAction.OrbitFamilyEquivalence
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.FieldExtension
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.PairOrbit

/-!
# The original coset orbit and exceptional-local intersection

Maximality of H inside the original exceptional J forces (L ∨ H) ∩ J = H.
The alternative J ≤ L ∨ H would give equality by their computed orders,
contradicting original uniqueness over L and the residual's escape.
The same heptad marking therefore identifies the actual J-orbit of the
base coset in G/(L ∨ H) with every two-subset of the native heptad. The
formula retains the full J-action, its two-core and the original H.

Source: Aschbacher–Smith 5.2.19(1–2), printed p.656 (`refs/quasithin.pdf`).
The source edge fixer and ambient generation remain further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Sporadic.Mathieu.M23Geometry
variable {G : Type*} [Group G] [Finite G]

/-- Source 5.2.19(1): the intersection uses the original Sylow enlargement,
not an abstract copy of its isomorphism type. -/
theorem Preparation.linear_exceptional_pair_intersection
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : (L ⊔ H : Subgroup G) ⊓ J = H := by
  obtain ⟨hTJ,hHJ,hmax,_,_,_,_,hcardJ⟩ :=
    d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  have hcardX := (d.linear_nonmaximal_extension_geometry h hH hp F hm hF he hnonmax).2
  obtain ⟨_,_,_,_,_,_,hmaxH⟩ := d.linear_exceptional_pair_marking h hH hp F hm hF he hJ hKJ
  have hproper : (L ⊔ H).subgroupOf J ≠ ⊤ := by
    intro htop
    have hJX : J ≤ L ⊔ H := subgroupOf_eq_top.mp htop
    have heq : J = L ⊔ H := eq_of_le_of_card_ge hJX (by rw [hcardJ,hcardX])
    have hLJ : L ≤ J := heq ▸ (show L ≤ L ⊔ H from le_sup_left)
    have hJM := d.unique_left J hmax hLJ
    exact d.right_outside (hJM ▸ hKJ.le)
  have heq : H.subgroupOf J = (L ⊔ H).subgroupOf J :=
    ((hmaxH.le_iff_eq hproper).mp (subgroupOf_mono J le_sup_right)).symm
  have hh := congrArg (Subgroup.map J.subtype) heq
  rw [map_subgroupOf_eq_of_le hHJ,subgroupOf_map_subtype] at hh
  exact hh.symm

/-- Source 5.2.19: the actual J-orbit of the base coset is equivariantly
identified with the native heptad orbit by the same full local marking. -/
theorem Preparation.linear_exceptional_coset_orbit
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : ∃ (ζ : J ≃* heptadStabilizer)
        (e : MulAction.orbit J ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ≃
          {p : Finset (Fin 23) // p.card = 2 ∧ p ⊆ omega}),
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ∀ j : J, (e ⟨j • ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)),
        MulAction.mem_orbit _ j⟩).val = ζ j • x.val := by
  obtain ⟨ζ,hU,_,hHm⟩ := d.linear_exceptional_pair_heptad_marking h hH hp F hm hF he hJ hKJ
  have hi := d.linear_exceptional_pair_intersection h hH hp F hm hF he hJ hKJ
  let x0 := ((1 : G) : G ⧸ (L ⊔ H : Subgroup G))
  have hs : MulAction.stabilizer J x0 = H.subgroupOf J := by
    ext j
    change (j:G) • x0 = x0 ↔ (j:G) ∈ H
    have hh : (j:G) ∈ (L ⊔ H : Subgroup G) ↔ (j:G) ∈ H := by
      constructor
      · intro hj
        exact hi ▸ (show (j:G) ∈ (L ⊔ H : Subgroup G) ⊓ J from ⟨hj,j.property⟩)
      · exact fun hj => mem_sup_right hj
    exact (show (j:G) ∈ MulAction.stabilizer G x0 ↔ (j:G) ∈ H by
      rw [MulAction.stabilizer_quotient]; exact hh)
  have hs' : (MulAction.stabilizer J x0).map ζ.toMonoidHom =
      MulAction.stabilizer heptadStabilizer x.val := by
    rw [hs,hHm]
    rfl
  refine ⟨ζ,(MulAction.orbitEquivOfStabilizerMap ζ x0 x.val hs').trans
    (Equiv.setCongr heptad_pair_orbit),hU,hHm,?_⟩
  exact MulAction.orbitEquivOfStabilizerMap_apply ζ x0 x.val hs'

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
