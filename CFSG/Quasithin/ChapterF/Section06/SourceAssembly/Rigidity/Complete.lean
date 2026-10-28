module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ContainedAction
public import Stellmacher.SectionTwo.IndexThreeOddOrbit
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.LocalProduct
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.OppositeExceptional

/-!
# Complete source Goldschmidt rigidity

For Y=Q2 L1, the original normal subgroup gives Sylow Q2 of index three.
In the noncubic case Y has characteristic two and F.6.12 supplies the
characteristic-subgroup obstruction. The index-three odd-orbit theorem
then constructs a nontrivial subgroup of Q2 normal in Y and invariant under
the actual Sylow-three conjugation action from G2. This contradicts the
strong invariant-subgroup clause of F.6.12.

Thus L1 is genuinely cubic. The already proved elementary-core and coset
bounds give every remaining clause of F.6.13. The universal legacy input
and the selected-component consumer are discharged here, with all original
subgroups, quotient maps, and relative normality retained.

Source: Aschbacher--Smith F.6.12--13 and F.6.17, printed pp.307,309.
The odd-orbit step uses the proved Stellmacher (2.5), avoiding the general
amalgam enumeration used by the printed A4 exclusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The contained residual is cubic for every actual normal-X source input. -/
theorem left_residual_card_three_of_normal_subgroup
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 := by
  classical
  by_contra hnc
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let Y := Q ⊔ L
  obtain ⟨S, hS, hi, hs, _⟩ := normal_subgroup_noncubic_local_product h hcore X h₁ h₂ hnc
  change (S : Subgroup Y).map Y.subtype = Q at hS
  have hP := local_product_characteristic_obstruction h hcore S hS
  let e : S ≃* Q := ((S : Subgroup Y).equivMapOfInjective
    Y.subtype Y.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  have hnQ : G₂ ≤ normalizer (Q : Set G) := h.symm.left_core_normalized
  let f : G₂ →* MulAut S := (MulAut.congr e.symm).toMonoidHom.comp
    (Q.normalizerMonoidHom.comp (inclusion hnQ))
  let D : Sylow 3 G₂ := Classical.choice inferInstance
  let U : Subgroup (MulAut S) := (D : Subgroup G₂).map f
  have hU : Odd (Nat.card U) := by
    obtain ⟨n, hn⟩ := (D.isPGroup'.map f).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  obtain ⟨N, hN, hnormal, hinv⟩ :=
    Stellmacher.SectionTwo.odd_invariant_normal_subgroup_of_index_three hs S hi hP U hU
  let A := (N.map (S : Subgroup Y).subtype).map Y.subtype
  have hAQ : A ≤ Q := (map_mono (f := Y.subtype) (map_subtype_le N)).trans_eq hS
  have hAN : (A.subgroupOf Y).Normal := by
    change ((N.map (S : Subgroup Y).subtype).map Y.subtype).subgroupOf Y |>.Normal
    simpa only [subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective] using hnormal
  have haction (d : G₂) (s : S) :
      (((f d s : S) : Y) : G) = (d : G) * ((s : Y) : G) * (d : G)⁻¹ := by
    have hh : e (f d s) = Q.normalizerMonoidHom (inclusion hnQ d) (e s) := by
      change e (e.symm _) = _
      exact e.apply_symm_apply _
    exact congrArg (fun x : Q => (x : G)) hh
  have hDA : (D : Subgroup G₂).map G₂.subtype ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    rintro d ⟨d', hd', rfl⟩ a ⟨a', ⟨s, hsN, rfl⟩, rfl⟩
    have hdU : f d' ∈ U := mem_map_of_mem f hd'
    have hn : f d' s ∈ N := hinv (f d') hdU (mem_map_of_mem (f d' : S →* S) hsN)
    change (d' : G) * ((s : Y) : G) * (d' : G)⁻¹ ∈ A
    rw [← haction d' s]
    exact mem_map_of_mem Y.subtype (mem_map_of_mem (S : Subgroup Y).subtype hn)
  have hAbot := h.right_invariant_subgroup_eq_bot hcore D A hAQ hDA hAN
  apply hN
  apply map_injective (S : Subgroup Y).subtype_injective
  apply map_injective Y.subtype_injective
  simpa only [Subgroup.map_bot] using hAbot

/-- Full source F.6.13, including both relative-normality clauses. -/
theorem source_lemma_F_6_13
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    let Q₁ := (pCore 2 G₁).map G₁.subtype
    let Q₂ := (pCore 2 G₂).map G₂.subtype
    let L₁ := (pResidual 2 G₁).map G₁.subtype
    let R₂ := pResidual 2 G₂
    let K₂ := (pCore 2 R₂).map (G₂.subtype.comp R₂.subtype)
    (X ⊔ G₂ = ⊤) ∧ (X ⊔ Q₂ : Subgroup G).Normal ∧
      (∃ S : Sylow 2 (X ⊔ Q₂ : Subgroup G),
        (S : Subgroup (X ⊔ Q₂ : Subgroup G)).map (X ⊔ Q₂ : Subgroup G).subtype = Q₂) ∧
      Nonempty (L₁ ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 Q₂ ∧ primeRank 2 Q₂ ≤ 3 ∧
      ((Q₂.subgroupOf (Q₂ ⊔ L₁)).Normal → Q₂ = ⊥) ∧
      ((K₂.subgroupOf (Q₂ ⊔ L₁)).Normal → K₂ = ⊥) ∧
      (pPrimeCore 2 X = ⊤ → ⁅Q₁, L₁⁆ = ⊥) := by
  dsimp only
  obtain ⟨hg, hn, hs⟩ := normal_subgroup_rigidity_setup h X h₁ h₂
  have hc := left_residual_card_three_of_normal_subgroup h hcore X h₁ h₂
  have hbad := left_not_characteristic_two_of_residual_cubic h hc
  obtain ⟨he, _, hr⟩ := right_core_small_elementary_of_not_characteristic_two h hcore hbad
  refine ⟨hg, hn, hs, ⟨mulEquivOfPrimeCardEq hc (by simp)⟩, he, hr, ?_, ?_, ?_⟩
  · intro hN
    exact h.right_invariant_subgroup_eq_bot hcore (Classical.choice inferInstance) _ le_rfl
      ((map_subtype_le _).trans h.symm.left_core_normalized) hN
  · exact right_residual_core_eq_bot_of_normal h hcore
  · intro _
    exact commutator_eq_bot_iff_le_centralizer.mpr (h.local_core_centralizes_residual hbad)

/-- The original universal F.6.13 input is now fully proved. -/
theorem goldschmidtRigidityInput : Noncyclic.GoldschmidtRigidityInput := by
  intro G _ _ G₁ G₂ h hcore X hX h₁ h₂
  let : X.Normal := hX
  exact source_lemma_F_6_13 h hcore X h₁ h₂

/-- The selected component in the actual F.6.17 reduction always has an
exceptional contained vertex; the both-characteristic-two branch is impossible. -/
theorem SingleResidualComponent.left_not_characteristic_two
    (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) : generalizedFitting G₁ ≠ pCore 2 G₁ := by
  let : d.component.Normal := d.normal
  exact left_not_characteristic_two_of_residual_cubic h
    (left_residual_card_three_of_normal_subgroup h hcore d.component
      d.left_contains d.right_escapes)

/-- The elementary Sylow conclusion on the very component selected by
F.6.10 now has no exceptional-vertex or rigidity premise. -/
theorem SingleResidualComponent.small_sylow
    (d : SingleResidualComponent G₁ G₂) (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) :
    Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 ∧
      IsSimpleGroup (d.component ⧸ center d.component) ∧
      ∃ S : Sylow 2 (d.component ⧸ center d.component),
        IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 :=
  d.small_sylow_of_exceptional_left h hcore (d.left_not_characteristic_two h hcore)

end CFSG.Quasithin.ChapterF.SourceAssembly
