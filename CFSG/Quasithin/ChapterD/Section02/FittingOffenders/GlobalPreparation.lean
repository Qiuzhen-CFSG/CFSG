module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly

/-!
# The shared source reductions for D.2.22

Generation by the actual starred actors kills C_V(O₃), since D.2.19 makes
all these actors noncyclic and D.2.14 makes each fix that subspace. It also
makes the complementary odd cores central. Consequently every involution
acts nontrivially on O₃ and its three-core centralizer is cyclic by the SQTK
cover theorem. The local configuration now acts on the original whole module.

Source: Aschbacher–Smith D.2.20–22, printed pp.188–189.
-/

public section
namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open ElementaryCore.SupportExclusion FittingConfigurations
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
  (hr : 1 < rank A)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
  (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤)
  (hgen : Jhat ρ = ⊤)

include hH f honto hf hA hr hF hcore hmoved in
theorem source_threeCore_elementary : IsElementaryAbelian 3 (pCore 3 G) := by
  obtain ⟨s,hs⟩ := source_reduced ρ hH f honto hf hA hr hF hcore hmoved
  let := hs.elementary
  let e := subgroupOfEquivOfLe (show pCore 3 G ≤ pCore 3 G ⊔ A from le_sup_left)
  exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_threeCore_fixedSpace_eq_bot : fixedSpace ρ (pCore 3 G) = ⊥ := by
  have hn := (source_ratio_and_noncyclic ρ hH f honto hf hA hr hF hcore hmoved).2.2
  apply (source_lemma_D_2_20 ρ hcore hmoved hgen).2
  intro B hB
  obtain ⟨hc,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hB (hn B hB) hF hcore
  exact (subspaceCommutator_eq_bot_iff _ _ _).mpr
    (fixed_complement_and_reduced_of_four ρ hf hB hF hcore hmoved hc hfix).1

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_threeCore_moved : subspaceCommutator ρ ⊤ (pCore 3 G) = ⊤ := by
  have hz := source_threeCore_fixedSpace_eq_bot ρ hH f honto hf hA hr hF hcore hmoved hgen
  have hodd : Odd (Nat.card (pCore 3 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  simpa only [hz, bot_sup_eq] using (moved_split ρ (pCore 3 G) hodd).sup_eq_top

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_complement_central : ⊤ ≤ centralizer (oddComplement G : Set G) := by
  have hn := (source_ratio_and_noncyclic ρ hH f honto hf hA hr hF hcore hmoved).2.2
  rw [← hgen]
  exact sSup_le fun B hB => le_centralizer_iff.mp
    (complement_centralizes ρ hf hB (hn B hB) hcore)

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_involution_threeCore_centralizer_cyclic (t : G) (ht : orderOf t = 2) :
    IsCyclic (pCore 3 G ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have htQ : t ∈ centralizer (oddComplement G : Set G) :=
    source_complement_central ρ hH f honto hf hA hr hF hcore hmoved hgen (mem_top t)
  have hnot : t ∉ centralizer (pCore 3 G : Set G) := by
    intro htP
    have htF : t ∈ centralizer (fittingSubgroup G : Set G) := by
      rw [fitting_eq_three_sup_complement (G := G)]
      intro x hx
      obtain ⟨p,hp,q,hq,rfl⟩ := mem_sup_of_normal_left.mp hx
      rw [mul_assoc, htQ q hq, ← mul_assoc, htP p hp, mul_assoc]
    have htF' : t ∈ fittingSubgroup G := by
      have hle : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G := by
        simpa only [hF] using centralizer_generalizedFitting_le G
      exact hle htF
    have ho := (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).of_dvd_nat
      ((fittingSubgroup G).orderOf_dvd_natCard htF')
    rw [ht] at ho
    exact (by decide : ¬ Odd 2) ho
  exact cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) f honto (hH.stronglyQuasithin 3 (by decide) (by decide))
    (pCore 3 G) pCore_isPGroup t ht hnot
    (pCore 3 G ⊓ centralizer ({t} : Set G))
    (pCore_isPGroup.to_le inf_le_left) inf_le_right

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_reduced_on_original_module :
    ∃ s : ℕ, Reduced (ρ.comp (pCore 3 G ⊔ A).subtype)
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) (A.subgroupOf (pCore 3 G ⊔ A)) s := by
  let P := pCore 3 G
  let L := P ⊔ A
  let P₀ := P.subgroupOf L
  let A₀ := A.subgroupOf L
  let σ := ρ.comp L.subtype
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨hcard,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hsupport := source_lemma_D_2_14_hyperplaneSupport ρ hf hA hcard hfix
  obtain ⟨hElem, ⟨s, hs, hcP, _⟩, hcomm⟩ :=
    ElementaryCore.elementary_structure_of_hyperplaneSupport ρ hf P A pCore_isPGroup
      hcard le_normalizer_of_normal hfaith hfix hsupport
  let : IsElementaryAbelian 3 P := hElem
  have hσ : Function.Injective σ := hf.comp L.subtype_injective
  have hstar : A₀ ∈ QhatStar σ := starred_subgroupOf ρ hA le_sup_right
  have hcA : Nat.card A₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ L from le_sup_right)).toEquiv).trans hcard
  have hcore' : pCore 3 L = P₀ := local_threeCore P A pCore_isPGroup
    (IsElementaryAbelian.isPGroup 2 A)
  have hfaith' : A₀ ⊓ centralizer (P₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1, ?_⟩
    intro p hp
    exact congrArg Subtype.val (ha.2 ⟨p,(le_sup_left : P ≤ L) hp⟩ hp)
  have hfix' : P₀ ⊓ centralizer (A₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro p hp
    apply Subtype.ext
    apply hfix.le
    refine ⟨hp.1, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hp.2 ⟨a,(le_sup_right : A ≤ L) ha⟩ ha)
  refine ⟨s, ⟨hσ, inferInstance, IsElementaryAbelian.subgroupOf le_sup_left,
    ?_, hs, hcA, hstar, ?_, hfaith', hfix', ?_, ?_, ?_⟩⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toEquiv).trans hcP
  · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, hcomm]
  · rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le le_sup_left]
    exact source_threeCore_moved ρ hH f honto hf hA hr hF hcore hmoved hgen
  · have hh := source_lemma_D_2_14_hyperplaneSupport σ hσ hstar hcA (hcore'.symm ▸ hfix')
    rw [hcore'] at hh
    exact hh

end CFSG.Quasithin.ChapterD.SourceReduction
