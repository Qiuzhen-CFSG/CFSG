module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.PairedMinimality
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# B.2 lifting for the paired natural-eight actions

Apply the proved B.2 maximum-image and constructive replacement theorems to
the range of each restricted action. Fixed-subgroup ranks identify their
weights with those on the natural S8 module, including every subimage. Thus
B.2.5 and B.2.8 require no surjectivity of the restricted action onto S8.
The consumer `Configuration.lifting_inputs` discharges all three B.2 premises
of the paired-minimality theorem for the actual two conjugate modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.5–8,
printed pp.76–77, applied in the proof of 15.3.25, pp.1133–1134.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedMinimality
open Subgroup Stellmacher Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem lifting_of_fixed_rank
    (S U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (f : G →* EightPerm)
    (hf : f.ker = centralizer (U : Set G))
    (hfix : ∀ A : Subgroup G, rank (U ⊓ centralizer (A : Set G)) =
      Module.finrank (ZMod 2) (fixedSpace eightRepresentation (A.map f))) :
    Lifting S f ∧ ConstructiveReplacement S U f := by
  let q := f.rangeRestrict
  have hq := f.rangeRestrict_surjective
  have hk : q.ker = centralizer (U : Set G) := by
    simpa only [q, MonoidHom.ker_rangeRestrict] using hf
  let ρ := representation U q hq hk
  have hw (A : Subgroup G) : weight ρ (A.map q) = weight eightRepresentation (A.map f) := by
    have hr : rank (A.map q) = rank (A.map f) := by
      have hm : (A.map q).map f.range.subtype = A.map f := by rw [map_map]; rfl
      rw [← hm, rank_map_injective _ f.range.subtype_injective]
    have hc : Module.finrank (ZMod 2) (fixedSpace ρ (A.map q)) =
        rank (U ⊓ centralizer (A : Set G)) := by
      rw [rank, ← Nat.card_congr (fixedSpaceEquiv U q hq hk A),
        Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Nat.log_pow Nat.one_lt_two]
    exact congrArg₂ (· + ·) hr (hc.trans (hfix A))
  have pre (A : Subgroup G) (E : Subgroup EightPerm) (hEA : E ≤ A.map f) :
      (preimage A f E).map f = E := by
    apply le_antisymm (map_le_iff_le_comap.mpr inf_le_right)
    intro e he
    obtain ⟨a, ha, rfl⟩ := hEA he
    exact mem_map_of_mem f ⟨ha, he⟩
  have best (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups S)
      (hne : A.map f ≠ ⊥) : IsBestOffender eightRepresentation (A.map f) := by
    have hnq : A.map q ≠ ⊥ := by
      intro he
      apply hne
      have hm : (A.map q).map f.range.subtype = A.map f := by rw [map_map]; rfl
      rw [← hm, he, Subgroup.map_bot]
    have hb := StarSelection.maxElementary_isBestOffender U q hq hk S A hUS hA hnq
    refine ⟨⟨hne, hA.2.1.map f⟩, ?_⟩
    intro E hEA
    have hh := hb.2 ((preimage A f E).map q) (map_mono inf_le_left)
    rw [hw, hw, pre A E hEA] at hh
    exact hh
  have replace (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups S)
      (E : Subgroup EightPerm) (hE : IsElementaryTwo E)
      (he : EqualWeightLE eightRepresentation E (A.map f)) :
      replacement U A f E ∈ elementaryAbelianMaxSubgroups S ∧
        (replacement U A f E).map f = E := by
    let B := preimage A f E
    let D := B.map q
    have hBf : B.map f = E := pre A E he.1
    have hd : IsElementaryTwo D := by
      refine ⟨?_, ?_⟩
      · intro hz
        apply hE.1
        have hm : D.map f.range.subtype = E := by rw [map_map]; exact hBf
        rw [← hm, hz, Subgroup.map_bot]
      · let _ := hA.2.1
        let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le inf_le_left
        exact IsElementaryAbelian.map q
    have he' : EqualWeightLE ρ D (A.map q) := by
      refine ⟨map_mono inf_le_left, ?_⟩
      change weight ρ (B.map q) = weight ρ (A.map q)
      rw [hw, hw, hBf]
      exact he.2
    have hb0 : A ⊓ D.comap q = B := by
      ext x
      constructor
      · rintro ⟨hx, b, hb, heq⟩
        have heqf : f b = f x := congrArg Subtype.val heq
        refine ⟨hx, ?_⟩
        change f x ∈ E
        rw [← heqf]
        exact hb.2
      · intro hx
        exact ⟨hx.1, mem_map_of_mem q hx⟩
    have hh := ChapterB.lemma_B_2_8_construct U q hq hk S hUS A hA D hd he'
    dsimp only at hh
    rw [hb0] at hh
    refine ⟨hh.1, ?_⟩
    have hm := congrArg (Subgroup.map f.range.subtype) hh.2
    have hmD : D.map f.range.subtype = E := by rw [map_map]; exact hBf
    rw [hmD, map_map] at hm
    exact hm
  exact ⟨⟨best, fun A hA E hE he => ⟨_, replace A hA E hE he⟩⟩,
    fun A hA E hE he => (replace A hA E hE he).1⟩

/-- B.2.5 and B.2.8 for a restricted natural-eight action. The restriction
need not be onto S8: the proof descends to its actual image. -/
theorem natural_lifting_and_replacement {I U J : Subgroup G}
    (a : NaturalEightAction I U) (hJI : J ≤ I) (hUJ : U ≤ J)
    (S : Subgroup J) (hUS : U.subgroupOf J ≤ S)
    [(U.subgroupOf J).Normal] [IsElementaryAbelian 2 (U.subgroupOf J)]
    (hk : (a.restrictActor J hJI).ker = centralizer (U.subgroupOf J : Set J)) :
    Lifting S (a.restrictActor J hJI) ∧
      ConstructiveReplacement S (U.subgroupOf J) (a.restrictActor J hJI) := by
  apply lifting_of_fixed_rank S (U.subgroupOf J) hUS _ hk
  intro A
  have hd := a.fixedCodim_restrict J hJI hUJ A
  have hdim : Module.finrank (ZMod 2) (natural (Fin 8)) = 6 := by
    simpa using finrank_natural_even (Fin 8) (by decide)
  have hu : rank (U.subgroupOf J) = 6 := by
    rw [rank, Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv]
    exact a.rank_module
  have hh := fixedCodim_add_finrank eightRepresentation (A.map (a.restrictActor J hJI))
  have hle : rank (U.subgroupOf J ⊓ centralizer (A : Set J)) ≤ rank (U.subgroupOf J) :=
    Nat.log_mono_right (Nat.card_le_card_of_injective _
      (inclusion_injective (inf_le_left : U.subgroupOf J ⊓ centralizer (A : Set J) ≤ U.subgroupOf J)))
  change _ + _ = Module.finrank (ZMod 2) (natural (Fin 8)) at hh
  rw [hdim] at hh
  rw [hu] at hd hle
  change fixedCodim eightRepresentation (A.map (a.restrictActor J hJI)) = _ at hd
  omega

/-- All B.2 inputs of the paired-minimality interface are discharged by the
actual two module actions in the configuration. -/
theorem Configuration.lifting_inputs {d : LocalData G} {I L X : Subgroup G} {t : G}
    (c : Configuration d I L X t) :
    Lifting c.S c.f ∧ Lifting c.S c.g ∧ ConstructiveReplacement c.S c.V c.g := by
  let _ := c.first_normal
  let _ := c.second_normal
  let _ := c.first_elementary
  let _ := c.second_elementary
  have hf := natural_lifting_and_replacement c.action c.local_le
    (c.first_le.trans le_sup_right) c.S (fun _ h => c.first_le h) c.first_kernel
  have hg := natural_lifting_and_replacement c.conjugateAction c.local_le_conjugate
    (c.second_le.trans le_sup_right) c.S (fun _ h => c.second_le h) c.second_kernel
  exact ⟨hf.1, hg⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedMinimality
