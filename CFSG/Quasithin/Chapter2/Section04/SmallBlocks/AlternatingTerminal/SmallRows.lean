module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SourceTransfers
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.AlternatingModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.OddModels
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.JankoTwo
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.SmallModuleRanks.M12
/-! Native order, binary-rank and odd-characteristic screens retain the
literal deleted-five layer. The source consumer maps that same layer through
its faithful component two-core quotient. Source: Aschbacher–Smith 2.4.25,
printed p.543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open ChapterC Chapter13.Section05.NormalBranch.DeletedFive
open Chapter15.Section03.Candidates.ComponentStructure
variable {D : Type*} [Group D] [Finite D]
omit [Finite D] in
/-- The actual order and elementary layer exclude the three small sporadic rows. -/
theorem small_sporadic_no_alternating_five_block
    (name : ClassificationModels.SporadicName)
    (hn : name = .m11 ∨ name = .m12 ∨ name = .j2)
    (e : D ≃* name.Carrier) (A : Subgroup D) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  rcases hn with rfl | rfl | rfl
  · have hd := card_dvd_of_alternatingFive A hA hc
    rw [Nat.card_congr e.toEquiv] at hd
    change 960 ∣ Nat.card Sporadic.Mathieu.M11 at hd
    rw [Sporadic.Mathieu.m11_order] at hd
    exact (by decide : ¬960 ∣ 7920) hd
  · let e12 : D ≃* Sporadic.Mathieu.M12 := e
    let U := (blockU A).map A.subtype
    let : IsElementaryAbelian 2 (blockU A) := hA.2.1.elementary
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.map A.subtype
    have helem : IsElementaryAbelian 2 (U.map e12.toMonoidHom) := IsElementaryAbelian.map _
    have hb := (primeRank_le_iff_elementary_card_le Sporadic.Mathieu.M12).mp
      Sporadic.Mathieu.m12_twoRank_le_three (U.map e12.toMonoidHom) helem
    have hcard : Nat.card (U.map e12.toMonoidHom) = Nat.card U := card_map_of_injective e12.injective
    have hb' : Nat.card U ≤ 2 ^ 3 := hcard ▸ hb
    change Nat.card U = 16 at hc
    omega
  · exact no_alternatingFive_of_j2_equiv e A hA hc

/-- Both odd families of the marked catalogue have insufficient binary rank. -/
theorem odd_no_alternating_five_block [Group.IsPerfect D]
    (hm : ClassicalGroup.IsPSL D 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL D 2 p)
    (A : Subgroup D) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  let : IsElementaryAbelian 2 (blockU A) := hA.2.1.elementary
  have he : IsElementaryAbelian 2 ((blockU A).map A.subtype) := IsElementaryAbelian.map _
  apply not_oddModel_of_elementary_sixteen _ he hc
  rcases hm with hm | ⟨p,hp,hm⟩
  · exact .linear_three 3 (by decide) (by decide) hm
  · have hp5 := Chapter16.OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hm
    exact .linear_two p 1 hp.1 (hp.1.odd_of_ne_two (by omega)) (by decide)
      (by simpa only [pow_one] using hm)

/-- The direct and triple-cover alternating actor rows both contradict the block order. -/
theorem alternating_action_no_alternating_five_block
    (a : MulAut D) {n : ℕ} (hn : n = 6 ∨ n = 7) (s : Equiv.Perm (Fin n))
    (hm : AlternatingAction a n s)
    (A : Subgroup D) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  rcases hm with ⟨e,_⟩ | ⟨_,⟨ez⟩,e,_⟩
  · exact not_alternating_of_alternatingFive A hA hc (by omega) e
  · have hd := card_dvd_of_alternatingFive A hA hc
    have hz : Nat.card (center D) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      simp
    rw [card_eq_card_quotient_mul_card_subgroup (center D),hz,
      Nat.card_congr e.toEquiv] at hd
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] at hd <;> norm_num at hd
end CFSG.Quasithin.Chapter2.AlternatingTerminal
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}
theorem AlternatingPairSourceSetup.small_sporadic_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
    SI S L ≤ normalizer (K.map GI.subtype : Set G) →
    ∀ name : ClassificationModels.SporadicName,
    (name = .m11 ∨ name = .m12 ∨ name = .j2) →
    Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) → False := by
  intro S L GI K hK hLK hNK name hn he
  let : Finite name.Carrier := Finite.of_equiv (K ⧸ pCore 2 K) he.some.toEquiv
  exact c.no_block_quotient_overcomponent_false hG T hM hTM hu hST hSM hMT hi
    K hK hLK hNK (AlternatingTerminal.small_sporadic_no_alternating_five_block
      name hn (MulEquiv.refl _)) he
end CFSG.Quasithin.Chapter2
