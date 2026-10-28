module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.SylowContainingTwoLocal

/-!
# Solvable quotient obstructions for local alternating-five sections

The smaller local C-component is perfect and its two-core quotient is simple.
A solvable ambient kernel therefore preserves that literal quotient. Passing
the full Sylow and local-component condition to the image excludes symmetric
six and binary linear four quotients. These are the local quotients needed
in the M24 and Held rows of Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] in
/-- The actual alternating-five quotient contributes a factor five. -/
theorem five_dvd_card (B : Subgroup G)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : 5 ∣ Nat.card B := by
  have hd := card_quotient_dvd_card (pCore 2 B)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd
  exact (by decide : 5 ∣ 60).trans hd

/-- A nontrivial characteristic two-core gives a common maximal two-local
overgroup of the original subgroup and its normalizing full Sylow. -/
theorem exists_maximal_two_local (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) (hc : pCore 2 B ≠ ⊥) :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ B ≤ N ∧ (S : Subgroup G) ≤ N := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U, hU, pCore_isPGroup.map B.subtype, rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  exact ⟨N, hN, B.le_normalizer.trans (hnorm.trans hNN), hn.trans (hnorm.trans hNN)⟩

omit [Finite G] in
/-- A local C-component is perfect as its original subgroup type. -/
theorem local_perfect {S : Subgroup G} {B : Subgroup G}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- A solvable kernel preserves the original alternating-five two-core quotient. -/
theorem section_map (q : G →* H) [Group.IsSolvable q.ker]
    {S : Subgroup G} (B : Subgroup G) (hB : B ∈ localCComponents S)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5)) := by
  let := local_perfect hB
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap q.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : q.ker => (x : G)) he)))
  exact ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv f
    (q.subgroupMap_surjective B)).symm.trans e⟩

/-- Equivalence transport retains both the original full Sylow and section. -/
theorem not_section_of_equiv (e : G ≃* H)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hex : ∀ (T : Sylow 2 H) (A : Subgroup H), A ∈ localCComponents T →
      (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) → False) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact hex (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom)
    (section_map e.toMonoidHom B hB eB).some

private theorem altSix_core : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with h|h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) := h ▸ pCore_isPGroup
    obtain ⟨n,hn⟩ := (hp.of_equiv topEquiv).exists_card_eq
    have hc : Nat.Coprime (2^n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    rw [←hn,nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc

private theorem altSix_not_section (S : Sylow 2 (alternatingGroup (Fin 6)))
    (B : Subgroup (alternatingGroup (Fin 6))) (hB : B ∈ localCComponents S)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hcard : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  by_cases ht : B = ⊤
  · let d : B ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr ht).trans topEquiv
    have hd := Nat.card_congr (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).toEquiv
    rw [altSix_core, Nat.card_congr QuotientGroup.quotientBot.toEquiv,
      nat_card_alternatingGroup,hcard] at hd
    norm_num at hd
  · exact AlternatingSmall.not_proper_six S B hB ht (MulEquiv.refl _)

/-- No full-Sylow local C-component of S6 has two-core quotient A5. -/
theorem symmetric_six_not_section (S : Sylow 2 (Equiv.Perm (Fin 6)))
    (B : Subgroup (Equiv.Perm (Fin 6))) (hB : B ∈ localCComponents S)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let := local_perfect hB
  have hBA : B ≤ alternatingGroup (Fin 6) := by
    intro b hb
    rw [Equiv.Perm.mem_alternatingGroup]
    let f := Equiv.Perm.sign.comp B.subtype
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨b,hb⟩) 1)
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal (alternatingGroup (Fin 6))
  let d := subgroupOfEquivOfLe hBA
  apply altSix_not_section T (B.subgroupOf (alternatingGroup (Fin 6))) _
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e)
  rw [hT]
  exact local_restrict hB hBA

/-- A solvable extension of S6 has no full-Sylow local A5 section. -/
theorem symmetric_six_quotient_not_section
    (q : G →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False :=
  symmetric_six_not_section (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB q)
    (section_map q B hB eB).some

/-- A solvable extension of PSL4(2) has no full-Sylow local A5 section. -/
theorem binary_four_quotient_not_section
    (q : G →* PSL(4, ZMod 2)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False :=
  BinaryLinear.not_section_binary_linear (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB q)
    (section_map q B hB eB).some (Or.inl rfl)
    ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
