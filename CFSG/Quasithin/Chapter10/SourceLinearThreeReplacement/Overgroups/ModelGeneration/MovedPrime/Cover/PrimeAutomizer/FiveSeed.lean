module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Solvable invariant seeds in alternating five subgroups

The Sylow normalizer of an A₅ subgroup is a solvable invariant seed.
Its cubic part cannot centralize a marked involution, whose centralizer
is a two-group. The literal ambient subgroup and acting two-subgroup
are retained for the prime-field automizer application.

Source application: Aschbacher--Smith E.1.12 and 10.3.3, pp.214 and 756.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
variable {G : Type*} [Group G] [Finite G]

private theorem five_normalizer_card (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (normalizer (P : Set (alternatingGroup (Fin 5)))) = 12 := by
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  rw [hi]
  let (j : Fin 5) : DecidablePred (· ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) j) :=
    fun x => inferInstanceAs (Decidable (x.val j = j))
  rw [Nat.card_eq_fintype_card]
  clear hi P
  revert i
  decide +kernel

theorem five_sylow_normalizer_seed (A : Subgroup G) (R : Subgroup G)
    (hn : R ≤ normalizer (A : Set G)) (P : Sylow 2 A)
    (hP : (P : Subgroup A).map A.subtype = R ⊓ A)
    (e : A ≃* alternatingGroup (Fin 5)) (t : G) (ht : orderOf t = 2) (htA : t ∈ A) :
    ∃ B : Subgroup G, B ≤ A ∧ Group.IsSolvable B ∧
      R ≤ normalizer (B : Set G) ∧ ¬ B ≤ centralizer ({t} : Set G) := by
  let V := R ⊓ A
  let B := A ⊓ normalizer (V : Set G)
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hNp : (normalizer (P : Set A)).map e.toMonoidHom = normalizer (P' : Set _) :=
    map_equiv_normalizer_eq _ e
  have hNc : Nat.card (normalizer (P : Set A)) = 12 := by
    rw [← card_map_of_injective (K := normalizer (P : Set A)) (f := e.toMonoidHom) e.injective, hNp]
    exact five_normalizer_card P'
  have hproper : normalizer (P : Set A) ≠ ⊤ := by
    intro h
    have hh := congrArg (Subgroup.map e.toMonoidHom) h
    rw [hNp, map_top_of_surjective _ e.surjective] at hh
    exact (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom P').1 hh
  have hBmap : (normalizer (P : Set A)).map A.subtype = B := by
    have hcomap : V.subgroupOf A = (P : Subgroup A) := by
      change (R ⊓ A).subgroupOf A = _
      rw [← hP]
      exact comap_map_eq_self (by rw [A.ker_subtype]; exact bot_le)
    have hN : (normalizer (V : Set G)).subgroupOf A = normalizer (P : Set A) := by
      rw [subgroupOf_normalizer_eq (show V ≤ A from inf_le_right), hcomap]
      rfl
    rw [← hN, subgroupOf_map_subtype, inf_comm]
  have hsN := alternatingGroup.isSolvable_subgroup_of_equiv_five e _ hproper
  have hsB : Group.IsSolvable B := by
    let := hsN
    rw [← hBmap]
    let eN := (normalizer (P : Set A)).equivMapOfInjective A.subtype A.subtype_injective
    exact Group.isSolvable_of_surjective (f := eN.toMonoidHom) eN.surjective
  have hRV : R ≤ normalizer (V : Set G) :=
    (le_inf R.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  have hRN : R ≤ normalizer (normalizer (V : Set G) : Set G) :=
    hRV.trans (normalizer (V : Set G)).le_normalizer
  have hRB : R ≤ normalizer (B : Set G) :=
    (le_inf hn hRN).trans inf_normalizer_le_normalizer_inf
  refine ⟨B, inf_le_left, hsB, hRB, ?_⟩
  intro hcentral
  let tA : A := ⟨t, htA⟩
  let C := centralizer ({e tA} : Set (alternatingGroup (Fin 5)))
  have hC : IsPGroup 2 C := alternatingGroup.isPGroup_centralizer_involution_of_degree_le_six
    (by decide) (e tA) ((e.orderOf_eq tA).trans ((orderOf_coe tA).symm.trans ht))
  let f : B →* C := (e.toMonoidHom.comp (Subgroup.inclusion (show B ≤ A from inf_le_left))).codRestrict C (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    change e (Subgroup.inclusion (show B ≤ A from inf_le_left) b) * e tA =
      e tA * e (Subgroup.inclusion (show B ≤ A from inf_le_left) b)
    rw [← map_mul, ← map_mul]
    apply congrArg e
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hcentral b.property))
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) (e.injective (congrArg Subtype.val h))
  have hBc : Nat.card B = 12 := by
    rw [← hBmap, card_map_of_injective A.subtype_injective, hNc]
  obtain ⟨n, hn⟩ := (hC.of_injective f hf).exists_card_eq
  have hd : 3 ∣ 2 ^ n := by rw [← hn, hBc]; decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
