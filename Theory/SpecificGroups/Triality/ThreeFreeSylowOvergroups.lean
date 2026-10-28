module
public import Theory.SpecificGroups.Triality.SylowComponentUnique
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.SolvableMutualCommutator
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Three-free full-Sylow overgroups in binary triality

Every proper subgroup containing a full Sylow two-subgroup lies in a root
parabolic of the genuine graph-field D₄ carrier. Its intersection with the
normal local factor has a two-group kernel and a proper Sylow overgroup in
PSL₂(q³) or PSL₂(q). If three does not divide its order, that intersection
is solvable. The cyclic quotient by the local factor then proves solvability
of the original subgroup. This includes the central factor at q = 2.

The Chapter 10 application in Components/TrialityContaining uses this result
to force a cubic divisor in the original local component, without assuming
component distinctness. Together with full-Sylow component uniqueness it
closes the literal triality containing-pair row of 10.2.6.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749;
the root-parabolic construction is from GLS3 §§2.3--2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.ThreeFreeSylowOvergroups
open Parabolics

private theorem three_dvd_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card PSL(2,F) :=
  (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans
    (card_subgroup_dvd_card _)

private theorem solvable_of_rank_one_quotient
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (d : (G ⧸ pCore 2 G) ≃* PSL(2,F))
    (S : Sylow 2 G) (A : Subgroup G) (hSA : (S : Subgroup G) ≤ A)
    (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  let q := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
  have hn : A.map q ≠ ⊤ := by
    intro he
    have hd : 3 ∣ Nat.card (A.map q) := by
      rw [he,card_top]
      exact three_dvd_psl2 F
    exact h3 (hd.trans (card_dvd_of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)))
  have hss : SolvableSylowOvergroups PSL(2,F) :=
    .of_equiv (Theory.PSL2.sl2QuotientEquiv F).symm
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  exact (Group.isSolvable_map_iff_of_solvable_ker q A).mp
    (hss (S.mapSurjective hq) (A.map q) (map_mono hSA) hn)

private theorem localFactor_three_free (n : ℕ) (hn : 0 < n) (a : Node)
    (S : Sylow 2 (localFactor (binaryParameters n hn) a))
    (A : Subgroup (localFactor (binaryParameters n hn) a))
    (hSA : (S : Subgroup _) ≤ A) (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  cases a with
  | arms =>
    exact solvable_of_rank_one_quotient (F := ExtensionField (binaryParameters n hn))
      (localFactorArmsQuotientEquivPSL2 (binaryParameters n hn) rfl) S A hSA h3
  | central =>
    exact solvable_of_rank_one_quotient (F := GaloisField 2 n)
      (localFactorCentralQuotientEquivPSL2 (binaryParameters n hn) rfl) S A hSA h3

private theorem parabolic_three_free (n : ℕ) (hn : 0 < n) (a : Node)
    (S : Sylow 2 (BinaryCarrier n hn)) (A : Subgroup (BinaryCarrier n hn))
    (hSA : (S : Subgroup _) ≤ A) (hAP : A ≤ parabolic (binaryParameters n hn) a)
    (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  let P := binaryParameters n hn
  let J := parabolic P a
  let N := localFactor P a
  let B := A.subgroupOf N
  have hSN : (S : Subgroup _) ≤ N := sylow_le_localFactor P a S (hSA.trans hAP)
  let f : B →* A := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : BinaryCarrier n hn)) he
  let : Group.IsSolvable B := localFactor_three_free n hn a (S.subtype hSN) B
    (fun _ hx => hSA hx) (fun hd => h3 (hd.trans (card_dvd_of_injective f hf)))
  let : IsCyclic (J ⧸ N.subgroupOf J) := parabolic_quotient_isCyclic P rfl a
  let q : A →* J ⧸ N.subgroupOf J :=
    (QuotientGroup.mk' (N.subgroupOf J)).comp (inclusion hAP)
  apply Group.isSolvable_of_ker_le_range f q
  intro x hx
  have hxN : (x : BinaryCarrier n hn) ∈ N :=
    (QuotientGroup.eq_one_iff (inclusion hAP x)).mp hx
  exact ⟨⟨⟨x.val,hxN⟩,x.property⟩,rfl⟩

/-- A three-free subgroup containing a full Sylow two-subgroup of the genuine
binary triality carrier is solvable. -/
theorem isSolvable_of_three_free (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (BinaryCarrier n hn)) (A : Subgroup (BinaryCarrier n hn))
    (hSA : (S : Subgroup _) ≤ A) (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  let P := binaryParameters n hn
  have hd : 3 ∣ Nat.card (Carrier P) := by
    have hl : 3 ∣ Nat.card (levi P .central) := by
      rw [Nat.card_congr (leviCentralEquivPSL2 P rfl).toEquiv]
      exact three_dvd_psl2 (GaloisField 2 n)
    exact hl.trans (card_subgroup_dvd_card _)
  have hA : A ≠ ⊤ := by
    intro he
    exact h3 (by simpa only [he,card_top] using hd)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P rfl)
  let c := MulAut.conj g
  have hS : (S : Subgroup (Carrier P)).map c.toMonoidHom = unipotent P :=
    congrArg Sylow.toSubgroup hg
  have hAc : A.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hA
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic n hn (A.map c.toMonoidHom)
    (hS ▸ map_mono hSA) hAc
  have hs : Group.IsSolvable (A.map c.toMonoidHom) := parabolic_three_free n hn a
    (S.mapSurjective c.surjective) _ (map_mono hSA) ha
    (by rwa [card_map_of_injective c.injective])
  let : Group.IsSolvable c.toMonoidHom.ker := by
    rw [c.toMonoidHom.ker_eq_bot_iff.mpr c.injective]
    infer_instance
  exact (Group.isSolvable_map_iff_of_solvable_ker c.toMonoidHom A).mp hs

end Triality.Standard.ThreeFreeSylowOvergroups
