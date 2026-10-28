module
public import Theory.Representation.BinaryPermutation.EightElementaryCertificate
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.Representation.BinaryOffender.Basic

/-!
# Three fixed-space extensions for elementary actors on the binary six-space

Place an elementary S8 subgroup in the binary-tree Sylow subgroup. The
checked extension table finds its exact row; excluding vector orbits of
size two leaves eight rows. In each, three actual vector stabilizers meet
in an index-eight subgroup and strictly enlarge the common fixed space.
Conjugation transports the same subgroups back to the original actor.

Source: Aschbacher--Smith,12.6.28(2), printed pp.833--834.
-/
public section
open Subgroup BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Representation.BinaryOffender
namespace BinaryPermutation.EightThreeExtensions
open EightElementaryCertificate
abbrev S := Equiv.Perm (Fin 8)
abbrev N := natural (Fin 8)
abbrev ρ := naturalRepresentation (Fin 8)
local instance : MulAction S N where
  smul a v := ρ a v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul a b v := by change ρ (a*b) v = ρ a (ρ b v); rw [map_mul,Module.End.mul_apply]

private theorem fixes_iff (i : Fin 128) (v : core (Fin 8)) :
    fixes i v ↔ ρ (treeWord i) (coreToNatural (Fin 8) v) = coreToNatural (Fin 8) v := by
  rw [← sub_eq_zero,←coreToNatural_equivariant,←map_sub,EightGeometry.coreToNatural_eq_zero]
  rfl

private theorem members_zero : members 0 = {0} := rfl

private theorem catalogue (A : Subgroup S) [IsElementaryAbelian 2 A]
    (_hA : A ≤ treeGroup) : ∃ r, ∀ i, i ∈ members r ↔ treeWord i ∈ A := by
  classical
  let P := Finset.univ.filter (fun i : Fin 128 => treeWord i ∈ A)
  have hP (i : Fin 128) : i ∈ P ↔ treeWord i ∈ A := by simp [P]
  let Q := Finset.univ.filter (fun r : Fin 241 => members r ⊆ P)
  have h0 : (0 : Fin 241) ∈ Q := by
    simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i hi
    have he : i = 0 := by simpa only [members_zero,Finset.mem_singleton] using hi
    subst i
    exact (hP 0).mpr A.one_mem
  obtain ⟨r,hr,hm⟩ := Q.exists_max_image (fun r => (members r).card) ⟨0,h0⟩
  have hrP : members r ⊆ P := (Finset.mem_filter.mp hr).2
  have he : members r = P := by
    apply Finset.Subset.antisymm hrP
    intro i hi
    obtain ⟨a,ha⟩ := involution_cover i (elemPow_eq_one_of_isElementaryAbelian _ ((hP i).mp hi))
    have hc (b : Fin 128) (hb : b ∈ members r) :
        multiply (involutions a) b = multiply b (involutions a) := by
      obtain ⟨c,hc⟩ := involution_cover b (elemPow_eq_one_of_isElementaryAbelian _ ((hP b).mp (hrP hb)))
      apply treeWord_injective
      rw [←hc,multiply_correct,multiply_correct,hc,ha]
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm
        ⟨_,(hP i).mp hi⟩ ⟨_,(hP b).mp (hrP hb)⟩)
    obtain ⟨hle,hin,hgen⟩ := extensions r a hc
    have hn : members (next r a) ⊆ P := by
      intro k hk
      rcases hgen k hk with hk | ⟨b,hb,he⟩
      · exact hrP hk
      · obtain ⟨c,hc⟩ := involution_cover b (elemPow_eq_one_of_isElementaryAbelian _ ((hP b).mp (hrP hb)))
        apply (hP k).mpr
        rw [he,←hc,multiply_correct,hc,ha]
        exact A.mul_mem ((hP i).mp hi) ((hP b).mp (hrP hb))
    have hcard := hm (next r a) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    have he := Finset.eq_of_subset_of_card_le hle hcard
    exact ha ▸ he.symm ▸ hin
  refine ⟨r,?_⟩
  intro i
  rw [he]
  exact hP i

private theorem card_indices (B : Subgroup S) (hB : B ≤ treeGroup)
    (P : Finset (Fin 128)) (hP : ∀ i, i ∈ P ↔ treeWord i ∈ B) : Nat.card B = P.card := by
  let f : P → B := fun i => ⟨treeWord i.val,(hP i.val).mp i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Subtype.ext (treeWord_injective (congrArg Subtype.val h))
    · intro b
      obtain ⟨i,hi⟩ := (mem_treeGroup b.val).mp (hB b.property)
      exact ⟨⟨i,(hP i).mpr (hi.symm ▸ b.property)⟩,Subtype.ext hi⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_eq_fintype_card]

/-- The genuine index-eight configuration, including strict growth of all
three fixed spaces. -/
@[expose] def ThreeExtensions (A : Subgroup S) : Prop :=
  ∃ D ≤ A, D.relIndex A = 8 ∧ ∃ E : Fin 3 → Subgroup S,
    Function.Injective E ∧ ∀ i, D ≤ E i ∧ E i ≤ A ∧ D.relIndex (E i) = 2 ∧
      fixedSpace ρ A < fixedSpace ρ (E i)

private theorem tree_three_extensions (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hA : A ≤ treeGroup) (hne : A ≠ ⊥)
    (hno : ∀ v : N, (A ⊓ MulAction.stabilizer S v).relIndex A ≠ 2) :
    ThreeExtensions A := by
  classical
  obtain ⟨r,hr⟩ := catalogue A hA
  have hcard := card_indices A hA (members r) hr
  have hs (v : core (Fin 8)) : Nat.card (A ⊓ MulAction.stabilizer S (coreToNatural (Fin 8) v) : Subgroup S) =
      (fixed r v).card := by
    apply card_indices _ (inf_le_left.trans hA)
    intro i
    simp only [fixed,Finset.mem_filter,hr,fixes_iff]
    rfl
  obtain rfl | ⟨j,rfl⟩ | hbad := obstructions r
  · apply (hne ?_).elim
    apply le_bot_iff.mp
    intro a ha
    obtain ⟨i,rfl⟩ := (mem_treeGroup a).mp (hA ha)
    have he : i = 0 := by simpa only [members_zero,Finset.mem_singleton] using (hr i).mpr ha
    subst i
    exact one_mem _
  · let v : Fin 3 → N := fun i => coreToNatural (Fin 8) (vectors j i)
    let E : Fin 3 → Subgroup S := fun i => A ⊓ MulAction.stabilizer S (v i)
    let D : Subgroup S := ⨅ i, E i
    have hDE (i) : D ≤ E i := iInf_le _ i
    have hDA : D ≤ A := (hDE 0).trans inf_le_left
    have hD : Nat.card D = (common j).card := by
      apply card_indices D (hDA.trans hA)
      intro a
      simp only [common,Finset.mem_filter,hr,fixes_iff, D,E,mem_iInf,mem_inf,
        MulAction.mem_stabilizer_iff]
      change (treeWord a ∈ A ∧ ∀ i, ρ (treeWord a) (v i) = v i) ↔
        ∀ i, treeWord a ∈ A ∧ ρ (treeWord a) (v i) = v i
      exact ⟨fun h i => ⟨h.1,h.2 i⟩,fun h => ⟨(h 0).1,fun i => (h i).2⟩⟩
    obtain ⟨h8,hpos,hinj,h2⟩ := triples j
    have hdpos : 0 < Nat.card D := hD.symm ▸ hpos
    have hindex : D.relIndex A = 8 := by
      have hh := relIndex_mul_card_of_le hDA
      rw [hcard,h8,←hD] at hh
      exact Nat.eq_of_mul_eq_mul_right hdpos hh
    refine ⟨D,hDA,hindex,E,?_,?_⟩
    · intro i k hik
      apply hinj
      ext a
      simp only [fixed,Finset.mem_filter,hr,fixes_iff]
      change treeWord a ∈ E i ↔ treeWord a ∈ E k
      rw [hik]
    · intro i
      have he : Nat.card (E i) = 2 * Nat.card D := (hs _).trans ((h2 i).trans (congrArg (2*·) hD.symm))
      have hed : D.relIndex (E i) = 2 :=
        Nat.eq_of_mul_eq_mul_right hdpos ((relIndex_mul_card_of_le (hDE i)).trans he)
      refine ⟨hDE i,inf_le_left,hed,?_⟩
      apply lt_of_le_of_ne
      · intro w hw a
        exact hw ⟨a.val,a.property.1⟩
      · intro hh
        have hv : v i ∈ fixedSpace ρ (E i) := fun a => a.property.2
        have hvA : v i ∈ fixedSpace ρ A := hh.symm ▸ hv
        have heq : E i = A := by
          apply le_antisymm inf_le_left
          intro a ha
          exact ⟨ha,hvA ⟨a,ha⟩⟩
        have hm := relIndex_mul_relIndex D (E i) A (hDE i) inf_le_left
        rw [hed,hindex,heq,relIndex_self] at hm
        norm_num at hm
  · let B := A ⊓ MulAction.stabilizer S (coreToNatural (Fin 8) (badVector r))
    have hi : B.relIndex A = 2 := by
      have hh := relIndex_mul_card_of_le (show B ≤ A from inf_le_left)
      rw [hs,hcard,hbad.1] at hh
      exact Nat.eq_of_mul_eq_mul_right (by omega) hh
    exact (hno _ hi).elim


private theorem action_conj (g a : S) (v : N) :
    ρ (MulAut.conj g a) (ρ g v) = ρ g (ρ a v) := by
  have h : MulAut.conj g a * g = g * a := by simp [MulAut.conj_apply,mul_assoc]
  simpa only [map_mul,Module.End.mul_apply] using congrArg (fun p => ρ p v) h

private theorem act_inv (g : S) (v : N) : ρ g⁻¹ (ρ g v) = v := by
  rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]

private theorem fixed_conj (g : S) (A : Subgroup S) (v : N) :
    ρ g v ∈ fixedSpace ρ (A.map (MulAut.conj g).toMonoidHom) ↔ v ∈ fixedSpace ρ A := by
  constructor
  · intro h a
    have hh := h ⟨_,mem_map_of_mem _ a.property⟩
    change ρ (MulAut.conj g a.val) (ρ g v) = ρ g v at hh
    rw [action_conj] at hh
    change ρ a.val v = v
    simpa only [act_inv] using congrArg (ρ g⁻¹) hh
  · intro h a
    obtain ⟨b,hb,hba⟩ := a.property
    change ρ a.val (ρ g v) = ρ g v
    rw [←hba]
    change ρ (MulAut.conj g b) (ρ g v) = ρ g v
    rw [action_conj]
    exact congrArg (ρ g) (h ⟨b,hb⟩)

private theorem stabilizer_conj (g : S) (A : Subgroup S) (v : N) :
    (A ⊓ MulAction.stabilizer S v).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊓ MulAction.stabilizer S (ρ g v) := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨mem_map_of_mem _ hb.1,by change ρ (MulAut.conj g b) (ρ g v) = ρ g v; rw [action_conj]; exact congrArg (ρ g) hb.2⟩
  · rintro ⟨⟨b,hb,rfl⟩,hf⟩
    refine ⟨b,⟨hb,?_⟩,rfl⟩
    change ρ (MulAut.conj g b) (ρ g v) = ρ g v at hf
    rw [action_conj] at hf
    change ρ b v = v
    simpa only [act_inv] using congrArg (ρ g⁻¹) hf

private theorem threeExtensions_conj (g : S) (A : Subgroup S) (h : ThreeExtensions A) :
    ThreeExtensions (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨D,hDA,hD,E,hE,hEs⟩ := h
  let f := (MulAut.conj g).toMonoidHom
  refine ⟨D.map f,map_mono hDA,?_,fun i => (E i).map f,?_,?_⟩
  · rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hD]
  · intro i k h
    exact hE ((Subgroup.map_injective (MulAut.conj g).injective) h)
  · intro i
    obtain ⟨hDE,hEA,hED,hfix⟩ := hEs i
    refine ⟨map_mono hDE,map_mono hEA,?_,?_⟩
    · rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hED]
    · apply lt_of_le_of_ne
      · intro v hv a
        exact hv ⟨a.val,map_mono hEA a.property⟩
      · intro he
        apply ne_of_lt hfix
        ext v
        rw [←fixed_conj g A v,←fixed_conj g (E i) v]
        exact Iff.of_eq (congrArg (fun U : Submodule (ZMod 2) N => ρ g v ∈ U) he)

/-- Every nontrivial elementary S8 actor whose vector stabilizers never have
index two has the source three-extension configuration. -/
theorem three_extensions (A : Subgroup S) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥)
    (hno : ∀ v : N, (A ⊓ MulAction.stabilizer S v).relIndex A ≠ 2) :
    ThreeExtensions A := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P treeSylow
  let f := (MulAut.conj g).toMonoidHom
  let B := A.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hP : (P : Subgroup S).map f = treeGroup := by
    change ((g • P : Sylow 2 S) : Subgroup S) = treeGroup
    rw [hg,treeSylow_coe]
  have hB : B ≤ treeGroup := hP ▸ map_mono hAP
  have hb : B ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective A (f := f) (MulAut.conj g).injective).mp h)
  have hn (v : N) : (B ⊓ MulAction.stabilizer S v).relIndex B ≠ 2 := by
    have hv : ρ g (ρ g⁻¹ v) = v := by simpa only [inv_inv] using act_inv g⁻¹ v
    rw [←hv,←stabilizer_conj,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hno _
  have h := threeExtensions_conj g⁻¹ B (tree_three_extensions B hB hb hn)
  have he : B.map (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [map_map]
    have hf : (MulAut.conj g⁻¹).toMonoidHom.comp f = MonoidHom.id S := by
      ext x
      simp [f,MulAut.conj_apply,mul_assoc]
    rw [hf,map_id]
  exact he ▸ h


/-- The fixed-space formulation used by E.3.8 and source 12.6.28(2). -/
theorem three_extensions_of_rigid (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hne : A ≠ ⊥)
    (hr : ∀ B ≤ A, Nat.log 2 (B.relIndex A) < 2 → fixedSpace ρ A = fixedSpace ρ B) :
    ThreeExtensions A := by
  apply three_extensions A hne
  intro v hi
  let B := A ⊓ MulAction.stabilizer S v
  have hf := hr B inf_le_left (by rw [hi]; decide)
  have hv : v ∈ fixedSpace ρ B := fun a => a.property.2
  have hvA : v ∈ fixedSpace ρ A := hf.symm ▸ hv
  have hb : B = A := le_antisymm inf_le_left (fun a ha => ⟨ha,hvA ⟨a,ha⟩⟩)
  change B.relIndex A = 2 at hi
  rw [hb,relIndex_self] at hi
  norm_num at hi


/-- The index-eight subgroup forces the full rank lower bound in12.6.28(2). -/
theorem ThreeExtensions.rank_lower {A : Subgroup S} (h : ThreeExtensions A) :
    3 ≤ rank A := by
  obtain ⟨D,hDA,hidx,_⟩ := h
  have hcard := relIndex_mul_card_of_le hDA
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hlarge : 8 ≤ Nat.card A := by rw [←hcard,hidx]; omega
  simpa only [rank,show Nat.log 2 8 = 3 from rfl] using Nat.log_mono_right (b := 2) hlarge
end BinaryPermutation.EightThreeExtensions
