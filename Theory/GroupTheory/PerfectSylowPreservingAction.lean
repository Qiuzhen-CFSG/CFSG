module
public import FeitThompson.FinalTheorem
public import Theory.GroupTheory.SylowOuterAutomorphisms
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Perfect actions preserving a Sylow two-subgroup

The normalizer of a Sylow two-subgroup is soluble: its normal Sylow is
nilpotent and its odd-order quotient is soluble by Feit--Thompson. If the
outer automorphism group is soluble, the full Sylow stabilizer is therefore
soluble as well. A perfect actor preserving that Sylow acts trivially.

The subgroup application retains the literal commutator and embedded two-core.
It supplies the action contradiction in Aschbacher--Smith C.4.4, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

theorem Sylow.normalizer_isSolvable_two (P : Sylow 2 G) :
    Group.IsSolvable (normalizer (P : Set G)) := by
  let N := normalizer (P : Set G)
  let S : Sylow 2 N := P.subtype (P : Subgroup G).le_normalizer
  let : (S : Subgroup N).Normal := normal_in_normalizer
  let : Group.IsNilpotent (S : Subgroup N) := S.isPGroup'.isNilpotent
  have ho : Odd (Nat.card (N ⧸ (S : Subgroup N))) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using S.not_dvd_index)
  let : Group.IsSolvable (N ⧸ (S : Subgroup N)) := odd_order_theorem _ ho
  exact Group.isSolvable_of_ker_le_range (S : Subgroup N).subtype
    (QuotientGroup.mk' (S : Subgroup N)) (by simp)

theorem MulAut.sylow_stabilizer_isSolvable (P : Sylow 2 G)
    [Group.IsSolvable (MulAut.Outer G)] :
    Group.IsSolvable (MulAction.stabilizer (MulAut G) (P : Subgroup G)) := by
  let N := normalizer (P : Set G)
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let : Group.IsSolvable N := P.normalizer_isSolvable_two
  let f : N →* H := ((MulAut.conj : G →* MulAut G).comp N.subtype).codRestrict H (by
    intro g
    exact mem_normalizer_iff_map_conj_eq.mp g.property)
  let q : H →* MulAut.Outer G :=
    (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp H.subtype
  apply Group.isSolvable_of_ker_le_range f q
  intro a ha
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp ha
  have hn : g ∈ N := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change MulAut.conj g • (P : Subgroup G) = (P : Subgroup G)
    rw [hg]
    exact a.property
  exact ⟨⟨g,hn⟩,Subtype.ext hg⟩

theorem MonoidHom.perfect_action_eq_one_of_preserves_sylow
    {A : Type*} [Group A] [Group.IsPerfect A]
    (a : A →* MulAut G) (P : Sylow 2 G)
    [Group.IsSolvable (MulAut.Outer G)]
    (hP : ∀ x : A, (P : Subgroup G).map (a x).toMonoidHom = (P : Subgroup G)) :
    ∀ x : A, a x = 1 := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let : Group.IsSolvable H := MulAut.sylow_stabilizer_isSolvable P
  let f : A →* H := a.codRestrict H hP
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro x
  exact congrArg (fun z : f.range => (z : H).val)
    (hs.elim (⟨f x,⟨x,rfl⟩⟩ : f.range) 1)

open scoped commutatorElement

theorem Subgroup.commutator_le_core_of_perfect_sylow_preserving
    (A K R : Subgroup G) [Group.IsPerfect A]
    (hAK : A ≤ normalizer (K : Set G))
    (hAR : A ≤ normalizer (R : Set G))
    (T : Sylow 2 K) (hT : (T : Subgroup K).map K.subtype = R ⊓ K)
    [Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K))] :
    ⁅A,K⁆ ≤ K.pCoreIn 2 := by
  let α : A →* MulAut K := K.normalizerMonoidHom.comp (inclusion hAK)
  let f : A →* MulAut (K ⧸ pCore 2 K) := (quotientAut (pCore 2 K)).comp α
  let P : Sylow 2 (K ⧸ pCore 2 K) := T.mapSurjective (QuotientGroup.mk'_surjective _)
  have hα (x : A) {k : K} (hk : k ∈ T) : α x k ∈ T := by
    have hkR : (k : G) ∈ R := (hT ▸ show (k : G) ∈ (T : Subgroup K).map K.subtype from
      ⟨k,hk,rfl⟩).1
    have hm : ((α x k : K) : G) ∈ (T : Subgroup K).map K.subtype := by
      rw [hT]
      refine ⟨?_,(α x k).property⟩
      exact (mem_normalizer_iff.mp (hAR x.property) (k : G)).mp hkR
    obtain ⟨l,hl,he⟩ := hm
    exact (Subtype.ext he : l = α x k) ▸ hl
  have hP (x : A) : (P : Subgroup (K ⧸ pCore 2 K)).map (f x).toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro q ⟨z,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨α x k,hα x hk,quotientAut_apply_mk _ _ _ |>.symm⟩
    · exact le_of_eq (Subgroup.card_map_of_injective (f x).injective).symm
  have hf := f.perfect_action_eq_one_of_preserves_sylow P hP
  apply commutator_le.mpr
  intro a ha k hk
  let a' : A := ⟨a,ha⟩
  let k' : K := ⟨k,hk⟩
  have he : QuotientGroup.mk' (pCore 2 K) (α a' k') =
      QuotientGroup.mk' (pCore 2 K) k' := by
    have ht := congrArg (fun t : MulAut (K ⧸ pCore 2 K) =>
      t (QuotientGroup.mk' (pCore 2 K) k')) (hf a')
    simpa only [f, MonoidHom.comp_apply, quotientAut_apply_mk, MulAut.one_apply] using ht
  have hc : α a' k' / k' ∈ pCore 2 K := QuotientGroup.eq_iff_div_mem.mp he
  change _ ∈ (pCore 2 K).map K.subtype
  refine ⟨α a' k' / k',hc,?_⟩
  change (a * k * a⁻¹) / k = ⁅a,k⁆
  simp only [div_eq_mul_inv, commutatorElement_def]
