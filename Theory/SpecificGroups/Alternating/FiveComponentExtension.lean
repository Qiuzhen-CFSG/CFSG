module
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Five-point coordinates for a normal C-component with a two-group supplement

A normal C-component with quotient A₅ maps to a normal simple subgroup of
H/O₂(H). Its two-group supplement and the trivial two-core of that quotient
make its centralizer trivial. Conjugation therefore embeds the quotient in
Aut(A₅) = S₅. The image contains the prescribed A₅, so it is A₅ or S₅.

The resulting map is defined on the original H, has kernel exactly O₂(H),
and agrees with the original component quotient marking on every element
of K. This does not assume a split extension or erase the component core.
If a two-subgroup has a unique maximal overgroup, its fixed point in the
five-point action identifies that overgroup with a point stabilizer of index
five. The source application is in Chapter14's Classification/Sieve/NormalFour.
Source: standard component and automorphism theory, used in
Aschbacher--Smith 14.3.6(1) and 14.6.20, printed pp.991,1037.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
variable {H : Type*} [Group H] [Finite H]

/-- The actual component marking extends to a faithful five-point action
of the two-core quotient, with alternating or symmetric image. -/
theorem cComponent_action
    (K P : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hP : IsPGroup 2 P) (hgen : K ⊔ P = ⊤)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ∃ f : H →* Equiv.Perm (Fin 5),
      f.ker = pCore 2 H ∧
      (f.range = alternatingGroup (Fin 5) ∨ f.range = ⊤) ∧
      ∀ k : K, f k = eK (QuotientGroup.mk' (pCore 2 K) k) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let D := K.map q
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let a := cComponentTwoCoreQuotientEquiv hK
  let j : D ≃* alternatingGroup (Fin 5) := a.symm.trans eK
  let : D.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup D := j.isSimpleGroup
  let : Group.IsPerfect D := (hK.map_quotient (pCore 2 H)).perfect
  have hgenq : D ⊔ P.map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot := isPGroup_quotient_of_sup_eq_top D (P.map q) (hP.map q) hgenq
  have hc : centralizer (D : Set (H ⧸ pCore 2 H)) = ⊥ :=
    Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient D
      (Group.IsPerfect.not_isMulCommutative D) hquot (pCore_quotient_pCore_eq_bot (G := H) 2)
  let b := action D j
  have hb : Function.Injective b := action_injective D j hc
  let f := b.comp q
  have hfk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ hb,QuotientGroup.ker_mk']
  have hfK (k : K) : f k = eK (QuotientGroup.mk' (pCore 2 K) k) := by
    have hh := action_on_subgroup D j (a (QuotientGroup.mk' (pCore 2 K) k))
    change b (q k) = (eK (a.symm (a (QuotientGroup.mk' (pCore 2 K) k)))).val at hh
    change b (q k) = _
    simpa only [a.symm_apply_apply] using hh
  have hA : alternatingGroup (Fin 5) ≤ f.range := by
    intro x hx
    obtain ⟨k,hk⟩ := eK.surjective ⟨x,hx⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) k
    exact ⟨l,(hfK l).trans (congrArg Subtype.val hk)⟩
  refine ⟨f,hfk,?_,hfK⟩
  have hd : f.range.index ∣ 2 :=
    (alternatingGroup.index_eq_two (α := Fin 5)) ▸ index_dvd_of_le hA
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact Or.inr (Subgroup.index_eq_one.mp he)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two he)

/-- In a five-point action containing A₅, the unique maximal overgroup of a
 two-subgroup is the preimage of a point stabilizer and has index five. -/
theorem point_stabilizer_of_unique_maximal
    (f : H →* Equiv.Perm (Fin 5)) (hA : alternatingGroup (Fin 5) ≤ f.range)
    (P B : Subgroup H) (hP : IsPGroup 2 P) (hB : B ≠ ⊤)
    (hmax : ∀ D : Subgroup H, P ≤ D → D ≠ ⊤ → D ≤ B) :
    ∃ i : Fin 5, B = (stabilizer (Equiv.Perm (Fin 5)) i).comap f ∧ B.index = 5 := by
  let : MulAction H (Fin 5) := MulAction.compHom (Fin 5) f
  let : IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  let : IsPretransitive H (Fin 5) := ⟨fun i j => by
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) i j
    obtain ⟨g,hg⟩ := hA a.property
    exact ⟨g,by change f g i = j; rw [hg]; exact ha⟩⟩
  obtain ⟨i,hi⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  let D := stabilizer H i
  have hindex : D.index = 5 := by
    simpa only [Nat.card_fin] using index_stabilizer_of_transitive H i
  have hD : IsCoatom D := by
    refine ⟨?_,?_⟩
    · intro h
      simp [h] at hindex
    · intro E hE
      have hd := index_dvd_of_le hE.le
      rw [hindex] at hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
      · exact index_eq_one.mp h
      · have := index_strictAnti hE
        omega
  have hPD : P ≤ D := by
    intro p hp
    exact hi ⟨p,hp⟩
  have heq : B = D := (hD.le_iff.mp (hmax D hPD hD.ne_top)).resolve_left hB
  refine ⟨i,heq,heq ▸ hindex⟩
end Theory.SpecificGroups.Alternating.FiveExtensionAction
