module
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Six-point preimages in the ordinary A₇ action

The point stabilizer in S₇ is S₆ and in A₇ is A₆. Their two-cores are
trivial. A surjection with a two-group kernel therefore gives the actual
A₆/S₆ quotient of the point preimage by its intrinsic two-core. The same
seven-point action is transitive of prime degree, so the point preimage is
a literal maximal subgroup.

Source: the A₇ point-stabilizer step in C.1.29, printed p.134.
-/
public section
open Subgroup MulAction
namespace alternatingGroup.SevenComponent

noncomputable def symmetricPointEquiv (i : Fin 7) :
    stabilizer (Equiv.Perm (Fin 7)) i ≃* Equiv.Perm (Fin 6) := by
  let p := fun a : Fin 7 => a ≠ i
  let f : Equiv.Perm {a : Fin 7 // p a} →* stabilizer (Equiv.Perm (Fin 7)) i :=
    (Equiv.Perm.ofSubtype : Equiv.Perm {a : Fin 7 // p a} →* Equiv.Perm (Fin 7)).codRestrict _
      (fun g => Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp [p]))
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h), ?_⟩
    intro g
    have hg : g.val i = i := g.property
    have hpred (a : Fin 7) : p (g.val a) ↔ p a := by
      change g.val a ≠ i ↔ a ≠ i
      exact ⟨fun hn he => hn (he ▸ hg), fun hn he => hn (g.val.injective (he.trans hg.symm))⟩
    refine ⟨g.val.subtypePerm hpred, ?_⟩
    apply Subtype.ext
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro a ha hai
    exact ha (hai.symm ▸ hg)
  exact (MulEquiv.ofBijective f hf).symm.trans
    (Equiv.permCongrHom (finSuccAboveEquiv i).symm)

theorem symmetric_six_twoCore : pCore 2 (Equiv.Perm (Fin 6)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 6))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hdiv : 360 ∣ Nat.card (pCore 2 (Equiv.Perm (Fin 6))) := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 6))).exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 360) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

theorem alternating_six_twoCore : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := pCore 2 (alternatingGroup (Fin 6))) with he | he
  · exact he
  · have hc : Nat.card (pCore 2 (alternatingGroup (Fin 6))) = 360 := by
      rw [he, card_top, nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 6))).exists_card_eq
    have hthree : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 360)
    exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree))

theorem range_eq_alternating_or_top {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 7)) (hA : alternatingGroup (Fin 7) ≤ f.range) :
    f.range = alternatingGroup (Fin 7) ∨ f.range = ⊤ := by
  have hd : f.range.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 7)) ▸ index_dvd_of_le hA
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact Or.inr (Subgroup.index_eq_one.mp he)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two he)

private theorem point_preimage_coreQuotient
    {G A B α : Type*} [Group G] [Finite G] [Group A] [Finite A] [Group B] [Finite B]
    [MulAction A α] (f : G →* A) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (i : α)
    (e : stabilizer A i ≃* B) (hB : pCore 2 B = ⊥) :
    Nonempty (((stabilizer A i).comap f) ⧸ pCore 2 ((stabilizer A i).comap f) ≃* B) := by
  let P := (stabilizer A i).comap f
  let q := f.subgroupComap (stabilizer A i)
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hkq : q.ker = f.ker.subgroupOf P := by
    ext x
    change q x = 1 ↔ f (x : G) = 1
    exact Subtype.ext_iff
  let g := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp hq
  have hkg : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, hkq]
    exact hk.comap_subtype
  exact ⟨(g.pCoreQuotientEquiv hg hkg).trans
    ((QuotientGroup.quotientMulEquivOfEq hB).trans QuotientGroup.quotientBot)⟩

/-- The point preimage in a seven-letter A₇-extension has precisely an
A₆ or S₆ quotient by its own two-core. -/
theorem point_preimage_six_coreQuotient
    {G : Type*} [Group G] [Finite G] (f : G →* Equiv.Perm (Fin 7))
    (hk : IsPGroup 2 f.ker) (hA : alternatingGroup (Fin 7) ≤ f.range)
    (i : Fin 7) :
    Nonempty ((((stabilizer (Equiv.Perm (Fin 7)) i).comap f) ⧸
      pCore 2 ((stabilizer (Equiv.Perm (Fin 7)) i).comap f)) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((((stabilizer (Equiv.Perm (Fin 7)) i).comap f) ⧸
      pCore 2 ((stabilizer (Equiv.Perm (Fin 7)) i).comap f)) ≃* Equiv.Perm (Fin 6)) := by
  rcases range_eq_alternating_or_top f hA with he | he
  · let g := f.codRestrict (alternatingGroup (Fin 7)) (fun x => he ▸ (show f x ∈ f.range from ⟨x, rfl⟩))
    have hg : Function.Surjective g := by
      intro a
      obtain ⟨x, hx⟩ := hA a.property
      exact ⟨x, Subtype.ext hx⟩
    have hkg : IsPGroup 2 g.ker := by
      rwa [MonoidHom.ker_codRestrict]
    have hp : (stabilizer (alternatingGroup (Fin 7)) i).comap g =
        (stabilizer (Equiv.Perm (Fin 7)) i).comap f := by ext x; rfl
    have hh := point_preimage_coreQuotient g hg hkg i
      (AlternatingSix.SmallIndex.pointEquiv i) alternating_six_twoCore
    exact Or.inl (hp ▸ hh)
  · exact Or.inr (point_preimage_coreQuotient f (f.range_eq_top.mp he) hk i
      (symmetricPointEquiv i) symmetric_six_twoCore)

/-- The point preimage is maximal in the original group: its transitive
seven-point action has prime degree. -/
theorem point_preimage_isCoatom
    {G : Type*} [Group G] (f : G →* Equiv.Perm (Fin 7))
    (hA : alternatingGroup (Fin 7) ≤ f.range) (i : Fin 7) :
    IsCoatom ((stabilizer (Equiv.Perm (Fin 7)) i).comap f) := by
  let : MulAction G (Fin 7) := MulAction.compHom (Fin 7) f
  let : IsPretransitive (alternatingGroup (Fin 7)) (Fin 7) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 7) (by simp)
  let : IsPretransitive G (Fin 7) := ⟨fun i j => by
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) i j
    obtain ⟨g, hg⟩ := hA a.property
    exact ⟨g, by change f g i = j; rw [hg]; exact ha⟩⟩
  let : IsPreprimitive G (Fin 7) := IsPreprimitive.of_prime_card (by rw [Nat.card_fin]; decide)
  exact IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G i

end alternatingGroup.SevenComponent
