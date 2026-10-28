module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Two cubic characters from complementary normal cubic subgroups

Let E=B×C have order nine in a finite group with trivial two-core, and
suppose a two-subgroup S supplements E. The action on the three cosets
of CS gives a second cubic character. Its kernel meets E in C, whereas
the supplied first character has kernel meeting E in B. The intersection
of both kernels embeds in the two-group quotient by E and is therefore
trivial. The pair consequently maps E onto A₃×A₃ and B onto 1×A₃.

The first character is preserved exactly. No factor exchange or independent
inverter is assumed by this construction. The original Cartan quotient
application supplies the normal cubic directions and later proves exchange.
Source application: Aschbacher–Smith, original 9.3.1, printed p.732.
-/
public noncomputable section
open Subgroup
namespace Theory.GroupTheory.CubicPairCharacters
local notation "S3" => Equiv.Perm (Fin 3)
local notation "A3" => alternatingGroup (Fin 3)
variable {X : Type*} [Group X] [Finite X]

private theorem cube_even (s : S3) (hs : s^3=1) : s ∈ A3 := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : ∀ s : S3, s^3=1 → Equiv.Perm.sign s = 1 := by decide +kernel
  exact h s hs

/-- A normal cubic complement gives a second degree-three action; together
with the first character it is faithful when the actual two-core is trivial. -/
theorem exists_second_character
    (E B C : Subgroup X) [E.Normal] [B.Normal] [C.Normal]
    (hE : Nat.card E = 9) (hB : Nat.card B = 3) (hC : Nat.card C = 3)
    (hd : Disjoint B C) (hBC : B ⊔ C = E)
    (S : Subgroup X) (hS : IsPGroup 2 S) (hgen : E ⊔ S = ⊤)
    (hcore : pCore 2 X = ⊥) (f : X →* S3) (hf : E ⊓ f.ker = B) :
    ∃ g : X →* S3, Function.Injective (f.prod g) ∧
      E.map (f.prod g) = (A3).prod A3 ∧
      B.map (f.prod g) = (⊥ : Subgroup S3).prod A3 ∧ C ≤ g.ker := by
  have hBE : B ≤ E := hBC ▸ le_sup_left
  have hCE : C ≤ E := hBC ▸ le_sup_right
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hE
  have hCp : IsPGroup 3 C := IsPGroup.of_card (n := 1) hC
  have hdES := hEp.disjoint_of_coprime hS (by decide : Nat.Coprime 3 2)
  have hdCS := hCp.disjoint_of_coprime hS (by decide : Nat.Coprime 3 2)
  let J := C ⊔ S
  have hX : Nat.card X = 9 * Nat.card S := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint E S
      (by rw [normalizer_eq_top]; exact le_top) hdES
    rwa [hgen,card_top,hE] at hh
  have hJ : Nat.card J = 3 * Nat.card S := by
    exact (card_sup_eq_mul_of_normalizes_of_disjoint C S
      (by rw [normalizer_eq_top]; exact le_top) hdCS).trans (by rw [hC])
  have hi : J.index = 3 := by
    have hh := J.card_mul_index
    rw [hJ,hX] at hh
    have hspos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  let a : X →* Equiv.Perm (X ⧸ J) := MulAction.toPermHom X (X ⧸ J)
  let e : (X ⧸ J) ≃ Fin 3 := (Finite.equivFin _).trans (finCongr hi)
  let g : X →* S3 := e.permCongrHom.toMonoidHom.comp a
  have hgker : g.ker = J.normalCore := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      ←J.normalCore_eq_ker]
  have hCg : C ≤ g.ker := by
    rw [hgker]
    exact normal_le_normalCore.mpr le_sup_left
  have hEJ : E ⊓ J = C := by
    apply le_antisymm
    · rintro x ⟨hxE,hxJ⟩
      obtain ⟨c,hc,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hxJ
      have hsE : s ∈ E := by
        have hh := E.mul_mem (E.inv_mem (hCE hc)) hxE
        simpa only [inv_mul_cancel_left] using hh
      have hs1 : s = 1 := disjoint_def.mp hdES hsE hs
      simpa only [hs1,mul_one] using hc
    · exact le_inf hCE le_sup_left
  have hEg : E ⊓ g.ker = C := by
    apply le_antisymm
    · rw [←hEJ,hgker]
      exact inf_le_inf_left _ J.normalCore_le
    · exact le_inf hCE hCg
  let k := f.prod g
  have hdEK : Disjoint E k.ker := by
    apply disjoint_def.mpr
    intro x hx hxk
    have hxf : f x = 1 := congrArg Prod.fst hxk
    have hxg : g x = 1 := congrArg Prod.snd hxk
    exact disjoint_def.mp hd (hf ▸ ⟨hx,hxf⟩) (hEg ▸ ⟨hx,hxg⟩)
  let π := QuotientGroup.mk' E
  have hπS : Function.Surjective (π.comp S.subtype) := by
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective E z
    have hx : x ∈ E ⊔ S := hgen.symm ▸ mem_top x
    obtain ⟨v,hv,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hx
    refine ⟨⟨s,hs⟩,?_⟩
    change π s = π (v*s)
    rw [map_mul,show π v = 1 from (QuotientGroup.eq_one_iff _).mpr hv,one_mul]
  have hquot : IsPGroup 2 (X ⧸ E) := hS.of_surjective (π.comp S.subtype) hπS
  have hπK : Function.Injective (π.comp k.ker.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hdEK ((QuotientGroup.eq_one_iff _).mp hx) x.property
  have hK : IsPGroup 2 k.ker := hquot.of_injective (π.comp k.ker.subtype) hπK
  have hkbot : k.ker = ⊥ := le_bot_iff.mp (hcore ▸ (show k.ker ≤ pCore 2 X from
    le_sSup ⟨inferInstance,hK⟩))
  have hk : Function.Injective k := (MonoidHom.ker_eq_bot_iff k).mp hkbot
  have hEimage : E.map k ≤ (A3).prod A3 := by
    rintro _ ⟨x,hx,rfl⟩
    have hx9 : x^9=1 := by
      simpa only [hE,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : E)))
    have cube_of_nine : ∀ s : S3, s^9=1 → s^3=1 := by decide +kernel
    exact ⟨cube_even _ (cube_of_nine _ (by change f x ^ 9 = 1; rw [←map_pow,hx9,map_one])),
      cube_even _ (cube_of_nine _ (by change g x ^ 9 = 1; rw [←map_pow,hx9,map_one]))⟩
  have hEpimage : E.map k = (A3).prod A3 := by
    apply eq_of_le_of_card_ge hEimage
    rw [card_map_of_injective hk,hE]
    have hc : Nat.card A3 = 3 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
    rw [Nat.card_congr (prodEquiv A3 A3).toEquiv,Nat.card_prod,hc]
  have hBimage : B.map k = (⊥ : Subgroup S3).prod A3 := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨b,hb,rfl⟩
      have hbf : f b = 1 := (hf.symm ▸ hb).2
      exact ⟨hbf,(hEimage (mem_map_of_mem k (hBE hb))).2⟩
    · rw [card_map_of_injective hk,hB]
      rw [Nat.card_congr (prodEquiv (⊥ : Subgroup S3) A3).toEquiv,
        Nat.card_prod,card_bot,one_mul,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
  exact ⟨g,hk,hEpimage,hBimage,hCg⟩

/-- Equal coordinate signs act on the entire cubic plane by the same scalar
power, either the identity or inversion. -/
theorem equal_signs_common_power (s t : S3) (h : Equiv.Perm.sign s = Equiv.Perm.sign t) :
    ∃ n : ℕ, ∀ c ∈ (A3).prod A3, (s,t)*c*(s,t)⁻¹=c^n := by
  have hpos : ∀ s c : S3, Equiv.Perm.sign s = 1 → Equiv.Perm.sign c = 1 →
      s*c*s⁻¹=c := by decide +kernel
  have hneg : ∀ s c : S3, Equiv.Perm.sign s = -1 → Equiv.Perm.sign c = 1 →
      s*c*s⁻¹=c^2 := by decide +kernel
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hs|hs
  · refine ⟨1,?_⟩
    intro c hc
    apply Prod.ext
    · change s*c.1*s⁻¹=c.1^1
      rw [pow_one]
      exact hpos _ _ hs (Equiv.Perm.mem_alternatingGroup.mp hc.1)
    · change t*c.2*t⁻¹=c.2^1
      rw [pow_one]
      exact hpos _ _ (h.symm.trans hs) (Equiv.Perm.mem_alternatingGroup.mp hc.2)
  · refine ⟨2,?_⟩
    intro c hc
    exact Prod.ext (hneg _ _ hs (Equiv.Perm.mem_alternatingGroup.mp hc.1))
      (hneg _ _ (h.symm.trans hs) (Equiv.Perm.mem_alternatingGroup.mp hc.2))

end Theory.GroupTheory.CubicPairCharacters
