module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCover
public import Theory.Quasithin.CentralExtensionSL2Pair

/-!
# Higher unitary field reduction through odd central kernels

Two commuting faithful SL₂ subgroups in the actual unitary quotient force
the fixed field to be prime. The ordinary root centralizer obstruction then
leaves only degree four or the prime three. This reduction uses the original
group's quasithinness and its odd center.
Source: Aschbacher–Smith A.2.17 Case II, printed p.39.
-/

open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

public theorem unitary_higher_fieldExponent_eq_one_of_odd_center
    {n r e : ℕ} [Fact r.Prime] (hn : 4 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) : e = 1 := by
  obtain ⟨d,rfl⟩ : ∃ d, n = 2+(2+d) := ⟨n-4,by omega⟩
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  let : NeZero (2+d) := ⟨by omega⟩
  let : Finite (ProjGenLinGroup (Fin (2+(2+d))) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨f,c,hf,_,hc,hcomm,_,_,_⟩ :=
    ClassicalStructure.unitary_fundamental J hr2 (by omega) hcard hconj
  have hq : IsPrimePow (r^e) := (isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd J.conj J.conj_involutive hq hr.pow hcard hconj
  let b := (left J.conj J.conj_involutive (m := 2) (n := d)).comp a.symm.toMonoidHom
  let g := c.comp b
  have hg : Function.Injective g := hc.comp ((left_injective _ _).comp a.symm.injective)
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = r^e :=
    J.fixed_card_prime_power hq hcard hconj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hfixed)
  exact CentralExtension.fieldExponent_eq_one_of_commuting_sl2 hr2 he hfixed
    iso ho hqt f g hf hg (fun x y => hcomm x (b y))

public theorem unitary_higher_central_quotient_parameters
    {n r e : ℕ} [Fact r.Prime] (hn : 4 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (ho : Odd (Nat.card (center G))) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) :
    e = 1 ∧ (n = 4 ∨ r = 3) := by
  have he1 := unitary_higher_fieldExponent_eq_one_of_odd_center hn hr he ho hqt model
  refine ⟨he1,?_⟩
  subst e
  by_cases hr3 : r = 3
  · exact Or.inr hr3
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hrgt : 3 < r := by have := (Fact.out : r.Prime).two_le; omega
  have hr9 : r ≠ 9 := by intro hh; subst r; exact (by decide : ¬ Nat.Prime 9) Fact.out
  have hpar := unitary_central_quotient_parameters_of_ordinary_field (by omega) hr
    (by decide : 1 ≤ 1) (by simpa) (by simpa) hqt model
  exact Or.inl (by omega)
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
