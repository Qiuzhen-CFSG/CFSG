module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.CentralCover.Data
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases

/-!
# A commutator equal to the marked central element

The retained degree-100 words u and v centralize x. Two words in u and v
have commutator exactly x, so the literal X inside C lies in the derived
subgroup. Every finite check uses small explicit permutation tables.
This certifies the nonabelian central-extension input in Aschbacher,
*Sporadic Groups* (1994), proof of 47.3(1), p.262.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.CentralCover
open Subgroup GeneratorPair Theory.GroupTheory
open scoped commutatorElement

theorem map_word {G H : Type*} [Group G] [Group H] {n : Nat}
    (f : G →* H) (g : Fin n → G) (w : List (Fin n)) :
    f (evalWord g w) = evalWord (fun i => f (g i)) w := by
  induction w with
  | nil => exact f.map_one
  | cons i w ih => exact (f.map_mul _ _).trans (congrArg (f (g i) * ·) ih)

def u : Carrier := evalWord ![a, b, b⁻¹] Data.uWord
def v : Carrier := evalWord ![a, b, b⁻¹] Data.vWord

private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (evalWord ![a, b, b⁻¹] w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  rw [map_word]
  congr 1
  funext i
  fin_cases i
  · exact generatorA_eq_table
  · exact generatorB_eq_table
  · exact (map_inv inclusion b).trans (congrArg Inv.inv
      (show inclusion b = tableB from generatorB_eq_table))

theorem inclusion_u : inclusion u = Data.u :=
  (inclusion_word Data.uWord).trans
    (by decide +kernel : evalWord ![tableA, tableB, tableB⁻¹] Data.uWord = Data.u)

theorem inclusion_v : inclusion v = Data.v :=
  (inclusion_word Data.vWord).trans
    (by decide +kernel : evalWord ![tableA, tableB, tableB⁻¹] Data.vWord = Data.v)

theorem inclusion_x : inclusion x = Data.x := by
  have h : inclusion x = (tableA * tableB * tableA * tableB⁻¹) ^ 4 := by
    simp only [x, map_pow, map_mul, map_inv,
      (show inclusion a = tableA from generatorA_eq_table),
      (show inclusion b = tableB from generatorB_eq_table)]
  exact h.trans (by decide +kernel)

theorem u_mem_C : u ∈ C := by
  apply (mem_C_iff u).mpr
  apply inclusion_injective
  simp only [map_mul, inclusion_u, inclusion_x]
  decide +kernel

theorem v_mem_C : v ∈ C := by
  apply (mem_C_iff v).mpr
  apply inclusion_injective
  simp only [map_mul, inclusion_v, inclusion_x]
  decide +kernel

def uC : C := ⟨u, u_mem_C⟩
def vC : C := ⟨v, v_mem_C⟩
def xC : C := ⟨x, X_le_C (mem_zpowers x)⟩

def letters : Fin 4 → C := ![uC, uC⁻¹, vC, vC⁻¹]
def p : C := evalWord letters Data.pWord
def q : C := evalWord letters Data.qWord

theorem inclusion_letters (i : Fin 4) :
    inclusion (C.subtype (letters i)) = ![Data.u, Data.u⁻¹, Data.v, Data.v⁻¹] i := by
  fin_cases i
  · exact inclusion_u
  · exact (map_inv inclusion u).trans (congrArg Inv.inv inclusion_u)
  · exact inclusion_v
  · exact (map_inv inclusion v).trans (congrArg Inv.inv inclusion_v)

private theorem inclusion_cword (w : List (Fin 4)) :
    inclusion (C.subtype (evalWord letters w)) =
      evalWord ![Data.u, Data.u⁻¹, Data.v, Data.v⁻¹] w := by
  rw [← MonoidHom.comp_apply, map_word]
  congr 1
  exact funext inclusion_letters

theorem inclusion_p : inclusion (p : Carrier) = Data.p :=
  (inclusion_cword Data.pWord).trans
    (by decide +kernel : evalWord ![Data.u, Data.u⁻¹, Data.v, Data.v⁻¹] Data.pWord = Data.p)

theorem inclusion_q : inclusion (q : Carrier) = Data.q :=
  (inclusion_cword Data.qWord).trans
    (by decide +kernel : evalWord ![Data.u, Data.u⁻¹, Data.v, Data.v⁻¹] Data.qWord = Data.q)

/-- An equality in the actual centralizer, not an abstract cover. -/
theorem commutator_p_q : ⁅p, q⁆ = xC := by
  apply Subtype.ext
  apply inclusion_injective
  change inclusion ((p : Carrier) * (q : Carrier) * (p : Carrier)⁻¹ * (q : Carrier)⁻¹) = inclusion x
  simp only [map_mul, map_inv, inclusion_p, inclusion_q, inclusion_x]
  decide +kernel

theorem xC_mem_commutator : xC ∈ commutator C := by
  rw [← commutator_p_q]
  exact commutator_mem_commutator (mem_top p) (mem_top q)

/-- The whole marked kernel is absorbed by the derived subgroup. -/
theorem XC_le_commutator : XC ≤ commutator C := by
  intro z hz
  obtain ⟨n, hn⟩ := hz
  have he : xC ^ n = z := Subtype.ext hn
  rw [← he]
  exact (commutator C).zpow_mem xC_mem_commutator n

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.CentralCover
