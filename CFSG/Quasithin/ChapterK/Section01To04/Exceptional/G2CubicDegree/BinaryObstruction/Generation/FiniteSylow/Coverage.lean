module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.ModelInput

/-!
# The eight elementary eights in the binary G₂ Sylow subgroup

The six positive-root coordinates identify all 64 actual octonion elements.
The eight displayed coordinate ranges are subgroups of order at most eight.
An elementary eight has an element outside the four exceptional coordinates;
its commuting involutions lie in a union of two displayed subgroups. A subgroup
contained in such a union lies in one member, and cardinality gives equality.
All finite coordinate claims are checked by the kernel, using the existing
polynomial multiplication law rather than enumerating abstract subgroups.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. Root conventions are inherited from the ATLAS port;
Gerald Höhn and the ATLAS contributors, ATLAS Research and Attribution License
1.0 (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
abbrev G := Model (ZMod 2)
abbrev Params := Fin 6 → ZMod 2

def params (n : Fin 64) : Params := fun i => ((n.val >>> i.val) % 2 : ℕ)
def encode (t : Params) : Fin 64 := ⟨((t 0).val + 2*(t 1).val + 4*(t 2).val +
  8*(t 3).val + 16*(t 4).val + 32*(t 5).val) % 64, Nat.mod_lt _ (by decide)⟩

theorem params_encode (t : Params) : params (encode t) = t := by
  exact (by decide +kernel : ∀ t : Params, params (encode t) = t) t

def row (i : Fin 8) : Fin 8 → Fin 64 :=
  ![![0,1,4,5,16,17,20,21], ![0,1,2,3,4,5,6,7],
    ![0,1,8,9,16,17,24,25], ![0,1,2,3,32,33,34,35],
    ![0,1,10,11,20,21,30,31], ![0,1,2,3,44,45,46,47],
    ![0,1,6,7,24,25,30,31], ![0,1,2,3,8,9,10,11]] i

def element (n : Fin 64) : G := unipotentProduct (params n)

theorem element_zero : element 0 = 1 := unipotentProduct_zero

theorem element_surjective (g : G) (hg : g ∈ unipotent) : ∃ n, element n = g := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  exact ⟨encode t, congrArg unipotentProduct (params_encode t)⟩

theorem element_square (n : Fin 64) : element n * element n = 1 ↔
    unipotentProductParameters (params n) (params n) = 0 := by
  rw [element, unipotentProduct_mul, ← unipotentProduct_zero]
  exact unipotentProduct_injective.eq_iff

theorem element_commute (m n : Fin 64) : element m * element n = element n * element m ↔
    unipotentProductParameters (params m) (params n) =
      unipotentProductParameters (params n) (params m) := by
  rw [element, element, unipotentProduct_mul, unipotentProduct_mul]
  exact unipotentProduct_injective.eq_iff

private theorem row_square (i : Fin 8) : ∀ j,
    unipotentProductParameters (params (row i j)) (params (row i j)) = 0 := by
  fin_cases i <;> decide +kernel

private theorem row_mul (i : Fin 8) : ∀ j k, ∃ l,
    unipotentProductParameters (params (row i j)) (params (row i k)) = params (row i l) := by
  fin_cases i <;> decide +kernel

def candidate (i : Fin 8) : Subgroup G where
  carrier := Set.range (fun j => element (row i j))
  one_mem' := ⟨0, by change element (row i 0) = 1; rw [show row i 0 = 0 by fin_cases i <;> rfl, element_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨j,rfl⟩ ⟨k,rfl⟩
    obtain ⟨l,hl⟩ := row_mul i j k
    exact ⟨l, by simp only [element, unipotentProduct_mul]; exact congrArg unipotentProduct hl.symm⟩
  inv_mem' := by
    rintro _ ⟨j,rfl⟩
    exact ⟨j, (inv_eq_of_mul_eq_one_left ((element_square _).mpr (row_square i j))).symm⟩

theorem candidate_card_le (i : Fin 8) : Nat.card (candidate i) ≤ 8 := by
  let f : Fin 8 → candidate i := fun j => ⟨element (row i j), ⟨j,rfl⟩⟩
  have h := Nat.card_le_card_of_surjective f (by rintro ⟨x,j,rfl⟩; exact ⟨j,rfl⟩)
  simpa using h

-- Every nonexceptional involution has its involution centralizer covered by two rows.
private theorem centralizer_cover (x : Fin 64) :
    4 ≤ x.val → unipotentProductParameters (params x) (params x) = 0 →
    ∃ i j : Fin 8, ∀ y : Fin 64,
      unipotentProductParameters (params y) (params y) = 0 →
      unipotentProductParameters (params x) (params y) =
        unipotentProductParameters (params y) (params x) →
      (∃ k, row i k = y) ∨ (∃ k, row j k = y) := by
  fin_cases x <;> decide +kernel

theorem elementary_eight_coverage (E : Subgroup G) (hEU : E ≤ unipotent)
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 8) :
    ∃ i : Fin 8, E = candidate i := by
  let := hE
  have sq (g : G) (hg : g ∈ E) : g*g=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) g hg
  have ex : ∃ x : Fin 64, element x ∈ E ∧ 4 ≤ x.val := by
    by_contra! hn
    let f : E → Fin 4 := fun g =>
      ⟨(encode (unipotentParameters g.val)).val, by
        have he : element (encode (unipotentParameters g.val)) = g.val := by
          obtain ⟨n, hn⟩ := element_surjective g.val (hEU g.prop)
          rw [← hn]
          simp only [element, unipotentParameters_product, params_encode]
        have := hn _ (he.symm ▸ g.prop)
        omega⟩
    have hi : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have he (g : E) : element (encode (unipotentParameters g.val)) = g.val := by
        obtain ⟨n, hn⟩ := element_surjective g.val (hEU g.prop)
        rw [← hn]
        simp only [element, unipotentParameters_product, params_encode]
      rw [← he a, ← he b]
      apply congrArg element
      exact Fin.ext (congrArg (fun z : Fin 4 => z.val) hab)
    have := Nat.card_le_card_of_injective f hi
    simp only [hc, Nat.card_fin] at this
    omega
  obtain ⟨x,hx,hx4⟩ := ex
  obtain ⟨i,j,hij⟩ := centralizer_cover x hx4 ((element_square x).mp (sq _ hx))
  have hsub : (E : Set G) ⊆ (candidate i : Set G) ∪ candidate j := by
    intro g hg
    obtain ⟨y,rfl⟩ := element_surjective g (hEU hg)
    have hcomm : element x * element y = element y * element x :=
      congrArg Subtype.val (mul_comm (⟨element x,hx⟩ : E) ⟨element y,hg⟩)
    rcases hij y ((element_square y).mp (sq _ hg)) ((element_commute x y).mp hcomm) with h | h
    · obtain ⟨k,rfl⟩ := h; exact Or.inl ⟨k,rfl⟩
    · obtain ⟨k,rfl⟩ := h; exact Or.inr ⟨k,rfl⟩
  rcases SubgroupClass.subset_union.mp hsub with hi | hj
  · exact ⟨i, Subgroup.eq_of_le_of_card_ge hi (by simpa only [hc] using candidate_card_le i)⟩
  · exact ⟨j, Subgroup.eq_of_le_of_card_ge hj (by simpa only [hc] using candidate_card_le j)⟩
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
