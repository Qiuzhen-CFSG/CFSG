module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.Inheritance
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleReduction
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The actual diagonal central involution in the counterexample span

The two original commutator subgroups Eᵢ=[Uᵢ,S] form a nontrivial
T-invariant elementary subgroup. The residual section has index two and
Sylow subgroup T₁, so the two outside elements x and t have product
x t⁻¹ in that section. Commutator transport puts E₂ in the literal
conjugate span of U₁. Its central intersection therefore supplies the
required involution in V∩Ω₁Z(T), rather than assuming that witness.

Source: Aschbacher–Smith, C.5.10, printed p.161.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylow_intersection (T : Sylow 2 G) (T₁ N : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G))
    (hs : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = T₁) :
    (T : Subgroup G) ⊓ N = T₁ := by
  obtain ⟨P,hP⟩ := hs
  have hPA : (P : Subgroup N) ≤ (T : Subgroup G).subgroupOf N := by
    intro p hp
    exact hT₁T (hP ▸ mem_map_of_mem N.subtype hp)
  have he := P.is_maximal' (T.isPGroup'.comap_subtype (K := N)) hPA
  change (T : Subgroup G).subgroupOf N = (P : Subgroup N) at he
  rw [← subgroupOf_map_subtype,he,hP]

omit [Finite G] in
private theorem commutator_pair_normalizes (T S U₁ U₂ : Subgroup G)
    (hTS : T ≤ normalizer (S : Set G))
    (hpair : ∀ g ∈ T, U₁.conjBy g = U₁ ∨ U₁.conjBy g = U₂)
    (t : G) (ht : t ∈ T) (hUt : U₁.conjBy t = U₂) :
    T ≤ normalizer ((⁅U₁,S⁆ ⊔ ⁅U₂,S⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg z hz
  have hs : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp (hTS hg)
  have hsecond : U₂.conjBy g = U₁ ∨ U₂.conjBy g = U₂ := by
    have he : U₂.conjBy g = U₁.conjBy (g*t) := by rw [← hUt,conjBy_conjBy]
    rw [he]
    exact hpair (g*t) (T.mul_mem hg ht)
  have hm : (⁅U₁,S⁆ ⊔ ⁅U₂,S⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      ⁅U₁,S⁆ ⊔ ⁅U₂,S⁆ := by
    rw [Subgroup.map_sup,map_commutator,map_commutator,hs]
    change ⁅U₁.conjBy g,S⁆ ⊔ ⁅U₂.conjBy g,S⁆ ≤ _
    apply sup_le
    · rcases hpair g hg with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
    · rcases hsecond with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hz)

theorem span_central_witness (T : Sylow 2 G) (T₁ S U₁ U₂ : Subgroup G)
    (hT₁T : T₁ ≤ (T : Subgroup G)) (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hU₁T₁ : U₁ ≤ T₁) (hU₂T₁ : U₂ ≤ T₁)
    (hSU : S ≤ normalizer (U₁ : Set G))
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hpair : ∀ g ∈ (T : Subgroup G), U₁.conjBy g = U₁ ∨ U₁.conjBy g = U₂)
    (hU : IsElementaryAbelian 2 (U₁ ⊔ U₂ : Subgroup G))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hUt : U₁.conjBy t = U₂)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hnc : ¬ U₁.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U₁ : Set G))
    (hcomm : ⁅U₁,S⁆ = ⁅U₁,U₁.map (MulAut.conj x⁻¹).toMonoidHom⁆)
    (hv : conjugateSpanBy U₁ (T₁ ⊔ (pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype) ≤ centralizer (U₁ : Set G)) :
    let V := conjugateSpanBy U₁ (T₁ ⊔ (pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype)
    V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  let Y := normalizer (T₁ : Set G)
  let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
  let V := conjugateSpanBy U₁ N
  let E₁ := ⁅U₁,S⁆
  let E₂ := ⁅U₂,S⁆
  have hNV : N ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hUV : U₁ ≤ V := le_conjugateSpanBy _ _
  have hTn : (T₁.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hhalf
  have hTY : (T : Subgroup G) ≤ Y := (normal_subgroupOf_iff_le_normalizer hT₁T).mp hTn
  obtain ⟨hi,hs⟩ := CounterexampleReduction.normalizer_residual_section T T₁ hT₁T hhalf
  have hxout : x ∉ N := by
    intro hxN
    apply hnc
    exact ((map_mono hUV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hNV (N.inv_mem hxN)))).trans hv
  have htN : t ∉ N := by
    intro htN
    exact htout ((sylow_intersection T T₁ N hT₁T hs) ▸ (show t ∈ (T : Subgroup G) ⊓ N from ⟨ht,htN⟩))
  have hn : x*t⁻¹ ∈ N := (mul_mem_iff_of_index_two hi
    (a := (⟨x,hx⟩ : Y)) (b := (⟨t⁻¹,Y.inv_mem (hTY ht)⟩ : Y))).mpr
      (iff_of_false hxout (fun hh => htN (by simpa using N.inv_mem hh)))
  have hconj : U₁.map (MulAut.conj (x*t⁻¹)⁻¹).toMonoidHom ≤ V :=
    (map_mono hUV).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hNV (N.inv_mem hn)))
  have hE₁U : E₁ ≤ U₁ := le_normalizer_iff_commutator_le_left.mp hSU
  have hEt : E₁.map (MulAut.conj t).toMonoidHom = E₂ := by
    change (⁅U₁,S⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅U₂,S⁆
    have hs : S.map (MulAut.conj t).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp (hTS ht)
    rw [map_commutator,hs]
    exact congrArg (fun A : Subgroup G => ⁅A,S⁆) hUt
  have hE₂U : E₂ ≤ U₂ := by
    rw [← hEt,← hUt]
    exact map_mono hE₁U
  have hE₂V : E₂ ≤ V := by
    rw [← hEt]
    change (⁅U₁,S⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom ≤ V
    rw [hcomm,map_commutator]
    change ⁅U₁.conjBy t,(U₁.conjBy x⁻¹).conjBy t⁆ ≤ V
    rw [hUt,conjBy_conjBy]
    have he : t*x⁻¹ = (x*t⁻¹)⁻¹ := by group
    rw [he]
    exact (commutator_mono le_rfl hconj).trans
      (le_normalizer_iff_commutator_le_right.mp (hU₂T₁.trans (le_sup_left.trans hNV)))
  have hEne : E₁ ⊔ E₂ ≠ ⊥ := by
    intro he
    have hh : E₁ = ⊥ := bot_unique (he ▸ (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left))
    apply hnc
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hcomm.symm.trans hh))
  have hEU : E₁ ⊔ E₂ ≤ U₁ ⊔ U₂ := sup_le_sup hE₁U hE₂U
  have hElem : IsElementaryAbelian 2 (E₁ ⊔ E₂ : Subgroup G) := by
    let := hU
    exact IsElementaryAbelian.of_le hEU
  exact central_witness (T : Subgroup G) (E₁ ⊔ E₂) V T.isPGroup'
    (hEU.trans (sup_le (hU₁T₁.trans hT₁T) (hU₂T₁.trans hT₁T)))
    (commutator_pair_normalizes _ S U₁ U₂ hTS hpair t ht hUt) hEne hElem
    (sup_le (hE₁U.trans hUV) hE₂V)
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
