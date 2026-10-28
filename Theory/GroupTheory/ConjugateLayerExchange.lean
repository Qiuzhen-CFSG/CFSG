module
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Exchange of conjugate layers under an internal actor

If `g` belongs to `I` and `I` centralizes `A∨Aᵍ` modulo `B∨Bᵍ`, with
`B≤A`, then `A∨Bᵍ=Aᵍ∨B`. Both inclusions follow by writing conjugation
as a commutator followed by the original element, once with `g` and once
with `g⁻¹`. No equality of the original conjugate subgroups is assumed.

This is the penultimate equality in Aschbacher–Smith, Lemma 13.3.18,
printed p.895, with `A=V₅` and `B=V₃`.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem normalizes_join_of_commutators (I B C : Subgroup G)
    (hB : ⁅I,B⁆ ≤ B ⊔ C) (hC : ⁅I,C⁆ ≤ B ⊔ C) :
    I ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm (S : Subgroup G) (hS : S ≤ B ⊔ C) (hcom : ⁅I,S⁆ ≤ B ⊔ C) :
      S.map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rintro _ ⟨a,ha,rfl⟩
    change g*a*g⁻¹ ∈ B ⊔ C
    have he : g*a*g⁻¹ = ⁅g,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    rw [he]
    exact (B ⊔ C).mul_mem (hcom (commutator_mem_commutator hg ha)) (hS ha)
  have hmap : (B ⊔ C).map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rw [map_sup]
    exact sup_le (hm B le_sup_left hB) (hm C le_sup_right hC)
  exact hmap (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

private theorem commutator_join_left_le {A B C D : Subgroup G}
    (hn : A ⊔ B ≤ normalizer (D : Set G))
    (hA : ⁅A,C⁆ ≤ D) (hB : ⁅B,C⁆ ≤ D) : ⁅A ⊔ B,C⁆ ≤ D :=
  (commutator_mono (sup_le (le_commutatorPreimage le_sup_left hA)
    (le_commutatorPreimage le_sup_right hB)) le_rfl).trans
    (commutator_commutatorPreimage_le (A ⊔ B) C D hn)

/-- In an abelian pair, the two cross-displacement bounds make the generated
pair centralize the join of the smaller groups modulo the seed join. -/
theorem conjugate_pair_commutator_bound
    (V W A B X Y : Subgroup G)
    [IsMulCommutative V] [IsMulCommutative W]
    (hAV : A ≤ V) (hBW : B ≤ W) (hXA : X ≤ A) (hYB : Y ≤ B)
    (hVB : ⁅V,B⁆ ≤ X) (hWA : ⁅W,A⁆ ≤ Y) :
    ⁅V ⊔ W,A ⊔ B⁆ ≤ X ⊔ Y := by
  have hVA : ⁅V,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_centralizer V).trans (centralizer_le hAV))
  have hWB : ⁅W,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_centralizer W).trans (centralizer_le hBW))
  have hVX : ⁅V,X⁆ ≤ X ⊔ Y := (commutator_mono le_rfl hXA).trans (hVA.le.trans bot_le)
  have hWY : ⁅W,Y⁆ ≤ X ⊔ Y := (commutator_mono le_rfl hYB).trans (hWB.le.trans bot_le)
  have hVY : ⁅V,Y⁆ ≤ X ⊔ Y :=
    (commutator_mono le_rfl hYB).trans (hVB.trans le_sup_left)
  have hWX : ⁅W,X⁆ ≤ X ⊔ Y :=
    (commutator_mono le_rfl hXA).trans (hWA.trans le_sup_right)
  have hVN := normalizes_join_of_commutators V X Y hVX hVY
  have hWN := normalizes_join_of_commutators W X Y hWX hWY
  have hN : V ⊔ W ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := sup_le hVN hWN
  have hABN : A ⊔ B ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := sup_le (hAV.trans hVN) (hBW.trans hWN)
  have hVAB : ⁅V,A ⊔ B⁆ ≤ X ⊔ Y := by
    rw [commutator_comm]
    apply commutator_join_left_le hABN
    · rw [commutator_comm,hVA]; exact bot_le
    · rw [commutator_comm]; exact hVB.trans le_sup_left
  have hWAB : ⁅W,A ⊔ B⁆ ≤ X ⊔ Y := by
    rw [commutator_comm]
    apply commutator_join_left_le hABN
    · rw [commutator_comm]; exact hWA.trans le_sup_right
    · rw [commutator_comm,hWB]; exact bot_le
  exact commutator_join_left_le hN hVAB hWAB

/-- A conjugator acting trivially modulo the join of two conjugate layers
exchanges the overgroups of those layers. -/
theorem conjugate_layer_sup_exchange (A B I : Subgroup G) (g : G)
    (hBA : B ≤ A) (hg : g ∈ I)
    (hc : ⁅I, A ⊔ A.map (MulAut.conj g).toMonoidHom⁆ ≤
      B ⊔ B.map (MulAut.conj g).toMonoidHom) :
    A ⊔ B.map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊔ B := by
  let X := A ⊔ A.map (MulAut.conj g).toMonoidHom
  let D := B ⊔ B.map (MulAut.conj g).toMonoidHom
  have hmap (S : Subgroup G) (hS : S ≤ X) (k : G) (hk : k ∈ I) :
      S.map (MulAut.conj k).toMonoidHom ≤ S ⊔ D := by
    rintro _ ⟨a,ha,rfl⟩
    have he : k*a*k⁻¹ = ⁅k,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    change k*a*k⁻¹ ∈ S ⊔ D
    rw [he]
    exact (S ⊔ D).mul_mem
      (mem_sup_right (hc (commutator_mem_commutator hk (hS ha)))) (mem_sup_left ha)
  have hgA : A.map (MulAut.conj g).toMonoidHom ≤ A ⊔ B.map (MulAut.conj g).toMonoidHom :=
    (hmap A le_sup_left g hg).trans
      (sup_le le_sup_left (sup_le (hBA.trans le_sup_left) le_sup_right))
  have hinv : (A.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [map_map]
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hA : A ≤ A.map (MulAut.conj g).toMonoidHom ⊔ B := by
    have hm := hmap (A.map (MulAut.conj g).toMonoidHom) le_sup_right g⁻¹ (I.inv_mem hg)
    rw [hinv] at hm
    exact hm.trans
      (sup_le le_sup_left (sup_le le_sup_right ((map_mono hBA).trans le_sup_left)))
  exact le_antisymm (sup_le hA ((map_mono hBA).trans le_sup_left))
    (sup_le hgA (hBA.trans le_sup_left))

end Subgroup
