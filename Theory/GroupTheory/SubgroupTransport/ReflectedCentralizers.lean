module
public import Theory.GroupTheory.SubgroupTransport.PointCovering

/-!
# Reflected centralizers in the right Sylow interval

Reflection exchanges the original Sylows. Applying the literal partial
isomorphism afterwards returns to the same right Sylow and supplies its
left-interval centralizer. This keeps the original depth and conjugator.

Source: Niles, *Pushing-up in finite groups* (1979), the symmetric use
of Lemma 5.2 in Lemmas 5.3--5.4, pp.49--51.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Relative centralizers transport under the literal subgroup isomorphism. -/
theorem image_relative_centralizer (φ : S ≃* T) (B : Subgroup G) (hB : B ≤ S) :
    image φ (S ⊓ centralizer (B : Set G)) = T ⊓ centralizer (image φ B : Set G) := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨(φ a).property,(centralizes_iff φ B hB a).mp ha.2⟩
  · intro x hx
    let a := φ.symm ⟨x,hx.1⟩
    have ha : (a : G) ∈ centralizer (B : Set G) := by
      apply (centralizes_iff φ B hB a).mpr
      simpa only [a,φ.apply_symm_apply] using (show x ∈ centralizer (image φ B : Set G) from hx.2)
    refine ⟨a,⟨a.property,ha⟩,?_⟩
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨x,hx.1⟩)

/-- Short elementary intervals remain short under reflection, including
cells below the singleton diagonal. -/
theorem intervalDiagram_short_symm (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b)) :
    ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ.symm (3*v) a b) := by
  intro a b hb hlen
  by_cases ha : a ≤ 3*v
  · rw [intervalDiagram_symm φ _ _ _ ha]
    exact hshort _ _ (by omega) (by omega)
  · let A := intervalDiagram φ.symm (3*v) (3*v) b
    have hA : IsElementaryAbelian 2 A := by
      let e : A ≃* intervalDiagram φ (3*v) (3*v-b) 0 :=
        MulEquiv.subgroupCongr (by
          dsimp only [A]
          rw [intervalDiagram_symm φ (3*v) (3*v) b le_rfl,Nat.sub_self])
      let _ := hshort (3*v-b) 0 (by omega) (by omega)
      exact IsElementaryAbelian.of_injective (p := 2) e.toMonoidHom e.injective
    let _ := hA
    have hle : intervalDiagram φ.symm (3*v) a b ≤ A :=
      intervalDiagram_mono φ.symm (by omega) le_rfl
    exact IsElementaryAbelian.of_injective (p := 2) (inclusion hle) (inclusion_injective hle)

/-- Reflect the exact right-interval centralizer and transport it back
into T. The result is the other centralizer used in Niles 5.4. -/
theorem intervalDiagram_left_centralizer_eq (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G))
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hkernel : T ⊓ centralizer (intervalDiagram φ (3*v) v (2*v) : Set G) ≤ T ⊓ S)
    {k : ℕ} (hk : 2*v < k) (hkw : k < 3*v) :
    T ⊓ centralizer (intervalDiagram φ (3*v) (3*v-k+1) (2*v) : Set G) =
      intervalDiagram φ (3*v) 1 (5*v-k) := by
  have hgenR : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hgen b a (by omega)
  have hshortR := intervalDiagram_short_symm φ v hv hshort
  have hkR : T ⊓ centralizer (intervalDiagram φ.symm (3*v) v (2*v) : Set G) ≤ T ⊓ S := by
    simpa only [intervalDiagram,intervalCell_symm,show 3*v-2*v=v by omega] using hkernel
  have hpR := intervalDiagram_opposite_point_kernel φ.symm v hv hgenR hshortR hkR
  have he := intervalDiagram_right_centralizer_eq φ.symm v
    (by simpa only [inf_comm] using hT) (by simpa only [inf_comm] using hS)
    hgenR hshortR (fun r _ hr => hpR r hr) (j := k) (by omega) (by omega)
  rw [intervalDiagram_symm φ (3*v) (v+1) k (by omega),
    intervalDiagram_symm φ (3*v) (k-2*v+1) (3*v) (by omega),Nat.sub_self] at he
  have hB : intervalDiagram φ (3*v) (3*v-k) (3*v-(v+1)) ≤ S := by
    have hh : intervalDiagram φ (3*v) (3*v-k) (3*v-(v+1)) ≤ intervalCell φ 0 1 :=
      intervalCell_antitone φ (by omega) (by omega)
    exact hh.trans (intervalCell_initial_left φ).le
  have hm := congrArg (image φ) he
  rw [image_relative_centralizer φ _ hB,
    image_intervalDiagram φ (show 3*v-(v+1) < 3*v by omega),
    image_intervalDiagram φ (show 3*v-(k-2*v+1) < 3*v by omega)] at hm
  simpa only [Nat.zero_add,show 3*v-(v+1)+1=2*v by omega,
    show 3*v-(k-2*v+1)+1=5*v-k by omega] using hm
end Theory.GroupTheory.SubgroupTransport
