module

public import Stellmacher.Recognition.NormalEightSeparatedReturning

/-!
# Rigidity of separated conjugate fours

Separation makes the distinguished central involution fixed by the
normalizer of every conjugate four. A two-subgroup normalizing such a four
can therefore be transported into the original Sylow while identifying
the four with the original normal four. Returning-conjugate centralizer
control then shows that normalized conjugate fours commute. A common
nonidentity element first gives normalization, and the returning
intersection theorem subsequently gives equality.

Source: Janko–Thompson, Math. Z. 113 (1970), printed p.395, using the
normalizer argument of Lemma 5.1 on printed p.394.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedConjugateRigidity

open Subgroup NormalFourCentralOmegaTwo NormalEightSeparatedFusion
open NormalEightSeparatedTransport NormalEightSeparatedReturning

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_map_comp (W : Subgroup G) (g k : G) :
    (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      W.map (MulAut.conj (k * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- A two-subgroup normalizing a separated conjugate four transports into
the original Sylow with that four identified with the original four. -/
public theorem transport_normalizing_conjugate_four
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z)
    (g : G) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hBR : (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤ R)
    (hRN : R ≤ normalizer
      (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) : Set G)) :
    ∃ k : G, R.map (MulAut.conj k).toMonoidHom ≤ (S : Subgroup G) ∧
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj k).toMonoidHom = W.map (S : Subgroup G).subtype := by
  let W₀ := W.map (S : Subgroup G).subtype
  let B := W₀.map (MulAut.conj g).toMonoidHom
  let f := MulAut.conj g
  let x := f (z : G)
  have hxB : x ∈ B := mem_map_of_mem _ (mem_map_of_mem _ hzW)
  have hRC : R ≤ centralizer ({x} : Set G) := by
    intro r hr
    have hmem : (MulAut.conj r) x ∈ B :=
      (mem_normalizer_iff.mp (hRN hr) x).mp hxB
    obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := hmem
    change f (t : G) = (MulAut.conj r) x at he
    have hzt : IsConj (z : G) (t : G) := by
      apply isConj_iff.mpr
      refine ⟨g⁻¹ * r * g, ?_⟩
      apply f.injective
      rw [he]
      simp [f, x, MulAut.conj_apply, mul_assoc]
    have htEq := hsep t ht hzt
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    exact he.symm.trans (congrArg (fun a : S => f (a : G)) htEq)
  obtain ⟨k, hkS, hkz⟩ := S.transport_centralizing_two_subgroup z hzC x
    (isConj_iff.mpr ⟨g, rfl⟩).symm R hR hRC
  refine ⟨k, hkS, ?_⟩
  rw [conj_map_comp]
  refine conjugate_four_eq_of_mem_central_involution S hno hZ W hW hunique
    (k * g) ?_ z hzC hz ?_
  · rw [← conj_map_comp]
    exact (map_mono hBR).trans hkS
  · rw [← conj_map_comp, ← hkz]
    exact mem_map_of_mem _ hxB

/-- Two conjugate fours generating a two-group commute if the second
normalizes the first. -/
public theorem conjugate_le_centralizer_of_le_normalizer
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) (hcontrol : LocalCentralizerControl S W)
    (g t : G)
    (hP : IsPGroup 2
      (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ⊔
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom) : Subgroup G))
    (hVN : (W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom ≤
      normalizer
        (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) : Set G)) :
    (W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer
        (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) : Set G) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let B := W₀.map (MulAut.conj g).toMonoidHom
  let V := W₀.map (MulAut.conj t).toMonoidHom
  obtain ⟨k, hkS, hkB⟩ := transport_normalizing_conjugate_four S hno hZ W hW hunique
    z hzW hzC hz hsep g (B ⊔ V) hP le_sup_left (sup_le B.le_normalizer hVN)
  change B.map (MulAut.conj k).toMonoidHom = W₀ at hkB
  have hVk : V.map (MulAut.conj k).toMonoidHom ≤ centralizer (W₀ : Set G) := by
    rw [conj_map_comp]
    apply returning_conjugate_le_centralizer S hno hZ W hW hunique hcontrol
    rw [← conj_map_comp]
    exact (map_mono (show V ≤ B ⊔ V from le_sup_right)).trans hkS
  intro v hv b hb
  apply (MulAut.conj k).injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
    hVk (mem_map_of_mem _ hv) ((MulAut.conj k) b) (hkB ▸ mem_map_of_mem _ hb)

/-- Distinct conjugate fours in a common two-subgroup are disjoint. -/
public theorem disjoint_conjugates_of_isPGroup_sup
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) [(fourImage S W).Normal]
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hsep : Separated S W z) (hfactor : CentralizerFactorization S W)
    (hcontrol : LocalCentralizerControl S W) (g t : G)
    (hP : IsPGroup 2
      (((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) ⊔
        ((W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom) : Subgroup G))
    (hne : (W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom ≠
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) :
    Disjoint ((W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom)
      ((W.map (S : Subgroup G).subtype).map (MulAut.conj t).toMonoidHom) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let B := W₀.map (MulAut.conj g).toMonoidHom
  let V := W₀.map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  apply disjoint_def.mpr
  intro x hxB hxV
  by_contra hx1
  have hRC : B ⊔ V ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro b hb
      exact mem_centralizer_singleton_iff.mpr (B.le_centralizer hb x hxB).symm
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (V.le_centralizer hv x hxV).symm
  have hRN : B ⊔ V ≤ normalizer (B : Set G) :=
    conjugate_normalized_by_centralizing_two_overgroup S hno hZ W hW hunique hcontrol
      g (B ⊔ V) hP le_sup_left x hxB hx1 hRC
  obtain ⟨k, hkS, hkB⟩ := transport_normalizing_conjugate_four S hno hZ W hW hunique
    z hzW hzC hz hsep g (B ⊔ V) hP le_sup_left hRN
  change B.map (MulAut.conj k).toMonoidHom = W₀ at hkB
  have hVkS : V.map (MulAut.conj k).toMonoidHom ≤ (S : Subgroup G) :=
    (map_mono (show V ≤ B ⊔ V from le_sup_right)).trans hkS
  have hVkne : V.map (MulAut.conj k).toMonoidHom ≠ W₀ := by
    intro he
    exact hne (map_injective (MulAut.conj k).injective (he.trans hkB.symm))
  have hd : Disjoint W₀ (V.map (MulAut.conj k).toMonoidHom) := by
    rw [conj_map_comp] at hVkS hVkne ⊢
    exact disjoint_of_distinct_returning_conjugate_four S hno hZ W hW hunique
      z hzW hzC hz hsep hfactor (k * t) hVkS hVkne
  have he : (MulAut.conj k) x = 1 :=
    disjoint_def.mp hd (hkB ▸ mem_map_of_mem _ hxB) (mem_map_of_mem _ hxV)
  exact hx1 ((MulAut.conj k).injective (he.trans (map_one _).symm))

end Stellmacher.Recognition.NormalEightSeparatedConjugateRigidity
