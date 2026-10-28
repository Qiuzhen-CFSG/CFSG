module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-! Normalizers as closed subgroups of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The normalizer of a closed subgroup is Zariski closed. -/
public lemma ClosedSubgroup.normalizer_isZariskiClosed
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IsZariskiClosed G
      (Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G)) :
        Set (Variety.Point G)) := by
  let A : H.toSubgroup → Set (Variety.Point G) := fun h ↦
    (conjugateMorphism G h.val).toFun ⁻¹'
      (H.toSubgroup : Set (Variety.Point G))
  let B : H.toSubgroup → Set (Variety.Point G) := fun h ↦
    (inverseConjugateMorphism G h.val).toFun ⁻¹'
      (H.toSubgroup : Set (Variety.Point G))
  have hclosedA : IsZariskiClosed G (⋂ h, A h) :=
    isZariskiClosed_iInter A fun h ↦
      (conjugateMorphism G h.val).isZariskiClosed_preimage
        H.isZariskiClosed
  have hclosedB : IsZariskiClosed G (⋂ h, B h) :=
    isZariskiClosed_iInter B fun h ↦
      (inverseConjugateMorphism G h.val).isZariskiClosed_preimage
        H.isZariskiClosed
  have hclosed : IsZariskiClosed G ((⋂ h, A h) ∩ ⋂ h, B h) :=
    isZariskiClosed_inter hclosedA hclosedB
  have hset :
      (Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G)) :
          Set (Variety.Point G)) = (⋂ h, A h) ∩ ⋂ h, B h := by
    ext g
    constructor
    · intro hg
      have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      have hginv : g⁻¹ ∈
          Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G)) :=
        (Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G))).inv_mem hg
      have hmapInv := Subgroup.mem_normalizer_iff_map_conj_eq.mp hginv
      constructor
      · rw [Set.mem_iInter]
        intro h
        change (conjugateMorphism G h.val).toFun g ∈ H.toSubgroup
        rw [conjugateMorphism_apply]
        have hm : (MulAut.conj g) h.val ∈
            Subgroup.map (MulAut.conj g : Variety.Point G →* Variety.Point G)
              H.toSubgroup :=
          Subgroup.mem_map_of_mem
            (MulAut.conj g : Variety.Point G →* Variety.Point G) h.property
        rw [hmap] at hm
        simpa [MulAut.conj_apply] using hm
      · rw [Set.mem_iInter]
        intro h
        change (inverseConjugateMorphism G h.val).toFun g ∈
          H.toSubgroup
        rw [inverseConjugateMorphism_apply]
        have hm : (MulAut.conj g⁻¹) h.val ∈
            Subgroup.map (MulAut.conj g⁻¹ : Variety.Point G →* Variety.Point G)
              H.toSubgroup :=
          Subgroup.mem_map_of_mem
            (MulAut.conj g⁻¹ : Variety.Point G →* Variety.Point G) h.property
        rw [hmapInv] at hm
        simpa [MulAut.conj_apply] using hm
    · intro hg
      change g ∈ Subgroup.normalizer
        (H.toSubgroup : Set (Variety.Point G))
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm
      · intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨h, hh, rfl⟩
        have hAh := Set.mem_iInter.mp hg.1 ⟨h, hh⟩
        change (conjugateMorphism G h).toFun g ∈ H.toSubgroup at hAh
        rw [conjugateMorphism_apply] at hAh
        simpa [MulAut.conj_apply] using hAh
      · intro h hh
        have hBh := Set.mem_iInter.mp hg.2 ⟨h, hh⟩
        change (inverseConjugateMorphism G h).toFun g ∈
          H.toSubgroup at hBh
        rw [inverseConjugateMorphism_apply] at hBh
        refine Subgroup.mem_map.mpr ⟨g⁻¹ * h * g, hBh, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
  rw [hset]
  exact hclosed

/-- The normalizer as a closed subgroup. -/
@[expose]
public def ClosedSubgroup.normalizer {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (Subgroup.normalizer (H.toSubgroup : Set (Variety.Point G)))
    H.normalizer_isZariskiClosed

end Theory.AlgebraicGroup
