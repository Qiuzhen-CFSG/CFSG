module

public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannTwoOvergroupNormalizer

/-!
# Thompson and Baumann transport through a two-overgroup

Let `S` be a Sylow two-subgroup of a finite group and let `Q` be a
two-subgroup containing the Baumann subgroup `B(S)`.  Then the elementary
Thompson and Baumann subgroups of `Q`, computed in the common ambient group,
are respectively `J(S)` and `B(S)`.

The proof extends `Q` to a Sylow subgroup `T` and repeats the weak-closure
transport underlying `twoSubgroup_le_normalizer_baumann`.  It first identifies
`J(T)` and `B(T)` with the corresponding subgroups of `S`.  Baumann heredity
through `B(T) ≤ Q ≤ T` identifies `B(Q)`, while the two maximum-order
comparisons identify `J(Q)`.

This is the subgroup-transport step in the final quotient argument of
Stellmacher (5.2), Journal of Algebra 190 (1997), pp. 28--29.
-/

namespace Stellmacher

universe u

private theorem centralizer_map_equiv
    {G : Type u} [Group G] (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer (A : Set G) at hx
    change e x ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg e (hx a ha)
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change y ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G) at hy
    change e.symm y ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro a ha
    apply e.injective
    simpa using hy (e a) ⟨a, ha, rfl⟩

private theorem baumann_map_equiv
    {G : Type u} [Group G] (S : Subgroup G) (e : G ≃* G) :
    (S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)).map
        e.toMonoidHom =
      S.map e.toMonoidHom ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S.map e.toMonoidHom)) : Set G) := by
  rw [Subgroup.map_inf _ _ _ e.injective,
    centralizer_map_equiv,
    elementaryAbelianMaxJ_map_equiv,
    omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective]

private theorem elementaryAbelianMaxJ_le_baumann
    {G : Type u} [Group G] (S : Subgroup G) :
    elementaryAbelianMaxJ S ≤
      S ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) := by
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA ↦ hA.1
  refine le_inf hJS ?_
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨wJ, hwJ, rfl⟩ := hw
  obtain ⟨wZ, _, rfl⟩ := hwJ
  exact congrArg Subtype.val
    ((Subgroup.mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm

/-- A two-subgroup containing `B(S)` has the same elementary Thompson and
Baumann subgroups as the Sylow two-subgroup `S`, in their common ambient
group. -/
public theorem twoSubgroup_thompson_baumann_eq
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) (Q : Subgroup G)
    (hQp : IsPGroup 2 Q)
    (hBQ : (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S : Subgroup G)) : Set G) ≤ Q) :
    elementaryAbelianMaxJ Q = elementaryAbelianMaxJ (S : Subgroup G) ∧
      Q ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) =
      (S : Subgroup G) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S : Subgroup G)) : Set G) := by
  let B : Subgroup G :=
    (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  obtain ⟨T, hQT⟩ := hQp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e : G ≃* G := MulAut.conj g
  have hTmap : (T : Subgroup G).map e.toMonoidHom = (S : Subgroup G) := by
    have hsub := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hsub
    exact hsub
  have hJleT : elementaryAbelianMaxJ (S : Subgroup G) ≤ (T : Subgroup G) :=
    (elementaryAbelianMaxJ_le_baumann (S : Subgroup G)).trans (hBQ.trans hQT)
  have hJmapLeS :
      (elementaryAbelianMaxJ (S : Subgroup G)).map e.toMonoidHom ≤
        (S : Subgroup G) := by
    exact (Subgroup.map_mono hJleT).trans_eq hTmap
  have hJstable :
      (elementaryAbelianMaxJ (S : Subgroup G)).map e.toMonoidHom =
        elementaryAbelianMaxJ (S : Subgroup G) :=
    elementaryAbelianMaxJ_map_eq_of_le (S : Subgroup G) e hJmapLeS
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) =
      elementaryAbelianMaxJ (S : Subgroup G) := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    calc
      (elementaryAbelianMaxJ (T : Subgroup G)).map e.toMonoidHom =
          elementaryAbelianMaxJ ((T : Subgroup G).map e.toMonoidHom) :=
        (elementaryAbelianMaxJ_map_equiv e (T : Subgroup G)).symm
      _ = elementaryAbelianMaxJ (S : Subgroup G) := by rw [hTmap]
      _ = (elementaryAbelianMaxJ (S : Subgroup G)).map e.toMonoidHom :=
        hJstable.symm
  let BT : Subgroup G :=
    (T : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (T : Subgroup G)) : Set G)
  have hB_le_BT : B ≤ BT := by
    refine le_inf (hBQ.trans hQT) ?_
    change B ≤ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (T : Subgroup G)) : Set G)
    rw [hJT]
    exact inf_le_right
  have hBTmap : BT.map e.toMonoidHom = B := by
    change
      ((T : Subgroup G) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient
          (elementaryAbelianMaxJ (T : Subgroup G)) : Set G)).map e.toMonoidHom =
      (S : Subgroup G) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
    rw [baumann_map_equiv, hTmap]
  have hB_eq_BT : B = BT := by
    apply Subgroup.eq_of_le_of_card_ge hB_le_BT
    rw [← hBTmap, Subgroup.card_map_of_injective e.injective]
  have hBTQ : BT ≤ Q := hB_eq_BT ▸ hBQ
  have hBQeq :
      Q ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) = B := by
    calc
      Q ⊓ Subgroup.centralizer
          (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) = BT := by
        simpa [BT] using baumann_eq_of_intermediate (T : Subgroup G) Q hBTQ hQT
      _ = B := hB_eq_BT.symm
  have hJQ_le_Q : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q :=
    (elementaryAbelianMaxJ_le_baumann (T : Subgroup G)).trans hBTQ
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq Q (T : Subgroup G) hQT
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    (T : Subgroup G) Q hJQ_le_Q
  have horder : elementaryAbelianMaxOrder Q =
      elementaryAbelianMaxOrder (T : Subgroup G) :=
    le_antisymm hsmall.1 hlarge.1
  have hJQT : elementaryAbelianMaxJ Q = elementaryAbelianMaxJ (T : Subgroup G) :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  exact ⟨hJQT.trans hJT, hBQeq⟩

end Stellmacher
