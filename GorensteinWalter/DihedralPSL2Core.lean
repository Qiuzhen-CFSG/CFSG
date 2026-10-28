module
public import GorensteinWalter.FinalTheorem
public import GorensteinWalter.PSL2CoreModelFacts

/-!
# A normal PSL2 core from the dihedral classification

A finite group with dihedral Sylow two-subgroups and trivial odd core has
an actual normal odd-field PSL2 subgroup once the two-group and A7 cases
are excluded. No normal index-two subgroup is assumed.

Apply the proved Gorenstein--Walter theorem and identify the odd-core
quotient with the original group. Its normal linear subgroup is either
already PSL2 or PGL2. In the latter case its characteristic commutator
subgroup is the required PSL2 subgroup, including the field of order three.
This is the classification step in ABG II.3 Lemma 2, article page 24.
-/

namespace GorensteinWalter
universe u

public theorem exists_normal_psl2_of_not_twoGroup_not_a7
    {H : Type u} [Group H] [Finite H]
    (hHd : HasDihedralSylowTwo H) (hO : pPrimeCore 2 H = ⊥)
    (htwo : ¬ IsPGroup 2 H)
    (hA : ¬ Nonempty (H ≃* alternatingGroup (Fin 7))) :
    ∃ (F : Type u) (iF : Field F) (_ : Finite F),
      let : Field F := iF
      IsOddPrimePower (Nat.card F) ∧
        ∃ L : Subgroup H, L.Normal ∧ Nonempty (L ≃* PSL2 F) := by
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) hO).trans
      (QuotientGroup.quotientBot (G := H))
  rcases gorensteinWalter H hHd with ⟨_, hT⟩ | ⟨_, ⟨eA⟩⟩ |
      ⟨_, F, hF, Nq, hNq, _hNi, hNm⟩
  · exact (htwo (hT.of_equiv eQ)).elim
  · exact (hA ⟨eQ.symm.trans eA⟩).elim
  · let N := Nq.map eQ.toMonoidHom
    let eN : Nq ≃* N := Subgroup.equivMapOfInjective Nq eQ.toMonoidHom eQ.injective
    have hNN : N.Normal := hNq.map eQ.toMonoidHom eQ.surjective
    let : N.Normal := hNN
    rcases hNm with hpsl | hpgl
    · exact ⟨F, inferInstance, inferInstance, hF, N, hNN, ⟨eN.symm.trans hpsl.some⟩⟩
    · let L := (commutator N).map N.subtype
      have hLN : L.Normal := ConjAct.normal_of_characteristic_of_normal
      exact ⟨F, inferInstance, inferInstance, hF, L, hLN,
        ⟨(Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).symm.trans
          (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 F hF (eN.symm.trans hpgl.some)).some⟩⟩

end GorensteinWalter
