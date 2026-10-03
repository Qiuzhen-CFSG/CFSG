module

public import Stellmacher.SectionTwo.LemmaTwoOne

/-!
# The Section 2 subgroup `V` is elementary abelian

Under the hypotheses of Section 2, this module proves that the normal closure
`V = ⟨Ω₁(Z(S))^G⟩` is an elementary abelian subgroup of the 2-core of
`G`.  This is the elementary-abelian input in Stellmacher's proof of (2.2),
independent of the classification results (1.6) and (1.7).

The proof first uses `C_G(O₂(G)) ≤ O₂(G)` and `O₂(G) ≤ S` to place
`Ω₁(Z(S))` in `Ω₁(Z(O₂(G)))`.  The latter subgroup is characteristic
in `O₂(G)`, hence normal in `G`, so it contains the normal closure `V`.
Its commutativity and exponent-two law then restrict to `V`.

Source: the setup preceding Lemma (2.2) in
`refs/latex/stellmacher-n-group.tex`, corresponding to Journal of Algebra 190
(1997), p. 20.
-/

namespace Stellmacher.SectionTwo

universe u

private theorem zSubgroup_le_omegaOneCenter_twoCore
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G) :
    zSubgroup S ≤ omegaOneCenterAmbient (pCore 2 G) := by
  let Q : Subgroup G := pCore 2 G
  have hQ_le_S : Q ≤ (S : Subgroup G) :=
    fitting_pCore_le_sylow S
  have hz_le_Q : zSubgroup S ≤ Q := by
    have hQ_le_cent_z :
        Q ≤ Subgroup.centralizer (zSubgroup S : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [zSubgroup, omegaOneCenterAmbient] at hz
      obtain ⟨zS, hzS, rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨zC, _hzOmega, rfl⟩ := Subgroup.mem_map.mp hzS
      have hqS : q ∈ (S : Subgroup G) := hQ_le_S hq
      have hcomm := (Subgroup.mem_center_iff.mp zC.property) ⟨q, hqS⟩
      simpa using congrArg (fun x : S ↦ (x : G)) hcomm.symm
    exact (Subgroup.le_centralizer_iff.mp hQ_le_cent_z).trans
      h.centralizer_twoCore_le
  intro z hz
  simp only [zSubgroup, omegaOneCenterAmbient] at hz ⊢
  obtain ⟨zS, hzS, hzeq⟩ := Subgroup.mem_map.mp hz
  obtain ⟨zC, hzOmega, hzSeq⟩ := Subgroup.mem_map.mp hzS
  have hzQ : z ∈ Q := hz_le_Q hz
  let zQ : Q := ⟨z, hzQ⟩
  have hzcenterQ : zQ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have hqS : (q : G) ∈ (S : Subgroup G) := hQ_le_S q.property
    have hcomm := (Subgroup.mem_center_iff.mp zC.property) ⟨(q : G), hqS⟩
    simpa [zQ, ← hzeq, ← hzSeq] using
      congrArg (fun x : S ↦ (x : G)) hcomm
  let zZQ : Subgroup.center Q := ⟨zQ, hzcenterQ⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOmegaS : IsElementaryAbelian 2
      (omega₁ (G := Subgroup.center (S : Subgroup G)) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2)
      (Subgroup.center (S : Subgroup G))
  let _ : IsElementaryAbelian 2
      (omega₁ (G := Subgroup.center (S : Subgroup G)) (p := 2)) := hOmegaS
  have hzpowS : zC ^ 2 = 1 := by
    have hzpow := elemPow_eq_one_of_isElementaryAbelian (p := 2) zC hzOmega
    simpa using hzpow
  have hzpowZQ : zZQ ^ 2 = 1 := by
    apply (Subgroup.center Q).subtype_injective
    apply Q.subtype_injective
    simpa [zZQ, zQ, ← hzeq, ← hzSeq] using
      congrArg
        (fun x : Subgroup.center (S : Subgroup G) ↦ (x : G)) hzpowS
  have hzOmegaQ : zZQ ∈ omega₁ (G := Subgroup.center Q) (p := 2) := by
    rw [omega₁, omega]
    apply Subgroup.subset_closure
    simpa using hzpowZQ
  exact Subgroup.mem_map_of_mem Q.subtype
    (Subgroup.mem_map_of_mem (Subgroup.center Q).subtype hzOmegaQ)

/-- Under the Section 2 characteristic-2 hypothesis, the normal closure of
`Ω₁(Z(S))` lies in `O₂(G)` and is elementary abelian. -/
public theorem vSubgroup_le_twoCore_and_elementaryAbelian
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G) :
    vSubgroup S ≤ pCore 2 G ∧ IsElementaryAbelian 2 (vSubgroup S) := by
  let Q : Subgroup G := pCore 2 G
  let ZQ : Subgroup Q := Subgroup.center Q
  let W : Subgroup ZQ := omega₁ (G := ZQ) (p := 2)
  let E : Subgroup Q := W.map ZQ.subtype
  let A : Subgroup G := E.map Q.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : ZQ.Characteristic := Subgroup.centerCharacteristic
  let _ : W.Characteristic := by
    dsimp [W]
    exact omega₁_characteristic ZQ
  let _ : E.Characteristic := by
    dsimp [E]
    exact Subgroup.characteristic_of_characteristic_of_characteristic
  let _ : A.Normal := by
    dsimp [A]
    exact ConjAct.normal_of_characteristic_of_normal
  have hW : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) ZQ
  have hE : IsElementaryAbelian 2 E := by
    exact IsElementaryAbelian.map (p := 2) (A := W) ZQ.subtype
  have hA : IsElementaryAbelian 2 A := by
    exact IsElementaryAbelian.map (p := 2) (A := E) Q.subtype
  have hzA : zSubgroup S ≤ A := by
    simpa [A, E, W, ZQ, Q, omegaOneCenterAmbient] using
      zSubgroup_le_omegaOneCenter_twoCore h S
  have hvA : vSubgroup S ≤ A :=
    Subgroup.normalClosure_le_normal hzA
  constructor
  · exact hvA.trans (Subgroup.map_subtype_le E)
  · let _ : IsElementaryAbelian 2 A := hA
    refine
      { toIsMulCommutative :=
          ⟨⟨fun x y ↦ Subtype.ext
            (show (x : G) * (y : G) = (y : G) * (x : G) from ?_)⟩⟩
        exponent_dvd_p := ?_ }
    · have hcomm := (IsMulCommutative.is_comm (M := A)).comm
          (⟨x, hvA x.property⟩ : A) (⟨y, hvA y.property⟩ : A)
      exact congrArg Subtype.val hcomm
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := A) (x : G) (hvA x.property)

end Stellmacher.SectionTwo
