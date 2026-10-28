module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Reduction
public import Theory.GroupTheory.IndexTwoFourCentralizer
public import Theory.GroupTheory.PerfectDihedralFourAction

/-!
# Four-group centralizers in quadratic extensions without field involutions

Every elementary actor lies in the literal linear kernel K. That kernel is
the prescribed PSL₂(F), whose four-groups are self-centralizing and have
nontrivial odd normalizer action by the perfect dihedral-Sylow argument.
The index-two centralizer lemma then proves C_S(A)=A: an outside centralizer
element would yield an outside involution, contrary to the hypothesis.

Thus the actual ambient tau equals A for every large elementary actor.
This justifies transporting local witnesses from the kernel, even though
an ambient Sylow need not be dihedral. Both p=3 and p=5 are included; no
field-involution lift, complement or model-exhaustion hypothesis is used.

Source: Aschbacher--Smith, E.1.1--2 and E.1.14(6), printed pp.209--210 and
214, with Gorenstein--Walter Part I, Lemma 2.1 for the normalizer action.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
variable {F : Type*} [Field F] [Finite F]

/-- No additional four-group centralizer occurs outside the literal PSL₂ kernel. -/
theorem kleinFour_selfCentralizing {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hkernel : pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (A : Subgroup S) (hA : IsKleinFour A) : centralizer (A : Set S) = A := by
  let : IsKleinFour A := hA
  let : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let K := pGammaL2LinearKernel F S
  have hAK : A ≤ K := elementary_le_linearKernel_of_no_field_involutions
    S hnofield A inferInstance
  let D := A.subgroupOf K
  have hD : IsKleinFour D := isKleinFour_subgroupOf hAK hA
  have hC : centralizer (D : Set K) = D :=
    linearKernel_four_selfCentralizing hp hodd hF S hS D hD
  let e : K ≃* PSL2 F := (MulEquiv.subgroupCongr hkernel).trans
    ((subgroupOfEquivOfLe hS).trans (pGammaL2PSLRangeEquiv F).symm)
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨n, hn, hn2⟩ := perfect_dihedral_four_normalizer_action
    (hasDihedralSylowTwo_of_mulEquiv e
      (psl2_odd_hasDihedralSylowTwo_model F ⟨p, 2, hp, hodd, by decide, hF⟩)) D hD
  apply centralizer_four_eq_of_index_two K A hindex hA
  · intro x hx
    have hxC : (⟨x, hx.2⟩ : K) ∈ centralizer (D : Set K) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact Subtype.ext (mem_centralizer_iff.mp hx.1 a ha)
    exact hC.le hxC
  · intro x hx
    exact (mem_pGammaL2LinearKernel_iff F S x).mpr (hnofield x hx)
  · refine ⟨n, ?_, ?_⟩
    · have hn' : n ∈ (normalizer (A : Set S)).subgroupOf K := by
        rw [subgroupOf_normalizer_eq hAK]
        exact hn
      exact hn'
    · intro hc
      apply hn2
      rw [mem_centralizer_iff]
      intro a ha
      exact Subtype.ext (mem_centralizer_iff.mp hc a ha)

/-- The ambient E0 subgroup is exactly the given large elementary actor. -/
theorem tau_eq_actor {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hkernel : pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (T : Sylow 2 S) (A : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup S)) (hr : 1 < Group.rank A) :
    tau (T : Subgroup S) A = A := by
  let := hA
  exact PrimeGeometry.tau_eq_self_of_selfCentralizing T A hAT
    (twoCore_eq_bot hp hodd hF hlarge S hS)
    (kleinFour_selfCentralizing hp hodd hF hlarge S hS hindex hkernel hnofield A
      (large_actor_isKleinFour_of_no_field_involutions hp hodd hF S hS hnofield A hA hr))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
