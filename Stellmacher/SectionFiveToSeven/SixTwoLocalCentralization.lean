module
public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.SectionThree.LemmaThreeSeven
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Local centralization from Thompson containment

Suppose `S` is a Sylow two-subgroup of a finite local subgroup `P` of
characteristic two. If `J(S) ≤ O₂(P)` and the commutator of `O²(P)` with
the Baumann subgroup of `S` is all of `O²(P)`, then `P` centralizes
`Ω₁(Z(S))`. Only these local hypotheses are used.

Write `Q = O₂(P)` and `E = Ω₁(Z(Q))`. Since `E ≤ S` is elementary and
centralizes `J(S) ≤ Q`, the maximum-elementary-subgroup argument places
`E` in `Ω₁(Z(J(S)))`. Thus the Baumann subgroup centralizes `E`.
Characteristicity makes `P` normalize `E` and hence normalize its centralizer;
the residual commutator hypothesis puts `O²(P)` in that centralizer.
Finally, characteristic two puts `Ω₁(Z(S))` inside `Q`, where it belongs
to `E`. Both `O²(P)` and `S` centralize it, and these generate `P`.

This is the implication used in Stellmacher (6.2), Journal of Algebra 190
(1997), p.30, `refs/latex/stellmacher-n-group.tex`. It isolates the argument
after the application of (3.4); it does not assume (6.1) or Hypothesis Two.
-/

namespace Stellmacher.SectionsFiveToSeven

private theorem normalizer_le_normalizer_omegaCenter
    {H : Type*} [Group H] (Q : Subgroup H) :
    Subgroup.normalizer (Q : Set H) ≤
      Subgroup.normalizer (omegaOneCenter Q : Set H) := by
  let K : Subgroup Q :=
    (omega₁ (G := Subgroup.center Q) (p := 2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic :=
    omega₁_characteristic (Subgroup.center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

/-- Thompson containment in a characteristic-two local core forces
centralization of the Sylow's central involutions when the Baumann residual
commutator is the full residual. -/
public theorem sixTwo_local_centralization
    {H : Type*} [Group H] [Finite H] (S P : Subgroup H)
    (hSyl : IsSylowTwoIn S P) (hchar : IsCharacteristicTwoType P)
    (hJ : elementaryAbelianMaxJ S ≤ twoCoreIn P)
    (hcomm : ⁅twoResidualIn P, baumannIn S⁆ = twoResidualIn P) :
    ⁅P, omegaOneCenter S⁆ = ⊥ := by
  let Q := twoCoreIn P
  let E := omegaOneCenter Q
  let C := Subgroup.centralizer (E : Set H)
  let R := twoResidualIn P
  have hSP : S ≤ P := hSyl.1
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hQS : Q ≤ S := by
    obtain ⟨T, hT⟩ := hSyl.2
    rw [← hT]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)
  have hQN : (Q.subgroupOf P).Normal := by
    change (((pCore 2 P).map P.subtype).subgroupOf P).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPNQ : P ≤ Subgroup.normalizer (Q : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQN
  have hPNE : P ≤ Subgroup.normalizer (E : Set H) :=
    hPNQ.trans (normalizer_le_normalizer_omegaCenter Q)
  have hEQ : E ≤ Q := fun x hx => (mem_omegaOneCenterAmbient_iff Q x).mp hx |>.1
  let _ : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian Q
  have hECQ : E ≤ Subgroup.centralizer (Q : Set H) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff Q x).mp hx |>.2.2)
  have hEJ : E ≤ omegaOneCenter (elementaryAbelianMaxJ S) :=
    elementary_centralizer_maxJ_le_omegaCenter S E (hEQ.trans hQS)
      (hECQ.trans (Subgroup.centralizer_le hJ))
  have hBC : baumannIn S ≤ C :=
    (show baumannIn S ≤ Subgroup.centralizer
      (omegaOneCenter (elementaryAbelianMaxJ S) : Set H) from inf_le_right).trans
        (Subgroup.centralizer_le hEJ)
  have hNC : Subgroup.normalizer (E : Set H) ≤ Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (E : Set H))).mp inferInstance
  have hRC : R ≤ C := by
    rw [show R = twoResidualIn P from rfl, ← hcomm]
    exact (Subgroup.commutator_mono (Subgroup.map_subtype_le _) hBC).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hPNE.trans hNC))
  have hZQ : omegaOneCenter S ≤ Q := by
    intro z hz
    obtain ⟨hzS, _hzpow, hzcent⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    have hzP : z ∈ P := hSP hzS
    have hzC : (⟨z, hzP⟩ : P) ∈ Subgroup.centralizer (pCore 2 P : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      exact hzcent q (hQS (Subgroup.mem_map_of_mem P.subtype hq))
    exact Subgroup.mem_map_of_mem P.subtype (hchar hzC)
  have hZE : omegaOneCenter S ≤ E := by
    intro z hz
    obtain ⟨_hzS, hzpow, hzcent⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    exact (mem_omegaOneCenterAmbient_iff Q z).mpr
      ⟨hZQ hz, hzpow, fun q hq => hzcent q (hQS hq)⟩
  have hgen : R ⊔ S = P := SectionThree.twoResidual_sup_sylowImage hSyl.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hgen]
  apply sup_le (hRC.trans (Subgroup.centralizer_le hZE))
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((mem_omegaOneCenterAmbient_iff S z).mp hz |>.2.2 s hs).symm

end Stellmacher.SectionsFiveToSeven
