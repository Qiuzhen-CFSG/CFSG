module
public import Theory.GroupTheory.Commutator.QuasisimpleTwoEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.FrattiniCore

/-!
# The Frattini comparison with a quasisimple component

The original two-subgroup comparison in MS93 (3.6) detects the full core
without replacing the component quotient by its central quotient. Thus the
same reduction covers A₆ and its odd central covers and permits a central
fixed layer in the resulting elementary core.

Source: MS93 (3.6), first paragraph, printed p.870. The local commutator
estimate is the precise geometric premise left to the critical-pair argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

/-- The source's local commutator comparison implies its whole Frattini bound. -/
theorem frattini_small_of_local_comparison
    (K R E : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hR : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (hE : IsPGroup 2 E) (hne : ¬ E ≤ pCore 2 H)
    (hcomm : ⁅pCore 2 H,E⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H) := by
  let : ((frattini (pCore 2 H)).map (pCore 2 H).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let : Fact (IsPGroup 2 (pCore 2 H)) := ⟨pCore_isPGroup⟩
  apply commutator_le_of_quasisimple_two_escape K R _ E hK hR hgen hE hne _ hcomm
  apply le_trans _ le_sup_left
  rw [←map_subtype_commutator]
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

/-- After the comparison, the entire intrinsic core is the moved omega-center. -/
theorem intrinsic_core_of_local_comparison
    (K R E : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hR : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (hE : IsPGroup 2 E) (hne : ¬ E ≤ pCore 2 H)
    (hcomm : ⁅pCore 2 H,E⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    (blockU K).map K.subtype = ⁅omegaCenterIn (pCore 2 H),K⁆ ∧
      IsElementaryAbelian 2 (blockU K) ∧
      blockU K ≤ centralizer (pCore 2 K : Set K) := by
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hn hq
    let := hn
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  exact intrinsic_core_of_frattini_small K hp
    (frattini_small_of_local_comparison K R E hK hR hgen hE hne hcomm)

end CFSG.Quasithin.ChapterC.MSCentralOrbit
