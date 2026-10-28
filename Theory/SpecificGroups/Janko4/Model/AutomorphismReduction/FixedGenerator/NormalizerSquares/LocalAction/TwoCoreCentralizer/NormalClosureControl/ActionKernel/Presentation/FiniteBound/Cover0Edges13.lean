module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges12

/-!
# The 693-coset cover of the fixed max2 presentation

The fixed words and transitions replay `source/special_scan.json`.
Tree edges are word extensions; 17 special edges have subgroup tails and
relations derived from the 29 published relators. Every remaining edge is
obtained by cancelling known paths in an original relator loop.
The untrusted producer uses GAP only to discover this finite witness.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000

theorem edge832 : Holds level0Subgroup PresentedGroup.of representative ⟨170, [(false, true)], 128⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨128, [(false, true)], 170⟩ :=
    edge169
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨128, [], 128⟩ :=
    (holds_refl 128)
  exact scanFacts hp hs (holds_relator 128 (level0Relator 0) (level0_relator 0))

theorem edge832Inv : Holds level0Subgroup PresentedGroup.of representative ⟨128, [(false, false)], 170⟩ :=
  holds_reverse edge832

theorem edge833 : Holds level0Subgroup PresentedGroup.of representative ⟨171, [(false, true)], 129⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(false, true)], 171⟩ :=
    edge170
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨129, [], 129⟩ :=
    (holds_refl 129)
  exact scanFacts hp hs (holds_relator 129 (level0Relator 0) (level0_relator 0))

theorem edge833Inv : Holds level0Subgroup PresentedGroup.of representative ⟨129, [(false, false)], 171⟩ :=
  holds_reverse edge833

theorem edge834 : Holds level0Subgroup PresentedGroup.of representative ⟨172, [(false, true)], 130⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨130, [(false, true)], 172⟩ :=
    edge171
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨130, [], 130⟩ :=
    (holds_refl 130)
  exact scanFacts hp hs (holds_relator 130 (level0Relator 0) (level0_relator 0))

theorem edge834Inv : Holds level0Subgroup PresentedGroup.of representative ⟨130, [(false, false)], 172⟩ :=
  holds_reverse edge834

theorem edge835 : Holds level0Subgroup PresentedGroup.of representative ⟨173, [(false, true)], 131⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(false, true)], 173⟩ :=
    edge172
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨131, [], 131⟩ :=
    (holds_refl 131)
  exact scanFacts hp hs (holds_relator 131 (level0Relator 0) (level0_relator 0))

theorem edge835Inv : Holds level0Subgroup PresentedGroup.of representative ⟨131, [(false, false)], 173⟩ :=
  holds_reverse edge835

theorem edge836 : Holds level0Subgroup PresentedGroup.of representative ⟨174, [(false, true)], 132⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨132, [(false, true)], 174⟩ :=
    edge173
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨132, [], 132⟩ :=
    (holds_refl 132)
  exact scanFacts hp hs (holds_relator 132 (level0Relator 0) (level0_relator 0))

theorem edge836Inv : Holds level0Subgroup PresentedGroup.of representative ⟨132, [(false, false)], 174⟩ :=
  holds_reverse edge836

theorem edge837 : Holds level0Subgroup PresentedGroup.of representative ⟨175, [(false, true)], 133⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(false, true)], 175⟩ :=
    edge174
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨133, [], 133⟩ :=
    (holds_refl 133)
  exact scanFacts hp hs (holds_relator 133 (level0Relator 0) (level0_relator 0))

theorem edge837Inv : Holds level0Subgroup PresentedGroup.of representative ⟨133, [(false, false)], 175⟩ :=
  holds_reverse edge837

theorem edge838 : Holds level0Subgroup PresentedGroup.of representative ⟨176, [(false, true)], 134⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨134, [(false, true)], 176⟩ :=
    edge175
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨134, [], 134⟩ :=
    (holds_refl 134)
  exact scanFacts hp hs (holds_relator 134 (level0Relator 0) (level0_relator 0))

theorem edge838Inv : Holds level0Subgroup PresentedGroup.of representative ⟨134, [(false, false)], 176⟩ :=
  holds_reverse edge838

theorem edge839 : Holds level0Subgroup PresentedGroup.of representative ⟨177, [(false, true)], 135⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(false, true)], 177⟩ :=
    edge176
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨135, [], 135⟩ :=
    (holds_refl 135)
  exact scanFacts hp hs (holds_relator 135 (level0Relator 0) (level0_relator 0))

theorem edge839Inv : Holds level0Subgroup PresentedGroup.of representative ⟨135, [(false, false)], 177⟩ :=
  holds_reverse edge839

theorem edge840 : Holds level0Subgroup PresentedGroup.of representative ⟨178, [(false, true)], 136⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨136, [(false, true)], 178⟩ :=
    edge177
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨136, [], 136⟩ :=
    (holds_refl 136)
  exact scanFacts hp hs (holds_relator 136 (level0Relator 0) (level0_relator 0))

theorem edge840Inv : Holds level0Subgroup PresentedGroup.of representative ⟨136, [(false, false)], 178⟩ :=
  holds_reverse edge840

theorem edge841 : Holds level0Subgroup PresentedGroup.of representative ⟨179, [(false, true)], 137⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(false, true)], 179⟩ :=
    edge178
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨137, [], 137⟩ :=
    (holds_refl 137)
  exact scanFacts hp hs (holds_relator 137 (level0Relator 0) (level0_relator 0))

theorem edge841Inv : Holds level0Subgroup PresentedGroup.of representative ⟨137, [(false, false)], 179⟩ :=
  holds_reverse edge841

theorem edge842 : Holds level0Subgroup PresentedGroup.of representative ⟨180, [(false, true)], 138⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨138, [(false, true)], 180⟩ :=
    edge179
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨138, [], 138⟩ :=
    (holds_refl 138)
  exact scanFacts hp hs (holds_relator 138 (level0Relator 0) (level0_relator 0))

theorem edge842Inv : Holds level0Subgroup PresentedGroup.of representative ⟨138, [(false, false)], 180⟩ :=
  holds_reverse edge842

theorem edge843 : Holds level0Subgroup PresentedGroup.of representative ⟨181, [(false, true)], 139⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(false, true)], 181⟩ :=
    edge180
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨139, [], 139⟩ :=
    (holds_refl 139)
  exact scanFacts hp hs (holds_relator 139 (level0Relator 0) (level0_relator 0))

theorem edge843Inv : Holds level0Subgroup PresentedGroup.of representative ⟨139, [(false, false)], 181⟩ :=
  holds_reverse edge843

theorem edge844 : Holds level0Subgroup PresentedGroup.of representative ⟨182, [(false, true)], 140⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨140, [(false, true)], 182⟩ :=
    edge181
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨140, [], 140⟩ :=
    (holds_refl 140)
  exact scanFacts hp hs (holds_relator 140 (level0Relator 0) (level0_relator 0))

theorem edge844Inv : Holds level0Subgroup PresentedGroup.of representative ⟨140, [(false, false)], 182⟩ :=
  holds_reverse edge844

theorem edge845 : Holds level0Subgroup PresentedGroup.of representative ⟨183, [(false, true)], 141⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(false, true)], 183⟩ :=
    edge182
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨141, [], 141⟩ :=
    (holds_refl 141)
  exact scanFacts hp hs (holds_relator 141 (level0Relator 0) (level0_relator 0))

theorem edge845Inv : Holds level0Subgroup PresentedGroup.of representative ⟨141, [(false, false)], 183⟩ :=
  holds_reverse edge845

theorem edge846 : Holds level0Subgroup PresentedGroup.of representative ⟨184, [(true, true)], 185⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨142, [(true, true)], 184⟩ :=
    edge183
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(true, true)], 142⟩ :=
    edge184Inv
  exact scanFacts hp hs (holds_relator 142 (level0Relator 1) (level0_relator 1))

theorem edge846Inv : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(true, false)], 184⟩ :=
  holds_reverse edge846

theorem edge847 : Holds level0Subgroup PresentedGroup.of representative ⟨186, [(true, true)], 187⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨143, [(true, true)], 186⟩ :=
    edge185
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(true, true)], 143⟩ :=
    edge186Inv
  exact scanFacts hp hs (holds_relator 143 (level0Relator 1) (level0_relator 1))

theorem edge847Inv : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(true, false)], 186⟩ :=
  holds_reverse edge847

theorem edge848 : Holds level0Subgroup PresentedGroup.of representative ⟨188, [(true, true)], 189⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨144, [(true, true)], 188⟩ :=
    edge187
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(true, true)], 144⟩ :=
    edge188Inv
  exact scanFacts hp hs (holds_relator 144 (level0Relator 1) (level0_relator 1))

theorem edge848Inv : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(true, false)], 188⟩ :=
  holds_reverse edge848

theorem edge849 : Holds level0Subgroup PresentedGroup.of representative ⟨190, [(true, true)], 191⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨145, [(true, true)], 190⟩ :=
    edge189
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(true, true)], 145⟩ :=
    edge190Inv
  exact scanFacts hp hs (holds_relator 145 (level0Relator 1) (level0_relator 1))

theorem edge849Inv : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(true, false)], 190⟩ :=
  holds_reverse edge849

theorem edge850 : Holds level0Subgroup PresentedGroup.of representative ⟨192, [(true, true)], 193⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨146, [(true, true)], 192⟩ :=
    edge191
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(true, true)], 146⟩ :=
    edge192Inv
  exact scanFacts hp hs (holds_relator 146 (level0Relator 1) (level0_relator 1))

theorem edge850Inv : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(true, false)], 192⟩ :=
  holds_reverse edge850

theorem edge851 : Holds level0Subgroup PresentedGroup.of representative ⟨194, [(true, true)], 195⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨147, [(true, true)], 194⟩ :=
    edge193
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(true, true)], 147⟩ :=
    edge194Inv
  exact scanFacts hp hs (holds_relator 147 (level0Relator 1) (level0_relator 1))

theorem edge851Inv : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(true, false)], 194⟩ :=
  holds_reverse edge851

theorem edge852 : Holds level0Subgroup PresentedGroup.of representative ⟨196, [(true, true)], 197⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨148, [(true, true)], 196⟩ :=
    edge195
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(true, true)], 148⟩ :=
    edge196Inv
  exact scanFacts hp hs (holds_relator 148 (level0Relator 1) (level0_relator 1))

theorem edge852Inv : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(true, false)], 196⟩ :=
  holds_reverse edge852

theorem edge853 : Holds level0Subgroup PresentedGroup.of representative ⟨198, [(true, true)], 199⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨149, [(true, true)], 198⟩ :=
    edge197
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(true, true)], 149⟩ :=
    edge198Inv
  exact scanFacts hp hs (holds_relator 149 (level0Relator 1) (level0_relator 1))

theorem edge853Inv : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(true, false)], 198⟩ :=
  holds_reverse edge853

theorem edge854 : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(true, true)], 201⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨150, [(true, true)], 200⟩ :=
    edge199
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(true, true)], 150⟩ :=
    edge200Inv
  exact scanFacts hp hs (holds_relator 150 (level0Relator 1) (level0_relator 1))

theorem edge854Inv : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(true, false)], 200⟩ :=
  holds_reverse edge854

theorem edge855 : Holds level0Subgroup PresentedGroup.of representative ⟨202, [(true, true)], 203⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨151, [(true, true)], 202⟩ :=
    edge201
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(true, true)], 151⟩ :=
    edge202Inv
  exact scanFacts hp hs (holds_relator 151 (level0Relator 1) (level0_relator 1))

theorem edge855Inv : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(true, false)], 202⟩ :=
  holds_reverse edge855

theorem edge856 : Holds level0Subgroup PresentedGroup.of representative ⟨169, [(true, true)], 204⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨152, [(true, true)], 169⟩ :=
    edge698
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(true, true)], 152⟩ :=
    edge203Inv
  exact scanFacts hp hs (holds_relator 152 (level0Relator 1) (level0_relator 1))

theorem edge856Inv : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(true, false)], 169⟩ :=
  holds_reverse edge856

theorem edge857 : Holds level0Subgroup PresentedGroup.of representative ⟨205, [(true, true)], 206⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨153, [(true, true)], 205⟩ :=
    edge204
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(true, true)], 153⟩ :=
    edge205Inv
  exact scanFacts hp hs (holds_relator 153 (level0Relator 1) (level0_relator 1))

theorem edge857Inv : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(true, false)], 205⟩ :=
  holds_reverse edge857

theorem edge858 : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(true, true)], 208⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨154, [(true, true)], 207⟩ :=
    edge206
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(true, true)], 154⟩ :=
    edge207Inv
  exact scanFacts hp hs (holds_relator 154 (level0Relator 1) (level0_relator 1))

theorem edge858Inv : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(true, false)], 207⟩ :=
  holds_reverse edge858

theorem edge859 : Holds level0Subgroup PresentedGroup.of representative ⟨209, [(true, true)], 210⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨155, [(true, true)], 209⟩ :=
    edge208
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(true, true)], 155⟩ :=
    edge209Inv
  exact scanFacts hp hs (holds_relator 155 (level0Relator 1) (level0_relator 1))

theorem edge859Inv : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(true, false)], 209⟩ :=
  holds_reverse edge859

theorem edge860 : Holds level0Subgroup PresentedGroup.of representative ⟨211, [(true, true)], 212⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨156, [(true, true)], 211⟩ :=
    edge210
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(true, true)], 156⟩ :=
    edge211Inv
  exact scanFacts hp hs (holds_relator 156 (level0Relator 1) (level0_relator 1))

theorem edge860Inv : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(true, false)], 211⟩ :=
  holds_reverse edge860

theorem edge861 : Holds level0Subgroup PresentedGroup.of representative ⟨213, [(true, true)], 214⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨157, [(true, true)], 213⟩ :=
    edge212
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(true, true)], 157⟩ :=
    edge213Inv
  exact scanFacts hp hs (holds_relator 157 (level0Relator 1) (level0_relator 1))

theorem edge861Inv : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(true, false)], 213⟩ :=
  holds_reverse edge861

theorem edge862 : Holds level0Subgroup PresentedGroup.of representative ⟨215, [(true, true)], 216⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨158, [(true, true)], 215⟩ :=
    edge214
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(true, true)], 158⟩ :=
    edge215Inv
  exact scanFacts hp hs (holds_relator 158 (level0Relator 1) (level0_relator 1))

theorem edge862Inv : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(true, false)], 215⟩ :=
  holds_reverse edge862

theorem edge863 : Holds level0Subgroup PresentedGroup.of representative ⟨217, [(true, true)], 218⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨159, [(true, true)], 217⟩ :=
    edge216
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(true, true)], 159⟩ :=
    edge217Inv
  exact scanFacts hp hs (holds_relator 159 (level0Relator 1) (level0_relator 1))

theorem edge863Inv : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(true, false)], 217⟩ :=
  holds_reverse edge863

theorem edge864 : Holds level0Subgroup PresentedGroup.of representative ⟨219, [(true, true)], 220⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨160, [(true, true)], 219⟩ :=
    edge218
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(true, true)], 160⟩ :=
    edge219Inv
  exact scanFacts hp hs (holds_relator 160 (level0Relator 1) (level0_relator 1))

theorem edge864Inv : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(true, false)], 219⟩ :=
  holds_reverse edge864

theorem edge865 : Holds level0Subgroup PresentedGroup.of representative ⟨221, [(true, true)], 222⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨161, [(true, true)], 221⟩ :=
    edge220
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(true, true)], 161⟩ :=
    edge221Inv
  exact scanFacts hp hs (holds_relator 161 (level0Relator 1) (level0_relator 1))

theorem edge865Inv : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(true, false)], 221⟩ :=
  holds_reverse edge865

theorem edge866 : Holds level0Subgroup PresentedGroup.of representative ⟨223, [(true, true)], 224⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(true, true)], 223⟩ :=
    edge222
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(true, true)], 162⟩ :=
    edge223Inv
  exact scanFacts hp hs (holds_relator 162 (level0Relator 1) (level0_relator 1))

theorem edge866Inv : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(true, false)], 223⟩ :=
  holds_reverse edge866

theorem edge867 : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(false, true)], 222⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨162, [(false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 222⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge824 (appendFacts edge119Inv edge771)) (appendFacts edge63Inv (appendFacts edge742 edge33Inv))) (appendFacts (appendFacts edge727 (appendFacts edge17Inv edge717)) (appendFacts edge7Inv (appendFacts edge712 edge710Inv)))) (appendFacts (appendFacts (appendFacts edge3 (appendFacts edge6 edge10)) (appendFacts edge16 (appendFacts edge23 edge32))) (appendFacts (appendFacts edge44 (appendFacts edge62 edge85)) (appendFacts edge118 (appendFacts edge160 edge221)))))
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(true, false), (false, true), (true, false)], 162⟩ :=
    (appendFacts edge865Inv (appendFacts edge700 edge222Inv))
  exact scanFacts hp hs (holds_relator 162 (level0Relator 2) (level0_relator 2))

theorem edge867Inv : Holds level0Subgroup PresentedGroup.of representative ⟨222, [(false, false)], 222⟩ :=
  holds_reverse edge867

theorem edge868 : Holds level0Subgroup PresentedGroup.of representative ⟨225, [(true, true)], 226⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨163, [(true, true)], 225⟩ :=
    edge224
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(true, true)], 163⟩ :=
    edge225Inv
  exact scanFacts hp hs (holds_relator 163 (level0Relator 1) (level0_relator 1))

theorem edge868Inv : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(true, false)], 225⟩ :=
  holds_reverse edge868

theorem edge869 : Holds level0Subgroup PresentedGroup.of representative ⟨227, [(true, true)], 228⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨164, [(true, true)], 227⟩ :=
    edge226
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(true, true)], 164⟩ :=
    edge227Inv
  exact scanFacts hp hs (holds_relator 164 (level0Relator 1) (level0_relator 1))

theorem edge869Inv : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(true, false)], 227⟩ :=
  holds_reverse edge869

theorem edge870 : Holds level0Subgroup PresentedGroup.of representative ⟨229, [(true, true)], 230⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨165, [(true, true)], 229⟩ :=
    edge228
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(true, true)], 165⟩ :=
    edge229Inv
  exact scanFacts hp hs (holds_relator 165 (level0Relator 1) (level0_relator 1))

theorem edge870Inv : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(true, false)], 229⟩ :=
  holds_reverse edge870

theorem edge871 : Holds level0Subgroup PresentedGroup.of representative ⟨231, [(true, true)], 232⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨166, [(true, true)], 231⟩ :=
    edge230
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(true, true)], 166⟩ :=
    edge231Inv
  exact scanFacts hp hs (holds_relator 166 (level0Relator 1) (level0_relator 1))

theorem edge871Inv : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(true, false)], 231⟩ :=
  holds_reverse edge871

theorem edge872 : Holds level0Subgroup PresentedGroup.of representative ⟨233, [(true, true)], 234⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨167, [(true, true)], 233⟩ :=
    edge232
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(true, true)], 167⟩ :=
    edge233Inv
  exact scanFacts hp hs (holds_relator 167 (level0Relator 1) (level0_relator 1))

theorem edge872Inv : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(true, false)], 233⟩ :=
  holds_reverse edge872

theorem edge873 : Holds level0Subgroup PresentedGroup.of representative ⟨235, [(true, true)], 236⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨168, [(true, true)], 235⟩ :=
    edge234
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(true, true)], 168⟩ :=
    edge235Inv
  exact scanFacts hp hs (holds_relator 168 (level0Relator 1) (level0_relator 1))

theorem edge873Inv : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(true, false)], 235⟩ :=
  holds_reverse edge873

theorem edge874 : Holds level0Subgroup PresentedGroup.of representative ⟨237, [(true, true)], 238⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨170, [(true, true)], 237⟩ :=
    edge236
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(true, true)], 170⟩ :=
    edge237Inv
  exact scanFacts hp hs (holds_relator 170 (level0Relator 1) (level0_relator 1))

theorem edge874Inv : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(true, false)], 237⟩ :=
  holds_reverse edge874

theorem edge875 : Holds level0Subgroup PresentedGroup.of representative ⟨239, [(true, true)], 240⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨171, [(true, true)], 239⟩ :=
    edge238
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(true, true)], 171⟩ :=
    edge239Inv
  exact scanFacts hp hs (holds_relator 171 (level0Relator 1) (level0_relator 1))

theorem edge875Inv : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(true, false)], 239⟩ :=
  holds_reverse edge875

theorem edge876 : Holds level0Subgroup PresentedGroup.of representative ⟨241, [(true, true)], 242⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨172, [(true, true)], 241⟩ :=
    edge240
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨242, [(true, true)], 172⟩ :=
    edge241Inv
  exact scanFacts hp hs (holds_relator 172 (level0Relator 1) (level0_relator 1))

theorem edge876Inv : Holds level0Subgroup PresentedGroup.of representative ⟨242, [(true, false)], 241⟩ :=
  holds_reverse edge876

theorem edge877 : Holds level0Subgroup PresentedGroup.of representative ⟨243, [(true, true)], 244⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨173, [(true, true)], 243⟩ :=
    edge242
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(true, true)], 173⟩ :=
    edge243Inv
  exact scanFacts hp hs (holds_relator 173 (level0Relator 1) (level0_relator 1))

theorem edge877Inv : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(true, false)], 243⟩ :=
  holds_reverse edge877

theorem edge878 : Holds level0Subgroup PresentedGroup.of representative ⟨245, [(true, true)], 246⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨174, [(true, true)], 245⟩ :=
    edge244
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(true, true)], 174⟩ :=
    edge245Inv
  exact scanFacts hp hs (holds_relator 174 (level0Relator 1) (level0_relator 1))

theorem edge878Inv : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(true, false)], 245⟩ :=
  holds_reverse edge878

theorem edge879 : Holds level0Subgroup PresentedGroup.of representative ⟨247, [(true, true)], 248⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨175, [(true, true)], 247⟩ :=
    edge246
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(true, true)], 175⟩ :=
    edge247Inv
  exact scanFacts hp hs (holds_relator 175 (level0Relator 1) (level0_relator 1))

theorem edge879Inv : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(true, false)], 247⟩ :=
  holds_reverse edge879

theorem edge880 : Holds level0Subgroup PresentedGroup.of representative ⟨249, [(true, true)], 250⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨176, [(true, true)], 249⟩ :=
    edge248
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(true, true)], 176⟩ :=
    edge249Inv
  exact scanFacts hp hs (holds_relator 176 (level0Relator 1) (level0_relator 1))

theorem edge880Inv : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(true, false)], 249⟩ :=
  holds_reverse edge880

theorem edge881 : Holds level0Subgroup PresentedGroup.of representative ⟨251, [(true, true)], 252⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨177, [(true, true)], 251⟩ :=
    edge250
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(true, true)], 177⟩ :=
    edge251Inv
  exact scanFacts hp hs (holds_relator 177 (level0Relator 1) (level0_relator 1))

theorem edge881Inv : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(true, false)], 251⟩ :=
  holds_reverse edge881

theorem edge882 : Holds level0Subgroup PresentedGroup.of representative ⟨253, [(true, true)], 254⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨178, [(true, true)], 253⟩ :=
    edge252
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(true, true)], 178⟩ :=
    edge253Inv
  exact scanFacts hp hs (holds_relator 178 (level0Relator 1) (level0_relator 1))

theorem edge882Inv : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(true, false)], 253⟩ :=
  holds_reverse edge882

theorem edge883 : Holds level0Subgroup PresentedGroup.of representative ⟨255, [(true, true)], 256⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨179, [(true, true)], 255⟩ :=
    edge254
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(true, true)], 179⟩ :=
    edge255Inv
  exact scanFacts hp hs (holds_relator 179 (level0Relator 1) (level0_relator 1))

theorem edge883Inv : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(true, false)], 255⟩ :=
  holds_reverse edge883

theorem edge884 : Holds level0Subgroup PresentedGroup.of representative ⟨257, [(true, true)], 258⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨180, [(true, true)], 257⟩ :=
    edge256
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(true, true)], 180⟩ :=
    edge257Inv
  exact scanFacts hp hs (holds_relator 180 (level0Relator 1) (level0_relator 1))

theorem edge884Inv : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(true, false)], 257⟩ :=
  holds_reverse edge884

theorem edge885 : Holds level0Subgroup PresentedGroup.of representative ⟨259, [(true, true)], 260⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨181, [(true, true)], 259⟩ :=
    edge258
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(true, true)], 181⟩ :=
    edge259Inv
  exact scanFacts hp hs (holds_relator 181 (level0Relator 1) (level0_relator 1))

theorem edge885Inv : Holds level0Subgroup PresentedGroup.of representative ⟨260, [(true, false)], 259⟩ :=
  holds_reverse edge885

theorem edge886 : Holds level0Subgroup PresentedGroup.of representative ⟨261, [(true, true)], 262⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨182, [(true, true)], 261⟩ :=
    edge260
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(true, true)], 182⟩ :=
    edge261Inv
  exact scanFacts hp hs (holds_relator 182 (level0Relator 1) (level0_relator 1))

theorem edge886Inv : Holds level0Subgroup PresentedGroup.of representative ⟨262, [(true, false)], 261⟩ :=
  holds_reverse edge886

theorem edge887 : Holds level0Subgroup PresentedGroup.of representative ⟨263, [(true, true)], 264⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨183, [(true, true)], 263⟩ :=
    edge262
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(true, true)], 183⟩ :=
    edge263Inv
  exact scanFacts hp hs (holds_relator 183 (level0Relator 1) (level0_relator 1))

theorem edge887Inv : Holds level0Subgroup PresentedGroup.of representative ⟨264, [(true, false)], 263⟩ :=
  holds_reverse edge887

theorem edge888 : Holds level0Subgroup PresentedGroup.of representative ⟨265, [(false, true)], 184⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨184, [(false, true)], 265⟩ :=
    edge264
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨184, [], 184⟩ :=
    (holds_refl 184)
  exact scanFacts hp hs (holds_relator 184 (level0Relator 0) (level0_relator 0))

theorem edge888Inv : Holds level0Subgroup PresentedGroup.of representative ⟨184, [(false, false)], 265⟩ :=
  holds_reverse edge888

theorem edge889 : Holds level0Subgroup PresentedGroup.of representative ⟨266, [(false, true)], 185⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(false, true)], 266⟩ :=
    edge265
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨185, [], 185⟩ :=
    (holds_refl 185)
  exact scanFacts hp hs (holds_relator 185 (level0Relator 0) (level0_relator 0))

theorem edge889Inv : Holds level0Subgroup PresentedGroup.of representative ⟨185, [(false, false)], 266⟩ :=
  holds_reverse edge889

theorem edge890 : Holds level0Subgroup PresentedGroup.of representative ⟨267, [(false, true)], 186⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨186, [(false, true)], 267⟩ :=
    edge266
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨186, [], 186⟩ :=
    (holds_refl 186)
  exact scanFacts hp hs (holds_relator 186 (level0Relator 0) (level0_relator 0))

theorem edge890Inv : Holds level0Subgroup PresentedGroup.of representative ⟨186, [(false, false)], 267⟩ :=
  holds_reverse edge890

theorem edge891 : Holds level0Subgroup PresentedGroup.of representative ⟨268, [(false, true)], 187⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(false, true)], 268⟩ :=
    edge267
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨187, [], 187⟩ :=
    (holds_refl 187)
  exact scanFacts hp hs (holds_relator 187 (level0Relator 0) (level0_relator 0))

theorem edge891Inv : Holds level0Subgroup PresentedGroup.of representative ⟨187, [(false, false)], 268⟩ :=
  holds_reverse edge891

theorem edge892 : Holds level0Subgroup PresentedGroup.of representative ⟨269, [(false, true)], 188⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨188, [(false, true)], 269⟩ :=
    edge268
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨188, [], 188⟩ :=
    (holds_refl 188)
  exact scanFacts hp hs (holds_relator 188 (level0Relator 0) (level0_relator 0))

theorem edge892Inv : Holds level0Subgroup PresentedGroup.of representative ⟨188, [(false, false)], 269⟩ :=
  holds_reverse edge892

theorem edge893 : Holds level0Subgroup PresentedGroup.of representative ⟨270, [(false, true)], 189⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(false, true)], 270⟩ :=
    edge269
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨189, [], 189⟩ :=
    (holds_refl 189)
  exact scanFacts hp hs (holds_relator 189 (level0Relator 0) (level0_relator 0))

theorem edge893Inv : Holds level0Subgroup PresentedGroup.of representative ⟨189, [(false, false)], 270⟩ :=
  holds_reverse edge893

theorem edge894 : Holds level0Subgroup PresentedGroup.of representative ⟨271, [(false, true)], 190⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨190, [(false, true)], 271⟩ :=
    edge270
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨190, [], 190⟩ :=
    (holds_refl 190)
  exact scanFacts hp hs (holds_relator 190 (level0Relator 0) (level0_relator 0))

theorem edge894Inv : Holds level0Subgroup PresentedGroup.of representative ⟨190, [(false, false)], 271⟩ :=
  holds_reverse edge894

theorem edge895 : Holds level0Subgroup PresentedGroup.of representative ⟨272, [(false, true)], 191⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(false, true)], 272⟩ :=
    edge271
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨191, [], 191⟩ :=
    (holds_refl 191)
  exact scanFacts hp hs (holds_relator 191 (level0Relator 0) (level0_relator 0))

theorem edge895Inv : Holds level0Subgroup PresentedGroup.of representative ⟨191, [(false, false)], 272⟩ :=
  holds_reverse edge895


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
