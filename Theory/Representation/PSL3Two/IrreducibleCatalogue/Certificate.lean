module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
import Mathlib.Tactic

/-!
# A checked spanning certificate for the binary adjoint action

Sixty-four words in the actual cycle and transvection action matrices span
all endomorphisms of the eight-dimensional adjoint space. Each word is checked
against its packed matrix, and an explicit inverse coefficient table expresses
every matrix unit as their linear combination. Kernel reduction verifies both
finite identities; the witness data alone is never used as a proof.

This supplies the absolute irreducibility ingredient of Aschbacher–Smith H.6.1,
printed p.386 of the combined manuscript of 1 March 2004.
-/

@[expose] public section

open Matrix
namespace BinaryLinearThree.IrreducibleCatalogue
namespace Certificate

private def words : Fin 64 → List Bool := ![[],
    [false],
    [true],
    [false, false],
    [true, false],
    [false, true],
    [true, false, false],
    [false, true, false],
    [false, false, true],
    [true, false, true],
    [false, true, false, false],
    [false, false, true, false],
    [true, false, true, false],
    [true, false, false, true],
    [false, true, false, true],
    [false, false, true, false, false],
    [true, false, true, false, false],
    [true, false, false, true, false],
    [false, true, false, true, false],
    [false, true, false, false, true],
    [false, false, true, false, true],
    [true, false, true, false, true],
    [true, false, false, true, false, false],
    [false, true, false, true, false, false],
    [false, true, false, false, true, false],
    [false, false, true, false, true, false],
    [true, false, true, false, true, false],
    [false, false, true, false, false, true],
    [true, false, true, false, false, true],
    [true, false, false, true, false, true],
    [false, true, false, true, false, true],
    [false, true, false, false, true, false, false],
    [true, false, true, false, true, false, false],
    [false, false, true, false, false, true, false],
    [true, false, true, false, false, true, false],
    [true, false, false, true, false, true, false],
    [false, true, false, true, false, true, false],
    [true, false, false, true, false, false, true],
    [false, true, false, true, false, false, true],
    [false, false, true, false, true, false, true],
    [true, false, true, false, false, true, false, false],
    [false, true, false, true, false, true, false, false],
    [true, false, false, true, false, false, true, false],
    [false, true, false, true, false, false, true, false],
    [false, false, true, false, true, false, true, false],
    [false, true, false, false, true, false, false, true],
    [true, false, true, false, true, false, false, true],
    [false, true, false, true, false, false, true, false, false],
    [false, false, true, false, true, false, true, false, false],
    [false, true, false, false, true, false, false, true, false],
    [true, false, true, false, true, false, false, true, false],
    [true, false, true, false, false, true, false, false, true],
    [false, true, false, true, false, true, false, false, true],
    [true, false, true, false, true, false, false, true, false, false],
    [true, false, true, false, false, true, false, false, true, false],
    [false, true, false, true, false, true, false, false, true, false],
    [false, true, false, true, false, false, true, false, false, true],
    [false, false, true, false, true, false, true, false, false, true],
    [false, true, false, true, false, true, false, false, true, false, false],
    [false, true, false, true, false, false, true, false, false, true, false],
    [false, false, true, false, true, false, true, false, false, true, false],
    [true, false, true, false, true, false, false, true, false, false, true],
    [false, false, true, false, true, false, true, false, false, true, false, false],
    [true, false, true, false, true, false, false, true, false, false, true, false]]

private def packed : Fin 64 → ℕ := ![9241421688590303745,
    4665731417544590344,
    9313760895090098689,
    13871091284724293648,
    4737789012119438602,
    5244443978327655432,
    13871584974035099696,
    14447552037061306388,
    15028516406680494096,
    5461179714169980170,
    9243823039165235715,
    10394343193264280097,
    14592160914447969269,
    17343861133390585904,
    15894333437358549012,
    4670323115541136396,
    9316729323082023427,
    12772525412215780129,
    10684974919990927019,
    9460840967810515459,
    12781532609577832993,
    4572497017367735285,
    4751424193254442447,
    5250175354486129676,
    5460616763260063498,
    7048223719329690974,
    8379980603894119592,
    5538392295981450252,
    9387941843604079107,
    10403350395472868129,
    4603708770893389483,
    14448619671441811644,
    5422259910239569359,
    15893207536511400980,
    5245006929522789384,
    6985209607893292220,
    16419102433183560530,
    10250038077059679695,
    4958567596366496780,
    4579688528275830110,
    14592238971183606622,
    15870530410776537276,
    4589666989499440885,
    15029642310144897040,
    10282269210274090949,
    8376642279832922300,
    9579363202308818383,
    10683717061508882165,
    12772155514854658675,
    4560924576368817579,
    17326691159597912112,
    10726461626629008222,
    6954528835211733180,
    8395853407155764244,
    15873125306950489256,
    9503625164650381571,
    7039460607931801333,
    14000792983646524019,
    16384096559935550241,
    12812845346769084754,
    5516437247631493132,
    6958079155844004884,
    10286793348435070730,
    10444054330495476083]

private def inverseColumns : Fin 64 → ℕ := ![8430208349073803317,
    423477367066764,
    328756296303345,
    16489201566665658422,
    14312216011730892504,
    422226148836982,
    10773972533421536214,
    16237700106465589706,
    1760133306022791826,
    16489067271505912817,
    14311770711635668441,
    1531277525853833372,
    5412312470141515998,
    8430630609114549827,
    54927260651498584,
    1783622154858498466,
    244105424700618458,
    14312213806224579900,
    8429926884686865729,
    1088641414654549965,
    6403874788051056259,
    16489061960858566854,
    7489224989658217,
    223815446671798401,
    16489070726938267884,
    32025588511037,
    765354738830652,
    14312210602032341477,
    8430630484091554486,
    26436110981162,
    3396074547328163457,
    14672461072350048568,
    14312219035250355757,
    6333379278609,
    704247177538361,
    8430629740412391032,
    16489061923048338746,
    863430713852,
    13695529963945725187,
    8713823411605265933,
    5593210125978590236,
    8430630690421950521,
    16489017939616806712,
    5223992031866522638,
    1690712919475779753,
    14312219310689585105,
    318891306417570970,
    5332215784128058499,
    3849172004912426,
    4107928963134041347,
    11581497143469189985,
    109087732459775801,
    1376791198362459964,
    10028681115385010678,
    2471340214972174818,
    10388357687034622970,
    31296688045877212,
    18200450943734250370,
    15447100604370337976,
    973256965356843642,
    5466377759739975629,
    7852054634317919105,
    12853837837840053137,
    2470483760321842280]

private def storedMatrix (k : Fin 64) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => if (packed k).testBit (8 * j.val + i.val) then 1 else 0

private def matrixWord : List Bool → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | [] => 1
  | b :: bs => (if b then shearMatrix else cycleMatrix) * matrixWord bs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem words_checked : ∀ k : Fin 64, matrixWord (words k) = storedMatrix k := by
  decide +kernel

private def coefficient (i j : Fin 8) (k : Fin 64) : ZMod 2 :=
  if (inverseColumns ⟨8 * j.val + i.val, by omega⟩).testBit k.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem inverse_checked : ∀ i j : Fin 8,
    (∑ k : Fin 64, coefficient i j k • storedMatrix k) = Matrix.single i j 1 := by
  decide +kernel

private theorem matrixWord_mem (A : Subalgebra (ZMod 2) (Matrix (Fin 8) (Fin 8) (ZMod 2)))
    (hc : cycleMatrix ∈ A) (ht : shearMatrix ∈ A) (w : List Bool) : matrixWord w ∈ A := by
  induction w with
  | nil => exact A.one_mem
  | cons b bs ih =>
    apply A.mul_mem _ ih
    cases b
    · exact hc
    · exact ht

theorem matrix_algebra_eq_top (A : Subalgebra (ZMod 2) (Matrix (Fin 8) (Fin 8) (ZMod 2)))
    (hc : cycleMatrix ∈ A) (ht : shearMatrix ∈ A) : A = ⊤ := by
  have hunit (i j : Fin 8) : Matrix.single i j (1 : ZMod 2) ∈ A := by
    rw [← inverse_checked i j]
    apply A.sum_mem
    intro k _
    apply A.smul_mem
    rw [← words_checked]
    exact matrixWord_mem A hc ht _
  apply top_unique
  intro M _
  have hM : M = ∑ i : Fin 8, ∑ j : Fin 8, M i j • Matrix.single i j 1 := by
    simpa using Matrix.matrix_eq_sum_single M
  rw [hM]
  apply A.sum_mem
  intro i _
  apply A.sum_mem
  intro j _
  exact A.smul_mem (hunit i j) (M i j)

end Certificate
end BinaryLinearThree.IrreducibleCatalogue
