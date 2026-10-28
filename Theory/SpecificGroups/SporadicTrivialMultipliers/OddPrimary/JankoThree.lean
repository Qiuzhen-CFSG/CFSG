module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices
public import Theory.GroupTheory.PerfectCentralCoverSylowNine.OddInversion
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.FusionProducts
/-!
# Three-primary kernels over the concrete Janko4 carrier

The existing 27 normal forms prove generation, order and central-commutator
relations. The first literal U3(3) program output inverts both generators:
one product identity is already in the fusion certificates; the other two
packed products are checked here in the Lean kernel. The exact ambient
order makes this subgroup Sylow, so simultaneous-inversion transfer excludes
three from finite perfect central kernels.

Source: Aschbacher–Smith I.1.3, printed p.407; ATLAS J4G1-max10W1 and the
original matrix certificates in `Simplicity.PrimeCoverage.Threes`.
-/

open Subgroup
open scoped commutatorElement
open Janko4.GeneratorCertificates Janko4.Simplicity.ThreeLocalCertificates
namespace Janko4.OddPrimary
private def inversionProduct : Vector Nat 112 :=
  ⟨#[3823150381756962203362483337859924,
    4741543149385883864845949831167191,
    2281819086318252564006138695470600,
    4303746317350132424910822664962445,
    3577292094832257179528318153185823,
    2534126465133185676680054064444032,
    3608414277305633891592094259672191,
    159089380777236977446377219656696,
    5105918355132539272783265361542140,
    561080417980564959500352294379675,
    1422213900991278778813828501370581,
    412293163700803665945203006299980,
    2845451829200360583943436419378496,
    4918060816184498411739043775263809,
    4790232323526456707887889045932654,
    2571683049970334698618866527003602,
    3949340290526129627951361308992459,
    4842060413161150981314563035497970,
    2777706106891024510886161894841073,
    821788007320250702630936959797884,
    1948520598918553760078960138005009,
    2323415732409093046187603089579116,
    1409737503085834931951387818807952,
    2851152366627289595297168426064088,
    1020394769919059743740854013553788,
    4624072442769021937869155926829836,
    56575268646625928232513315294688,
    1821198871609397633693984214473595,
    2829998075776003996730584528543045,
    1553834339681113066301375954696027,
    2565414562766215291109981219937283,
    566698654104905148063939234928771,
    685166467547581566370861007135222,
    3838673694590558673091691098280182,
    4726334891820045224257273720008279,
    3073535335611477820842488172734470,
    3440249263011008542460297754312348,
    4140858676475883787631062064857802,
    3649437820202978448988478242612733,
    2509185753926393680930791201899765,
    2170481814018247043773711071555690,
    1604620050268997172782901114383076,
    363479637897822266544834880721118,
    1144894524715908363790607704286416,
    4670213586712317176177869240051133,
    1754736298068839780737699624447608,
    1810177060593837099508205661304461,
    874862058874244403980974452850064,
    2339637448548687046472918098875499,
    2043303051054685019529811939117188,
    1519751715922518754015190899294668,
    1404675860487425688440528825033487,
    832680316804999035169202599226181,
    2027391712915002905598367287651122,
    183501967371151995766645060328542,
    3475750021213269322447829733559980,
    1628461437365816282272688766095911,
    833839108521644786997013944045595,
    4465731184734312004658948951034952,
    1294864765730627035348273839531397,
    728575015535818997338918683421722,
    1410696191900711020590434760447449,
    1915751985318612271845670146635281,
    1437637386774806978452357806374646,
    2705641005189687611871356757961069,
    2141519338040154136776855843043102,
    1142502212569317265828209821892354,
    1041549306944761265464429908672458,
    1854101511054236213072332091971658,
    570416185123530751288125223742130,
    4247597104762962153425855939214038,
    1831391668408009909078177423942032,
    1544486909193419713449938565124123,
    452552272150081259680878680417160,
    1503639880121490233624340950839906,
    3445038509739733185968393041972804,
    1457544045185378865989570662843662,
    4305869484131310901541965865855381,
    3306603299581147752265889114323345,
    1241429190433325564158240282947790,
    4415624799647253285627281967777371,
    229229979782296485124475480764822,
    3326531792103787919675051585853356,
    2730894154841094861155690710824327,
    1598878676669732559022838076732903,
    1804256887644175725669425716191765,
    1388539979178150389386620401700286,
    4628042121063191103791945978649469,
    331760408107526911253410522505333,
    3579597208299951914780024882592124,
    1262591391015387792290295064897463,
    3955634181482162411874128202643621,
    2409347368750973499891815273567181,
    5068453707769332203801348821719829,
    487008262990516341225616880247664,
    2778704191413192833715189179556778,
    4967466927371991007158271983887330,
    4153427630382062518747065756427864,
    1989007946393642379578909450393431,
    4026630667969746358475470301181079,
    4122737070269678591783293260389524,
    1664793549631808742794085378032546,
    2464257385941779414463847328376393,
    453601875333488761554281812800082,
    3099119292387412679711015784921107,
    1992938033674808581653952229763333,
    86452319807378234856482159017070,
    1849602643206977702180365190688204,
    675923624581376312036703879463599,
    1799510500281547903188047384978577,
    1915190063208227649158640706862251,
    2674418318869194045838652430846356], by decide⟩
private theorem inversion_left : packedMul programFstRows vRows = inversionProduct :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
private theorem inversion_right : packedMul normal020Rows programFstRows = inversionProduct :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

open Simplicity Simplicity.ThreeLocalCertificates.Conjugacy

public theorem exists_three_configuration :
    ∃ (Q : Sylow 3 Model) (x y r : Model),
      closure ({x, y} : Set Model) = (Q : Subgroup Model) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let hA := matrixA_mul_self
  let hB := matrixB_pow_four
  let x := threeLocalU hA hB
  let y := threeLocalV hA hB
  let z := threeLocalZ hA hB
  let r := (threeLocalProgram (Simplicity.a hA) (Simplicity.b hB)).1
  have hx : x ^ 3 = 1 := by
    simpa [threeLocalNormalForm, ← pow_succ] using threeLocalNormalForm_mul_u hA hB (2,0,0)
  have hy : y ^ 3 = 1 := by
    simpa [threeLocalNormalForm, ← pow_succ] using threeLocalNormalForm_mul_v hA hB (0,2,0)
  have hxz : Commute x z := by
    apply Commute.symm
    change z * x = x * z
    simpa [threeLocalNormalForm] using threeLocalNormalForm_mul_u hA hB (0,0,1)
  have hyz : Commute y z := by
    apply Commute.symm
    change z * y = y * z
    simpa [threeLocalNormalForm] using threeLocalNormalForm_mul_v hA hB (0,0,1)
  have hxy : ⁅x, y⁆ = z := by
    calc
      ⁅x, y⁆ = (y * x) * z * (y * x)⁻¹ := by
        dsimp [z, threeLocalZ, x, y]
        simp only [commutatorElement_def]
        group
      _ = z := by rw [(hyz.mul_left hxz).eq, mul_inv_cancel_right]
  have hz : z ≠ 1 := by
    intro hh
    have he : threeLocalNormalForm hA hB (0,0,1) =
        threeLocalNormalForm hA hB (0,0,0) := by simpa [threeLocalNormalForm] using hh
    have hh := threeLocalNormalForm_injective hA hB he
    exact (by decide : (0,0,1) ≠ ((0,0,0) : Fin 3 × Fin 3 × Fin 3)) hh
  have hx2 : x ^ 2 = x⁻¹ := by
    apply mul_right_cancel (b := x)
    simpa [← pow_succ] using hx
  have hy2 : y ^ 2 = y⁻¹ := by
    apply mul_right_cancel (b := y)
    simpa [← pow_succ] using hy
  have hrx : r * x * r⁻¹ = x⁻¹ := by
    have he : x * r = r * x ^ 2 := by
      apply toMatrix_injective
      rw [map_mul, map_mul, u_matrix, program_fst_matrix]
      have hm := normalForm_matrix hA hB (2,0,0)
      simp only [threeLocalNormalForm, Fin.val_two, Fin.val_zero, pow_zero, mul_one] at hm
      rw [hm, ← decode_packedMul, ← decode_packedMul, show normalRows (2,0,0) = normal200Rows from rfl, fusion200_left, fusion200_right]
    have he' : r * x⁻¹ = x * r := by rw [← hx2]; exact he.symm
    have hh : x = r * x⁻¹ * r⁻¹ := by rw [he', mul_inv_cancel_right]
    have hi := congrArg (fun a : Model => a⁻¹) hh
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi.symm
  have hry : r * y * r⁻¹ = y⁻¹ := by
    have he : r * y = y ^ 2 * r := by
      apply toMatrix_injective
      rw [map_mul, map_mul, program_fst_matrix, v_matrix]
      have hm := normalForm_matrix hA hB (0,2,0)
      simp only [threeLocalNormalForm, Fin.val_two, Fin.val_zero, pow_zero, one_mul, mul_one] at hm
      rw [hm, ← decode_packedMul, ← decode_packedMul, show normalRows (0,2,0) = normal020Rows from rfl, inversion_left, inversion_right]
    rw [he, hy2, mul_inv_cancel_right]
  have hrz : Commute r z := by
    have hh : r * z * r⁻¹ = z := by
      rw [← hxy, conjugate_commutatorElement, hrx, hry]
      calc
        ⁅x⁻¹, y⁻¹⁆ = z := by
          change x⁻¹ * y⁻¹ * (x⁻¹)⁻¹ * (y⁻¹)⁻¹ = z
          simp only [inv_inv]
          rfl
        _ = ⁅x, y⁆ := hxy.symm
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hc := threeLocal_card hA hB
  have hp : IsPGroup 3 (threeLocalSubgroup hA hB) := IsPGroup.of_card (n := 3) hc
  have hi : ¬3 ∣ (threeLocalSubgroup hA hB).index := by
    intro hi
    have hd : 3 ^ 4 ∣ Nat.card Model := by
      rw [← (threeLocalSubgroup hA hB).card_mul_index, hc]
      exact Nat.mul_dvd_mul_left 27 hi
    rw [Cardinality.Thompson.model_card] at hd
    norm_num at hd
  exact ⟨hp.toSylow hi, x, y, r, rfl, hx, hy, hxy ▸ hz,
    hxy ▸ hxz, hxy ▸ hyz, hrx, hry, hxy ▸ hrz⟩

public theorem not_three_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ := exists_three_configuration
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two
    f hf hk (by decide : 3 ≠ 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end Janko4.OddPrimary

