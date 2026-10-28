module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstCubic
public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupTheory.PGroup.HeisenbergPair

/-!
# Excluding the triple Mathieu quotient at the first flag normalizer

In the existing binary matrix model of 3.M₂₂, put A=CD and B=D², using
the published ATLAS generators. The words x=(ABA⁴B)² and g=ABA⁶BA⁷B,
with y=gxg⁻¹, have order three and commutator equal to the square of the
published central scalar. Small kernel-checked matrix products certify
these relations. The Heisenberg-pair theorem gives a subgroup of order
27 and exponent three; the existing group order makes it Sylow. Hence
no element of the cover has order nine.

Recognition of the actual central cover and the proved outer bound now
force every cubic actor into a normal C-component of this type in a group
of three-rank at most two. The proof passes through the ambient two-core
quotient and reflects membership using the original two-group supplement.
In the first flag normalizer, that contradicts the faithful order-three
Cartan factor. All relative subgroup and intrinsic quotient maps are kept.

The preceding flag model, L₁-centralization and Cartan faithfulness remain
with qt-d-1222-natural-flag-cartan, with ultimate discharge by
qt-d-1222-natural-local-geometry. The relative-components owner retains the
other model rows and full source-family assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
A.3.18, printed pp.51--52, and 11.1.2, printed pp.761--762.
The binary generator data and original attribution to R. A. Wilson,
S. J. Nickerson and J. N. Bray are preserved in
`Theory/SpecificGroups/Janko4/Model/AutomorphismReduction/FixedGenerator/
NormalizerSquares/LocalAction/TwoCoreNormalizer/LinearModel/source/README.md`.
All added matrices below are products of those unchanged generators.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
private abbrev Triple := Sporadic.Mathieu.M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private def mx : Matrix12 := fromRows ![654,2394,1413,1190,432,1291,2877,2259,2803,549,1060,523]
private def mg : Matrix12 := fromRows ![1930,2869,2109,3476,786,3319,2023,3468,3083,31,3129,1685]
private def mgi : Matrix12 := fromRows ![3970,158,3476,1890,2026,628,1857,2313,2561,3429,2448,238]
private def my : Matrix12 := fromRows ![1593,2734,271,610,3944,1040,987,2835,3888,579,4081,3387]
private def ma2 : Matrix12 := fromRows ![128,28,412,2976,1639,4,400,2891,2823,1513,1412,1499]
private def ma4 : Matrix12 := fromRows ![2891,3163,3095,122,249,412,1579,409,2613,3964,1108,2307]
private def ma6 : Matrix12 := fromRows ![409,3220,1848,3151,1944,3095,2901,3339,1869,894,1007,3648]
private def ma7 : Matrix12 := fromRows ![3151,1848,3311,3339,1869,3220,482,2927,3558,1256,3648,3729]
private def mab : Matrix12 := fromRows ![8,31,22,938,2666,2,4,202,3356,32,64,1412]
private def mxa : Matrix12 := fromRows ![122,2948,181,2413,3561,3163,3095,2963,3062,412,1579,1007]
private def mxb : Matrix12 := fromRows ![2817,991,174,295,3785,1024,3095,979,2262,2518,1291,2191]
private def mga : Matrix12 := fromRows ![3151,482,3124,1524,2727,3220,1848,1669,1549,3095,2901,3729]
private def mgb : Matrix12 := fromRows ![1054,712,3855,3727,2733,4015,3954,1470,1564,3095,2148,1504]
private def mgc : Matrix12 := fromRows ![4049,878,844,1477,41,1207,1244,1484,3073,4,3848,1471]
private def mgx : Matrix12 := fromRows ![2525,2413,1309,58,60,3883,1094,1324,2397,2887,1212,2153]
private def mx2 : Matrix12 := fromRows ![655,3977,271,1315,1691,421,3531,2945,3247,37,1194,3415]
private def mzy : Matrix12 := fromRows ![28,3957,3869,1931,1538,4073,1209,163,634,833,312,3012]
private def x : Triple := (coreGeneratorA * coreGeneratorB * coreGeneratorA^4 * coreGeneratorB)^2
private def g : Triple := coreGeneratorA * coreGeneratorB * coreGeneratorA^6 * coreGeneratorB * coreGeneratorA^7 * coreGeneratorB
private def y : Triple := g*x*g⁻¹
private def z : Triple := coreScalar^2

private def value : Triple →* Matrix12 := (Units.coeHom Matrix12).comp derivedGroup.subtype

private theorem value_injective : Function.Injective value :=
  Units.val_injective.comp derivedGroup.subtype_injective
private theorem value_A : value coreGeneratorA=matrixA := coe_coreA
private theorem value_B : value coreGeneratorB=matrixB := coe_coreB

private theorem a4_matrix : matrixA^4=ma4 := by
  have h2 : matrixA*matrixA=ma2 := by decide +kernel
  have h4 : ma2*ma2=ma4 := by decide +kernel
  simpa only [show (4:ℕ)=2+2 from rfl,pow_add,pow_two,h2] using h4

private theorem a6_matrix : matrixA^6=ma6 := by
  have h2 : matrixA*matrixA=ma2 := by decide +kernel
  have h6 : ma4*ma2=ma6 := by decide +kernel
  simpa only [show (6:ℕ)=4+2 from rfl,pow_add,a4_matrix,pow_two,h2] using h6

private theorem a7_matrix : matrixA^7=ma7 := by
  have h : ma6*matrixA=ma7 := by decide +kernel
  simpa only [show (7:ℕ)=6+1 from rfl,pow_add,pow_one,a6_matrix] using h

private theorem x_matrix : value x = mx := by
  simp only [x,map_pow,map_mul,value_A,value_B,a4_matrix]
  have h1 : matrixA*matrixB=mab := by decide +kernel
  have h2 : mab*ma4=mxa := by decide +kernel
  have h3 : mxa*matrixB=mxb := by decide +kernel
  rw [h1,h2,h3,pow_two]
  decide +kernel

private theorem g_matrix : value g = mg := by
  simp only [g,map_pow,map_mul,value_A,value_B,a6_matrix,a7_matrix]
  have h1 : matrixA*matrixB=mab := by decide +kernel
  have h2 : mab*ma6=mga := by decide +kernel
  have h3 : mga*matrixB=mgb := by decide +kernel
  have h4 : mgb*ma7=mgc := by decide +kernel
  rw [h1,h2,h3,h4]
  decide +kernel

private theorem gi_matrix : value (g⁻¹) = mgi := by
  have h : mg * mgi = 1 := by decide +kernel
  rw [←g_matrix] at h
  calc
    value (g⁻¹) = value (g⁻¹) * (value g * mgi) := by rw [h,mul_one]
    _ = mgi := by rw [←mul_assoc,←map_mul,inv_mul_cancel,map_one,one_mul]

private theorem y_matrix : value y = my := by
  change value (g*x*g⁻¹) = my
  rw [map_mul,map_mul,g_matrix,x_matrix,gi_matrix]
  have h : mg*mx=mgx := by decide +kernel
  rw [h]
  decide +kernel

private theorem x_cube : x^3=1 := by
  apply value_injective
  rw [map_pow,map_one,x_matrix]
  have h : mx*mx=mx2 := by decide +kernel
  rw [show (3:ℕ)=2+1 from rfl,pow_add,pow_two,h,pow_one]
  decide +kernel

private theorem y_cube : y^3=1 := by
  simp only [y,conj_pow,x_cube,mul_one,mul_inv_cancel]

private theorem z_central : z ∈ center Triple :=
  (center Triple).pow_mem coreScalar_mem_center 2
private theorem z_cube : z^3=1 := by
  change (coreScalar^2)^3=1
  rw [←pow_mul, Nat.mul_comm 2 3, pow_mul, coreScalar_pow_three,one_pow]
private theorem z_ne_one : z ≠ 1 := by
  intro he
  have hh := orderOf_dvd_of_pow_eq_one he
  change orderOf coreScalar ∣ 2 at hh
  rw [Sporadic.Mathieu.M22TripleCover.scalar_order] at hh
  norm_num at hh

private theorem xy_swap : x*y=z*y*x := by
  apply value_injective
  have hz : value z = matrixJ := coe_scalarUnit_sq
  rw [map_mul,map_mul,map_mul,x_matrix,y_matrix,hz]
  have h : matrixJ*my=mzy := by decide +kernel
  rw [h]
  decide +kernel

private theorem commutator_eq : ⁅x,y⁆=z := by
  simp only [commutatorElement_def, xy_swap, mul_assoc, mul_inv_cancel, mul_one]

private theorem xy_ne : x*y ≠ y*x := by
  intro he
  apply z_ne_one
  have hh : z*(y*x)=1*(y*x) := by simpa only [mul_assoc,one_mul] using xy_swap.symm.trans he
  exact mul_right_cancel hh

private def P : Subgroup Triple := closure {x,y}

private theorem P_card : Nat.card P=27 := by
  exact PrimeCubePair.card_closure_pair (p:=3) x y x_cube y_cube
    (by rw [commutator_eq]; exact z_cube)
    (by rw [commutator_eq]; exact (mem_center_iff.mp z_central x).symm)
    (by rw [commutator_eq]; exact (mem_center_iff.mp z_central y).symm) xy_ne

private def eval : HeisenbergPrime 3 →* Triple :=
  HeisenbergPrime.evaluateHom y x z z_central (by simpa only [mul_assoc] using xy_swap) y_cube x_cube z_cube

private theorem eval_range : eval.range=P := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    change y^a.b.val*x^a.a.val*z^a.c.val ∈ P
    apply mul_mem
    · exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
    · have hz : z ∈ P := commutator_eq ▸ commutator_le_self P (commutator_mem_commutator (subset_closure (Or.inl rfl)) (subset_closure (Or.inr rfl)))
      exact pow_mem hz _
  · rw [P,closure_le]
    rintro a (rfl | rfl)
    · exact ⟨⟨1,0,0⟩,by simp [eval,HeisenbergPrime.evaluateHom,ZMod.val_one]⟩
    · exact ⟨⟨0,1,0⟩,by simp [eval,HeisenbergPrime.evaluateHom,ZMod.val_one]⟩

private theorem P_cube (a : P) : a^3=1 := by
  have ha : a.val ∈ eval.range := eval_range.symm ▸ a.property
  obtain ⟨b,hb⟩ := ha
  apply Subtype.ext
  change a.val^3=1
  rw [←hb,←map_pow,HeisenbergPrime.pow_prime (by decide : 3≠2),map_one]

private def threeSylow : Sylow 3 Triple :=
  (IsPGroup.of_card (p:=3) (n:=3) P_card).toSylow (by
    have hc := P.card_mul_index
    rw [P_card,Sporadic.Mathieu.M22TripleCover.card] at hc
    have hi : P.index=49280 := by omega
    rw [hi]
    decide)

private theorem triple_cube_of_ninth {a : Triple} (ha : a^9=1) : a^3=1 := by
  have hp : IsPGroup 3 (zpowers a) := IsPGroup.of_card_dvd_pow (n:=2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  let aQ : Q := ⟨a,hQ (mem_zpowers a)⟩
  let e := Q.equiv threeSylow
  have h := P_cube (e aQ)
  have he : aQ^3=1 := e.injective (by rw [map_pow,map_one]; exact h)
  exact congrArg Subtype.val he

private theorem rank_two_of_noncommuting_pair {G : Type*} [Group G] [Finite G]
    (a b : G) (hc : Nat.card (closure ({a,b} : Set G))=27) (hn : a*b ≠ b*a) :
    2 ≤ primeRank 3 G := by
  let P := closure ({a,b} : Set G)
  by_contra hh
  have hP : IsPGroup 3 P := IsPGroup.of_card (p:=3) (n:=3) hc
  have hr : primeRank 3 P ≤ 1 := (primeRank_subgroup_le 3 P).trans (by omega)
  let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  let a' : P := ⟨a,subset_closure (Or.inl rfl)⟩
  let b' : P := ⟨b,subset_closure (Or.inr rfl)⟩
  have he := congrArg P.subtype (mul_comm a' b')
  rw [map_mul,map_mul] at he
  exact hn he

private theorem triple_rank : 2 ≤ primeRank 3 Triple :=
  rank_two_of_noncommuting_pair x y P_card xy_ne

private theorem triple_outer_two : IsPGroup 2 (MulAut.Outer Triple) := by
  apply IsPGroup.of_card_dvd_pow (n:=1)
  exact (card_dvd_of_injective
    (MulAut.centralQuotientOuter Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv)
    (MulAut.centralQuotientOuter_injective _)).trans
    Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two

private theorem normal_triple_cubic_mem {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* Triple)
    (hr : primeRank 3 G ≤ 2) {a : G} (ha : a^3=1) : a ∈ L := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB : B ≃* Triple := (cComponentTwoCoreQuotientEquiv hL).symm.trans e
  let : B.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  have hzc : Nat.card (center B)=3 :=
    (Nat.card_congr (centerCongr eB).toEquiv).trans Sporadic.Mathieu.M22TripleCover.center_card
  have hz : ∀ z ∈ center B, z^3=1 := by
    intro z hz
    have hh : (⟨z,hz⟩ : center B)^Nat.card (center B)=1 := pow_card_eq_one'
    rw [hzc] at hh
    exact congrArg Subtype.val hh
  have hexp : ∀ b : B, b^9=1 → b^3=1 := by
    intro b hb
    apply eB.injective
    simpa only [map_pow,map_one] using triple_cube_of_ninth
      (a:=eB b) (by simpa only [map_pow,map_one] using congrArg eB hb)
  have hrB : 2 ≤ primeRank 3 B := by rw [primeRank_congr 3 eB]; exact triple_rank
  have hbar : q a ∈ B := HexacodeTheta.order_three_mem_of_normal B hz hexp
    (triple_outer_two.of_equiv (MulAut.outerCongr eB).symm) hrB
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
    (by simpa only [map_pow,map_one] using congrArg q ha)
  have haK : a ∈ L ⊔ pCore 2 G := by
    have hh : a ∈ (L.map q).comap q := hbar
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  let K := L ⊔ pCore 2 G
  let D := L.subgroupOf K
  have hi : Nat.Coprime 3 D.index := by
    change Nat.Coprime 3 (L.relIndex (L ⊔ pCore 2 G))
    rw [relIndex_sup_left]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=G)).exists_card_dvd_pow
    exact (((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn).coprime_dvd_right
      (relIndex_dvd_card _ _)
  exact primeToResidual_le D hi (mem_primeToResidual_of_pow (n:=1)
    (show (⟨a,haK⟩ : K)^(3^1)=1 from Subtype.ext (by simpa using ha)))

open CFSG.Quasithin.Chapter12.Section02
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual triple-M₂₂ row is impossible in the first flag normalizer.
The central cover, its exponent-three Sylow and its outer bound are all
proved; only the preceding flag and faithful Cartan inputs remain. -/
theorem first_component_not_mathieu_cover
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁=3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G)=⊥) :
    ¬ IsM22Cover (K ⧸ pCore 2 K) := by
  rintro ⟨hq,⟨ez⟩,eq⟩
  let := hq
  have hz : Nat.card (center (K ⧸ pCore 2 K))=3 :=
    (Nat.card_congr ez.toEquiv).trans (by simp)
  obtain ⟨eK⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hz eq
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let : B.Normal := hK.2
  let e : (B ⧸ pCore 2 B) ≃* Triple :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)).trans eK
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card X₁ by rw [hXcard])
  have haG : orderOf (a : G)=3 := (orderOf_coe a).trans ha
  have hmem : (a : G) ∈ K := normal_triple_cubic_mem B hK.1.2 e
    ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
      3 Nat.prime_three (by decide))
    (a:=⟨a,hXN a.property⟩) (Subtype.ext (by simpa [haG] using pow_orderOf_eq_one (a : G)))
  have he : (a : G)=1 := mem_bot.mp
    ((first_component_disjoint_of_faithful_cartan D S f hm hfix hK.1 hLK hfaith).le_bot
      ⟨hmem,a.property⟩)
  rw [he,orderOf_one] at haG
  contradiction

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
