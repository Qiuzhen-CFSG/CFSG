module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Commutator
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Plane
public import Theory.GroupAction.PerfectSectionDegreeTwo
public import Theory.GroupTheory.SylowKernelCore

/-!
# Odd-core actions of the original first radical

The original R₁ centralizes L₁ modulo O₂(L₁). On an odd prime-field
plane with nontrivial L₁-action, the projective image of R₁ centralizes a
nontrivial perfect subgroup of PGL₂ and is therefore trivial. Thus R₁
acts by scalars, and [R₁,X] acts trivially. Burnside's Frattini kernel
lifts this to the full odd prime group, retaining higher exponents.

The original-flag applications use the supplied local action overgroup,
not a representation of the full ambient group. A solvable centralizer
kernel supplies nontriviality of the seed action. A separate centralizer
criterion then detects the literal O₂(KT): the controlled centralizer has
a central kernel above a two-group and is nilpotent.

These results provide an action route to the second bound of 11.4.1(3).
Instantiation on the canonical A.3.6 prime cores after the two-core quotient
remains with qt-d-1222-shadow-component-triangle; no assertion about the
outstanding full Fitting index is made here. The registered preceding
source inputs retain their final discharge with qt-d-1222-shadow-components.
Source: Aschbacher–Smith, 11.4.1(3), printed pp.775–776, using A.3.6,
pp.43–45; the projective centralizer and Frattini kernel arguments are
implemented in Theory.GroupAction.PerfectSectionDegreeTwo.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G]

private theorem projective_image_ne_bot_of_perfect
    {F : Type*} [Field F] (A : Subgroup G) [Group.IsPerfect A]
    (a : G →* GL (Fin 2) F) (ha : a.comp A.subtype ≠ 1) :
    A.map (ProjGenLinGroup.mk.comp a) ≠ ⊥ := by
  intro he
  have hz : A.map a ≤ center (GL (Fin 2) F) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [← ProjGenLinGroup.ker_mk]
    exact mem_bot.mp (he ▸ mem_map_of_mem (ProjGenLinGroup.mk.comp a) hx)
  let : Group.IsPerfect (A.map a) := Group.IsPerfect.map a
  let : IsMulCommutative (A.map a) := IsMulCommutative.of_comm (by
    intro x y
    exact Subtype.ext (mem_center_iff.mp (hz y.property) x))
  apply ha
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨a x,mem_map_of_mem a x.property⟩ : A.map a) 1)

/-- A two-core-centralizing actor has scalar image on any odd plane
on which the perfect seed acts nontrivially. -/
theorem scalar_image_of_seed_core_commutator
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (A R : Subgroup G) [Group.IsPerfect A]
    (a : G →* GL (Fin 2) (ZMod p)) (ha : a.comp A.subtype ≠ 1)
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) :
    R.map a ≤ center (GL (Fin 2) (ZMod p)) := by
  let q := ProjGenLinGroup.mk (n := Fin 2) (R := ZMod p)
  let b := q.comp a
  have hk : A.pCoreIn 2 ≤ b.ker := by
    rintro _ ⟨x,hx,rfl⟩
    exact GeneralLinearGroup.perfect_twoCore_le_projective_ker ho (a.comp A.subtype) hx
  have hh : ⁅R.map b,A.map b⁆ = ⊥ := by
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hc.trans hk)
  have hn := commutator_eq_bot_iff_le_centralizer.mp hh
  let : Group.IsPerfect (A.map b) := Group.IsPerfect.map b
  rw [Theory.PGL2.centralizer_eq_bot_of_perfect _
    (projective_image_ne_bot_of_perfect A a ha)] at hn
  rintro _ ⟨x,hx,rfl⟩
  rw [← ProjGenLinGroup.ker_mk]
  exact mem_bot.mp (hn (mem_map_of_mem b hx))

/-- The entire mutual commutator is killed, with no bound on the
two-group of scalar actors. -/
theorem commutator_le_plane_ker_of_seed_core_commutator
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (A R X : Subgroup G) [Group.IsPerfect A]
    (a : G →* GL (Fin 2) (ZMod p)) (ha : a.comp A.subtype ≠ 1)
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) : ⁅R,X⁆ ≤ a.ker := by
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [map_commutator]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((scalar_image_of_seed_core_commutator ho A R a ha hc).trans
      (center_le_centralizer _))

/-- Burnside's Frattini kernel lifts the plane calculation to the whole
odd prime group, including higher homocyclic exponents. -/
theorem commutator_le_odd_core_action_ker
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : IsPGroup p P) (hd : Nat.card (P ⧸ frattini P) ≤ p ^ 2)
    (A R X : Subgroup G) [Group.IsPerfect A]
    (hR : IsPGroup 2 R) (hXR : X ≤ normalizer (R : Set G))
    (a : G →* MulAut P) (ha : a.comp A.subtype ≠ 1)
    (hc : ⁅R,A⁆ ≤ A.pCoreIn 2) : ⁅R,X⁆ ≤ a.ker := by
  let : Fact (IsPGroup p P) := ⟨hp⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨e,he⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (P ⧸ frattini P) hd
  let b := (quotientAut (frattini P)).comp a
  have hb : (e.comp b).comp A.subtype ≠ 1 := by
    intro hh
    apply MonoidHom.frattini_comp_ne_one_of_isPerfect hp (a.comp A.subtype) ha
    apply MonoidHom.ext
    intro x
    apply he
    exact (DFunLike.congr_fun hh x).trans e.map_one.symm
  have hker := commutator_le_plane_ker_of_seed_core_commutator ho A R X (e.comp b) hb hc
  have hD : IsPGroup 2 (⁅R,X⁆ : Subgroup G) :=
    hR.to_le (le_normalizer_iff_commutator_le_left.mp hXR)
  let d := a.comp (⁅R,X⁆).subtype
  have hsmall : IsPGroup p ((quotientAut (frattini P)).comp d).range := by
    have heq : (quotientAut (frattini P)).comp d = 1 := by
      apply MonoidHom.ext
      intro x
      apply he
      exact (hker x.property).trans e.map_one.symm
    rw [heq,MonoidHom.range_one]
    exact IsPGroup.of_subsingleton p _
  have hdp := d.isPGroup_range_of_frattini_range hp hsmall
  have hd2 : IsPGroup 2 d.range := hD.of_surjective d.rangeRestrict d.rangeRestrict_surjective
  have hbot : d.range = ⊥ := disjoint_self.mp (hd2.disjoint_of_coprime hdp ho.coprime_two_left)
  intro x hx
  exact mem_bot.mp (hbot ▸ (show a x ∈ d.range from ⟨⟨x,hx⟩,rfl⟩))

/-- The first radical acts trivially on the seed modulo its own two-core. -/
theorem local_core_seed_commutator (T : Sylow 2 G) (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    ⁅(A ⊔ (T : Subgroup G)).pCoreIn 2,A⁆ ≤ A.pCoreIn 2 := by
  have hRT : (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (A ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hn : A ≤ normalizer ((A ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_left.trans ((A ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp (hRT.trans hTA))
    (le_normalizer_iff_commutator_le_left.mp hn)).trans
      (inf_pCoreIn_le_of_le 2 (show A ≤ A ⊔ (T : Subgroup G) from le_sup_left))

variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- Apply the scalar and Frattini arguments to the literal original R₁.
The action is defined only on its supplied local overgroup; no action of
the full simple ambient group is required. -/
theorem ofFlag_commutator_le_odd_core_action_ker
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H J : Subgroup G)
    (hAJ : f.Li 0 ≤ J) (hRJ : (ofFlag S f X z H).R₁ ≤ J) (hXJ : X ≤ J)
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : IsPGroup p P) (hd : Nat.card (P ⧸ frattini P) ≤ p ^ 2)
    (a : J →* MulAut P) (ha : a.comp ((f.Li 0).subgroupOf J).subtype ≠ 1) :
    (⁅(ofFlag S f X z H).R₁,X⁆).subgroupOf J ≤ a.ker := by
  let A := (f.Li 0).subgroupOf J
  let R := (ofFlag S f X z H).R₁.subgroupOf J
  let Y := X.subgroupOf J
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  let e : A ≃* f.Li 0 := subgroupOfEquivOfLe hAJ
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hn : Y ≤ normalizer (R : Set J) := by
    rw [← subgroupOf_normalizer_eq hRJ]
    exact comap_mono hXR
  have hc : ⁅R,A⁆ ≤ A.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hAJ,
      map_pCoreIn_of_injective 2 A J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hAJ]
    exact local_core_seed_commutator T (f.Li 0) (f.sylow_normalizes_Li 0)
  have hh := commutator_le_odd_core_action_ker ho hp hd A R Y
    (isPGroup_pCoreIn 2 _).comap_subtype hn a ha hc
  have heq : ⁅R,Y⁆ = (⁅(ofFlag S f X z H).R₁,X⁆).subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hXJ,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hRJ hXJ))]
  exact heq ▸ hh

/-- A solvable action kernel cannot contain the original nonsolvable seed. -/
theorem ofFlag_seed_action_ne_one
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (J : Subgroup G) (hAJ : f.Li 0 ≤ J)
    {Q : Type*} [Group Q] (a : J →* Q)
    (hk : Group.IsSolvable (a.comp ((f.Li 0).subgroupOf J).subtype).ker) :
    a.comp ((f.Li 0).subgroupOf J).subtype ≠ 1 := by
  intro he
  rw [he,MonoidHom.ker_one] at hk
  let := hk
  let : Group.IsSolvable ((f.Li 0).subgroupOf J) :=
    Group.isSolvable_of_surjective (f := (topEquiv (G := (f.Li 0).subgroupOf J)).toMonoidHom)
      (topEquiv (G := (f.Li 0).subgroupOf J)).surjective
  exact Chapter1.mem_L_not_isSolvable (Triangle.Reselection.flag_residual_mem_local D S f 0)
    (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hAJ).toMonoidHom)
      (subgroupOfEquivOfLe hAJ).surjective)

/-- On an actual normal odd prime subgroup with a small Frattini quotient,
the original commutator centralizes the whole subgroup. The solvable
centralizer premise is the action-kernel clause supplied by A.3.6. -/
theorem ofFlag_commutator_centralizes_odd_core
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H J : Subgroup G)
    (hAJ : f.Li 0 ≤ J) (hRJ : (ofFlag S f X z H).R₁ ≤ J) (hXJ : X ≤ J)
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (P : Subgroup J) [P.Normal] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : IsPGroup p P) (hd : Nat.card (P ⧸ frattini P) ≤ p ^ 2)
    (hk : Group.IsSolvable ((centralizer (P : Set J)).subgroupOf ((f.Li 0).subgroupOf J))) :
    (⁅(ofFlag S f X z H).R₁,X⁆).subgroupOf J ≤ centralizer (P : Set J) := by
  let a : J →* MulAut P := MulAut.conjNormal
  have hak : a.ker = centralizer (P : Set J) := MulAut.conjNormal_ker_eq_centralizer P
  have hker : Group.IsSolvable (a.comp ((f.Li 0).subgroupOf J).subtype).ker := by
    change Group.IsSolvable (a.ker.subgroupOf ((f.Li 0).subgroupOf J))
    rw [hak]
    exact hk
  rw [← hak]
  exact
    ofFlag_commutator_le_odd_core_action_ker S f X z H J hAJ hRJ hXJ hXR ho hp hd a
      (ofFlag_seed_action_ne_one S f J hAJ a hker)

/-- If a normal subgroup's centralizer is controlled inside a normal
two-cocomplement, every two-subgroup centralizing it lies in the ambient
two-core. This does not bound the order of the other two-actors. -/
theorem two_subgroup_le_core_of_controlled_centralizer
    (K F R : Subgroup G) [K.Normal] [F.Normal]
    (hq : IsPGroup 2 (G ⧸ K))
    (hc : K ⊓ centralizer (F : Set G) ≤ F)
    (hR : IsPGroup 2 R) (hRF : R ≤ centralizer (F : Set G)) :
    R ≤ pCore 2 G := by
  let C := centralizer (F : Set G)
  let a := (QuotientGroup.mk' K).comp C.subtype
  have hk : a.ker ≤ center C := by
    intro x hx
    have hxF : (x : G) ∈ F := hc ⟨(QuotientGroup.eq_one_iff _).mp hx,x.property⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((y.property x hxF).symm)
  let : Group.IsNilpotent (G ⧸ K) := hq.isNilpotent
  let : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center a hk
  obtain ⟨P,hP⟩ := (show IsPGroup 2 (R.subgroupOf C) from hR.comap_subtype).exists_le_sylow
  have hm := map_mono (f := C.subtype) hP
  rw [map_subgroupOf_eq_of_le hRF] at hm
  exact hm.trans (P.map_le_pCore inferInstance inferInstance 2)


/-- Detect the original commutator inside O₂(KT) from centralization of
a normal subgroup whose centralizer in K is contained in that subgroup.
This is the final group-theoretic use of the odd-core action calculation;
it does not require a bound on the whole of R₁/O₂(KT). -/
theorem ofFlag_commutator_le_core_of_controlled_centralizer
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hAK : f.Li 0 ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXR : X ≤ normalizer (f.Ri 0 : Set G))
    (F : Subgroup (K ⊔ (T : Subgroup G) : Subgroup G)) [F.Normal]
    (hc : K ⊓ centralizer (F.map (K ⊔ (T : Subgroup G)).subtype : Set G) ≤
      F.map (K ⊔ (T : Subgroup G)).subtype)
    (hcentral : ⁅(ofFlag S f X z H).R₁,X⁆ ≤
      centralizer (F.map (K ⊔ (T : Subgroup G)).subtype : Set G)) :
    ⁅(ofFlag S f X z H).R₁,X⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let R := (ofFlag S f X z H).R₁
  let C := ⁅R,X⁆
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans (sup_le_sup_right hAK _)
  have hCR : C ≤ R := le_normalizer_iff_commutator_le_left.mp hXR
  have hCJ : C ≤ J := hCR.trans hRJ
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right),subgroupOf_self])
  have hc' : B ⊓ centralizer (F : Set J) ≤ F := by
    rintro x ⟨hxK,hxC⟩
    have hx : (x : G) ∈ K ⊓ centralizer (F.map J.subtype : Set G) := by
      refine ⟨hxK,?_⟩
      rintro y ⟨y',hy',rfl⟩
      exact congrArg Subtype.val (hxC y' hy')
    obtain ⟨y,hy,he⟩ := hc hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hC2 : IsPGroup 2 (C.subgroupOf J) :=
    ((isPGroup_pCoreIn 2 _).to_le hCR).comap_subtype
  have hCF : C.subgroupOf J ≤ centralizer (F : Set J) := by
    intro x hx y hy
    exact Subtype.ext (hcentral hx y (mem_map_of_mem J.subtype hy))
  have hh := two_subgroup_le_core_of_controlled_centralizer B F (C.subgroupOf J)
    hq hc' hC2 hCF
  have hm := map_mono (f := J.subtype) hh
  rw [map_subgroupOf_eq_of_le hCJ] at hm
  exact hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
