module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.EqualCore
public import Theory.GroupTheory.CharacteristicCentralizerTriple
public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.GeneralizedFitting.CentralSylowOutside

/-!
# The odd core of the original paired point join

In the actual point centralizer, Baum(T) is Sylow. Characteristic two in
C_G(z), its centralizer of v, and the original Sylow overgroup therefore
gives characteristic two in C_J(z). The three residual conjugates of z
have product v, central in J, so the odd core of J is trivial.

The actual complementary point zv centralizes the common Sylow subgroup.
When it lies in O₂(J), characteristic two follows from C_J(z), and B.2.13
makes its literal conjugate span a reduced elementary module. Otherwise
it moves an actual component, and J/O₃′(J) is nonsolvable. These facts
prepare the two branches of the F.6.18 comparison; the remaining module
and model exclusions stay with qt-d-1367-assembly.

Source: Aschbacher--Smith 13.2.12, printed pp.882--883. The terminal
application retains the original point groups and quotient maps.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original singular-point centralizer in J has characteristic two. -/
theorem point_singular_centralizer_characteristic
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module)) :
    J ⊓ Gv (markedZ d.flag.flag.module) ∈ Chapter1.He G := by
  let s := d.flag.flag.module
  let z := markedZ s
  let v := markedV s
  let B := ChapterB.baumann (T : Subgroup G)
  let C := Gv z ⊓ Gv v
  let D := J ⊓ Gv z
  have hzT := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp d.flag.flag.z_central
  have hz2 : orderOf z = 2 := orderOf_eq_prime s.markedZ_pow_two (markedZ_ne_one s)
  have hTC : (T : Subgroup G) ≤ Gv z := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
  have hCz : Gv z ∈ Chapter1.He G := by
    apply Chapter1.twoLocal_mem_He_of_sylow_le T (d.hypothesis.qtke.evenCharacteristic T)
      ?_ hTC
    refine ⟨zpowers z,?_,IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers,hz2,pow_one]),?_⟩
    · exact fun he => markedZ_ne_one s (mem_bot.mp (he ▸ mem_zpowers z))
    · exact (normalizer_zpowers_eq_centralizer_of_order_two z hz2).symm
  have hv2 : v^2=1 := by
    change s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2=1
    rw [←map_pow]
    have hp : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2=1 := by decide +kernel
    rw [hp,map_one]
  have hvC : v ∈ Gv z := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (markedZ_mem_Gv s)).symm
  have hC : C ∈ Chapter1.He G := by
    have hh := pCoreIn_selfCentralizing_centralizer hCz
      (IsPGroup.of_card (n := 1) (show Nat.card (zpowers v) = 2^1 by
        rw [Nat.card_zpowers,orderOf_eq_prime hv2 (markedV_ne_one s),pow_one]))
      (zpowers_le.mpr hvC)
    change C ⊓ centralizer (C.pCoreIn 2 : Set G) ≤ C.pCoreIn 2
    simpa only [C,Gv,zpowers_eq_closure,centralizer_closure] using hh
  have hBC : B ≤ C := le_inf (inf_le_left.trans hTC)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right)
  have hBD : B ≤ D := le_inf hBJ (inf_le_left.trans hTC)
  obtain ⟨P,hP⟩ := point_baumann_sylow d hH hB hZ hs hz
  have hpi : ¬2 ∣ B.relIndex (Gv v) := by
    have hh := relIndex_map_map_of_injective (P : Subgroup (Gv v)) ⊤ (Gv v).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,hP,relIndex_top_right] at hh
    rw [hh]
    exact P.not_dvd_index
  have hBi : ¬2 ∣ (B.subgroupOf C).index := by
    change ¬2 ∣ B.relIndex C
    intro hh
    exact hpi (hh.trans (dvd_of_mul_right_eq _
      (relIndex_mul_relIndex B C (Gv v) hBC inf_le_right)))
  let R := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf C)).toSylow hBi
  have hCB : C.pCoreIn 2 ≤ B := (pCoreIn_le_sylow C R).trans_eq
    (map_subgroupOf_eq_of_le hBC)
  have hzB : z ∈ B := by
    change z ∈ ChapterB.baumann (T : Subgroup G)
    rw [source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem]
    exact ⟨hzT.1,markedZ_mem_Gv s⟩
  refine Chapter1.lemma_1_1_4_4 (N := D) ?_ (le_inf inf_le_right (inf_le_left.trans hJv)) hC ?_
  · intro he
    exact markedZ_ne_one s (mem_bot.mp (he ▸ hBD hzB))
  · exact inf_le_left.trans (hCB.trans hBD)

/-- The marked singular point lies in the original Baumann subgroup. -/
theorem singular_mem_baumann
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    markedZ d.flag.flag.module ∈ ChapterB.baumann (T : Subgroup G) :=
  by
    rw [source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem]
    exact ⟨((mem_omegaOneCenterAmbient_iff _ _).mp d.flag.flag.z_central).1,
      markedZ_mem_Gv d.flag.flag.module⟩

/-- Characteristic two for the intrinsic centralizer on the same original join. -/
theorem point_singular_centralizer_intrinsic
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module)) :
    let z : J := ⟨markedZ d.flag.flag.module,hBJ (singular_mem_baumann d hH hB hZ hs hz)⟩
    centralizer (pCore 2 (centralizer ({z} : Set J)) : Set (centralizer ({z} : Set J))) ≤
      pCore 2 (centralizer ({z} : Set J)) := by
  intro z
  let C := J ⊓ Gv (markedZ d.flag.flag.module)
  let e : centralizer ({z} : Set J) ≃* C :=
    { toFun := fun x => ⟨x, x.val.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      invFun := fun x => ⟨⟨x,x.property.1⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
    (Chapter1.mem_He_iff.mp (point_singular_centralizer_characteristic d hH hB hZ hs hz hBJ hJv))

/-- The literal odd core of every original point overgroup vanishes. -/
theorem point_overgroup_oddCore_eq_bot
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hLJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module)) : pPrimeCore 2 J = ⊥ := by
  let s := d.flag.flag.module
  let z : J := ⟨markedZ s,hBJ (singular_mem_baumann d hH hB hZ hs hz)⟩
  obtain ⟨c,hc,hprod⟩ := exists_residual_triple s
  let c' : J := ⟨c,hLJ hc⟩
  apply oddCore_eq_bot_of_characteristic_centralizer_triple z c' (c'^2)
    (Subtype.ext s.markedZ_pow_two)
    (point_singular_centralizer_intrinsic d hH hB hZ hs hz hBJ hJv)
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  change (x:G) * (markedZ s * MulAut.conj c (markedZ s) *
      MulAut.conj (c^2) (markedZ s)) =
    (markedZ s * MulAut.conj c (markedZ s) * MulAut.conj (c^2) (markedZ s)) * (x:G)
  rw [hprod]
  exact mem_centralizer_singleton_iff.mp (hJv x.property)

/-- The fixed marked point lies in the original Baumann subgroup. -/
theorem point_mem_baumann
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    markedV d.flag.flag.module ∈ ChapterB.baumann (T : Subgroup G) := by
  rw [source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
    d.flag.flag.vector_mem d.flag.flag.vector_not_mem]
  exact ⟨d.chosen.le_sylow (d.flag.two_le_V d.flag.flag.vector_mem),
    mem_centralizer_singleton_iff.mpr rfl⟩

/-- The original fixed point is central in every point overgroup, hence in its two-core. -/
theorem point_mem_overgroup_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module)) :
    markedV d.flag.flag.module ∈ J.pCoreIn 2 := by
  let v : J := ⟨markedV d.flag.flag.module,hBJ (point_mem_baumann d hH hB hZ hs hz)⟩
  have hvC : v ∈ center J := mem_center_iff.mpr fun j =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hJv j.property))
  have hv2 : orderOf v = 2 := by
    rw [←Subgroup.orderOf_coe]
    apply orderOf_eq_prime _ (markedV_ne_one d.flag.flag.module)
    change (d.flag.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))^2=1
    rw [←map_pow]
    have hp : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2=1 := by decide +kernel
    rw [hp,map_one]
  have hline : zpowers v ≤ center J := zpowers_le.mpr hvC
  let : (zpowers v).Normal := ⟨fun x hx j => by
    simpa only [mem_center_iff.mp (hline hx) j,mul_assoc,mul_inv_cancel,mul_one] using hx⟩
  have hline2 : IsPGroup 2 (zpowers v) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hv2,pow_one])
  have hc : zpowers v ≤ pCore 2 J := le_sSup ⟨inferInstance,hline2⟩
  exact mem_map_of_mem J.subtype (hc (mem_zpowers v))

/-- The source complementary point e₁=zv centralizes the original common Sylow. -/
theorem complement_centralizes_baumann
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∈
      centralizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  apply mem_centralizer_iff.mpr
  intro b hb
  have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp d.flag.flag.z_central
  have hbv := (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
    d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le hb
  exact (Commute.mul_right (hzT.2.2 b hb.1)
    (mem_centralizer_singleton_iff.mp hbv.2)).eq

/-- In the core branch, C_J(z) proves characteristic two in the actual J. -/
theorem point_overgroup_characteristic_of_complement_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (he : markedZ d.flag.flag.module * markedV d.flag.flag.module ∈ J.pCoreIn 2) :
    J ∈ Chapter1.He G := by
  let z : J := ⟨markedZ d.flag.flag.module,hBJ (singular_mem_baumann d hH hB hZ hs hz)⟩
  have hzcore : (z : G) ∈ J.pCoreIn 2 :=
    (mul_mem_cancel_right (point_mem_overgroup_core d hH hB hZ hs hz hBJ hJv)).mp he
  obtain ⟨z',hz',heq⟩ := hzcore
  have hzJ : z ∈ pCore 2 J := (Subtype.ext heq : z' = z) ▸ hz'
  apply Chapter1.mem_He_iff.mpr
  exact centralizer_pCore_le_of_overgroup 2 (centralizer ({z} : Set J))
    (point_singular_centralizer_intrinsic d hH hB hZ hs hz hBJ hJv)
    (centralizer_le (Set.singleton_subset_iff.mpr hzJ))

/-- Outside the two-core, the same complementary point moves an ordinary
component. The O₃′ quotient is nonsolvable, excluding F.6.18(1)--(2) in this branch. -/
theorem point_overgroup_component_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hLJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    {A B : Subgroup J} (hg : ChapterF.IsGoldschmidtTriple A B)
    (he : markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2) :
    ¬ Group.IsSolvable (J ⧸ pPrimeCore 3 J) ∧
      ∃ K : Subgroup J, IsComponent J K ∧ K ≠ ⊥ ∧
        ⁅K,zpowers (⟨markedZ d.flag.flag.module * markedV d.flag.flag.module,
          J.mul_mem (hBJ (singular_mem_baumann d hH hB hZ hs hz))
            (hBJ (point_mem_baumann d hH hB hZ hs hz))⟩ : J)⁆ = K := by
  let e : J := ⟨markedZ d.flag.flag.module * markedV d.flag.flag.module,
    J.mul_mem (hBJ (singular_mem_baumann d hH hB hZ hs hz))
      (hBJ (point_mem_baumann d hH hB hZ hs hz))⟩
  have ho := point_overgroup_oddCore_eq_bot d hH hB hZ hs hz hBJ hLJ hJv
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hc : e ∈ centralizer (S : Set J) := by
    intro x hx
    apply Subtype.ext
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      x (hS ▸ mem_map_of_mem J.subtype hx)
  have hn : e ∉ pCore 2 J := fun hh => he (mem_map_of_mem J.subtype hh)
  obtain ⟨K,hK,hcomm,hne⟩ := exists_component_commutator_of_central_sylow_outside_core S ho e hc hn
  refine ⟨?_,K,hK,hne,hcomm⟩
  intro hquot
  exact not_solvable_of_central_sylow_outside_core S ho e hc hn
    ((Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 J)).mpr
      ⟨hg.primeToThreeCore_solvable,hquot⟩)

/-- B.2.13 constructs the reduced module generated by the actual complementary
point in the core branch, retaining the literal conjugation quotient. -/
theorem point_overgroup_reduced_span_of_complement_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module))
    (he : markedZ d.flag.flag.module * markedV d.flag.flag.module ∈ J.pCoreIn 2) :
    ∃ x : J, (x : G) = markedZ d.flag.flag.module * markedV d.flag.flag.module ∧
      IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤) := by
  let s := d.flag.flag.module
  let e : J := ⟨markedZ s * markedV s,
    J.mul_mem (hBJ (singular_mem_baumann d hH hB hZ hs hz))
      (hBJ (point_mem_baumann d hH hB hZ hs hz))⟩
  obtain ⟨e',he',heq⟩ := he
  have hecore : e ∈ pCore 2 J := (Subtype.ext heq : e' = e) ▸ he'
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hc : e ∈ centralizer (S : Set J) := by
    intro x hx
    apply Subtype.ext
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      x (hS ▸ mem_map_of_mem J.subtype hx)
  have hp : e^2=1 := by
    apply Subtype.ext
    change (s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z) *
      s.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))^2=1
    rw [←map_mul,←map_pow]
    have hh : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.z *
      Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2=1 := by decide +kernel
    rw [hh,map_one]
  exact ⟨e,rfl,central_sylow_core_span_reduced S e hc hecore hp⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
