module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.LowerBounds
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.CentralizerSource
public import Theory.SpecificGroups.SU3.OddSylowCenter
/-!
# The normal odd unitary source row in E.2.2

The actual normal subgroup supplies a Sylow-central involution. The proved
unitary centralizer maximality identifies the original unique maximal
overgroup with its full ambient centralizer. In the wrong congruence the
characteristic wreathed-base normalizer is a proper solvable Sylow overgroup
that moves this involution, a contradiction. In the surviving congruence
the actual Sylow center has order two, giving exactly the centralizer of
Z(T∩K) required by the source. All stored field and form markings remain.
Source: Aschbacher–Smith E.2.2(2d), printed pp.215–216; the independent
unitary matrix geometry is reused from the completed E.1.14 family.
-/
public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
open ValuesOdd.PSUThreeGeneration
variable {H : Type*} [Group H] [Finite H]

/-- The unique maximal Sylow overgroup is an actual involution centralizer,
and the unitary field parameter is one modulo four. -/
theorem unitary_centralizer_congruence
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen : K⊔(T:Subgroup H)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSU K 3 p) :
    p%4=1 ∧ ∃t:K,orderOf t=2 ∧ (t:H)∈(T:Subgroup H) ∧
      (T:Subgroup H)≤centralizer ({(t:H)}:Set H) ∧
      ChapterB.minimalParabolicMax T hP=centralizer ({(t:H)}:Set H) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K=centralizer ({t}:Set K) := by
  have heven : 2∣Nat.card K := by
    obtain ⟨F,_,_,J,hcard,hc,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.SU3.two_dvd_projective_card_of_prime_frobenius J p hp ho hcard hc
  obtain ⟨t,ht,htT,hTt⟩ := normal_even_subgroup_central_sylow_involution T K heven
  have hto : orderOf t=2 := orderOf_eq_prime_iff.mpr ht.symm
  have hmax := InnerGeometry.centralizer_isCoatom_of_matrix_geometry hp ho hm t hto
  obtain ⟨hM,hMK⟩ := minimalParabolic_max_eq_involution_centralizer T hP K hgen t hmax hTt
  refine ⟨?_,t,hto,htT,hTt,hM,hMK⟩
  have hmod : p%4=1 ∨ p%4=3 := by obtain ⟨k,hk⟩:=ho;omega
  rcases hmod with hgood|hbad
  · exact hgood
  · obtain ⟨A,hTA,hsol,hmove⟩ :=
      InnerGeometry.WreathedNormalizer.exists_solvable_sylow_overgroup K hgen hp ho hbad hm
        ((orderOf_injective K.subtype K.subtype_injective t).trans hto) t.property htT hTt
    have hne : A≠⊤ := by
      intro he
      have hsolH : Group.IsSolvable H := by
        let _ : Group.IsSolvable (⊤:Subgroup H) := he ▸ hsol
        exact Group.isSolvable_of_surjective (f:=(topEquiv (G:=H)).toMonoidHom) (topEquiv (G:=H)).surjective
      let _ := hsolH
      let _ : Group.IsPerfect K := isPerfect_of_model hp ho hm
      exact Group.IsPerfect.not_isSolvable K inferInstance
    have hAM : A≤ChapterB.minimalParabolicMax T hP := hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
        (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ hTA
      (lt_top_iff_ne_top.mpr hne)
    exact (hmove (hM ▸ hAM)).elim
/-- E.2.2(2d), with the original Sylow-center centralizer and field congruence. -/
theorem unitary
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen : K⊔(T:Subgroup H)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSU K 3 p) :
    p%4=1 ∧ (ChapterB.minimalParabolicMax T hP).subgroupOf K =
      centralizer ((center ((T:Subgroup H).subgroupOf K)).map
        ((T:Subgroup H).subgroupOf K).subtype : Set K) := by
  obtain ⟨hmod,t,hto,htT,hTt,_,hMK⟩ := unitary_centralizer_congruence T hP K hgen hp ho hm
  refine ⟨hmod,?_⟩
  let R := (T:Subgroup H).subgroupOf K
  have hR : Nat.card (center R)=2 := by
    obtain ⟨F,_,_,J,hcard,hc,⟨e⟩⟩ := hm
    obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal K
    let P' := P.mapSurjective (f:=e.toMonoidHom) e.surjective
    let eP : P≃*P' := (P:Subgroup K).equivMapOfInjective e.toMonoidHom e.injective
    change Nat.card (center ((T:Subgroup H).subgroupOf K))=2
    rw [← hP,Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
    exact BenderSuzuki.MatrixGroups.HermitianForm.OddSylowCenter.card_center J hp ho hmod hcard hc P'
  let Z := (center R).map R.subtype
  have htZ : t∈Z := by
    refine ⟨⟨t,htT⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hTt r.property)
  have hZ : Z=zpowers t := by
    apply (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htZ) ?_).symm
    rw [card_map_of_injective R.subtype_injective,Nat.card_zpowers,hto]
    exact hR.le
  rw [hMK]
  change centralizer ({t}:Set K)=centralizer (Z:Set K)
  rw [hZ,zpowers_eq_closure,centralizer_closure]
end CFSG.Quasithin.ChapterE.Structure.OddDegreeThree
