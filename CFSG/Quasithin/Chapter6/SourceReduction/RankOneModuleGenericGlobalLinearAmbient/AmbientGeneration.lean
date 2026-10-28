module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.InvolutiveAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FourClosureAlternatives
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FullNormalizer
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.FixedCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.Generation

/-!
# The original Sylow and ambient generation in the maximal linear row

An outer involution fixes a nonabelian binary unitriangular subgroup.
Consequently the central-derived characteristic subgroup of its Sylow
centralizer is nontrivial and lies in the original highest root Z(S).
Choose an outer involution with maximal centralizer inside T. The normalizer
condition in a larger two-subgroup centralizer would produce a nonidentity
fixed element of that characteristic subgroup. Its full centralizer lies
in the original common normalizer by the proved source 5.3.7, contradicting
local maximality. Ambient involution fusion then forces S=T.

The existing strong-embedding argument now gives generation of original G
by both the full normalizers and the original factors. The constructed
marked extension therefore has a faithful completion in G. Recognition
below remains conditional only on the source endpoint cubic witness; the
Hall-torus argument producing it is still owed by this ambient-row task.
Field four, every original n>1, and both comparison orientations are retained.

Source: Aschbacher–Smith F.4.37–38 and F.4.45–46, printed pp.293–294,297,
using 5.3.7 on pp.660–661 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem prime_overgroup_eq_of_characteristic_centralizers
    (E D C : Subgroup G) (Q : Subgroup E) [Q.Characteristic] (hQ : Q ≠ ⊥)
    (hcentral : ∀ z ∈ Q.map E.subtype, z ≠ 1 → centralizer ({z} : Set G) ≤ D)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V → E ≤ V → V ≤ C → V ≤ D → V=E)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hER : E ≤ R) (hRC : R ≤ C) : R=E := by
  by_contra hne
  let : Group.IsNilpotent R := hR.isNilpotent
  have hproper : E.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    intro hRE
    exact hne (le_antisymm hRE hER)
  obtain ⟨u,huN,huE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (E.subgroupOf R) hproper)
  let V := R ⊓ normalizer (E : Set G)
  have hEV : E ≤ V := le_inf hER E.le_normalizer
  have hVp : IsPGroup 2 V := hR.to_le inf_le_left
  let Z := Q.map E.subtype
  have hZV : Z ≤ V := (map_subtype_le Q).trans hEV
  have hVN : V ≤ normalizer (Z : Set G) := inf_le_right.trans
    (normalizer_le_normalizer_characteristic_image E Q)
  let : (Z.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer hVN
  have hZne : Z.subgroupOf V ≠ ⊥ := by
    intro hh
    have hZbot : Z = ⊥ := by
      rw [←map_subgroupOf_eq_of_le hZV,hh,Subgroup.map_bot]
    exact hQ ((Q.map_eq_bot_iff_of_injective E.subtype_injective).mp hZbot)
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal hVp (Z.subgroupOf V) hZne)
  have hzG : (z.val : G) ≠ 1 := by
    intro hh
    exact hz1 (Subtype.ext (Subtype.ext hh))
  have hVD : V ≤ D := by
    apply le_trans ?_ (hcentral z.val.val z.property.2 hzG)
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg V.subtype (mem_center_iff.mp z.property.1 ⟨v,hv⟩))
  have hVE : V=E := hmax V hVp hEV (inf_le_left.trans hRC) hVD
  have huVG : u.val ∈ V := by
    refine ⟨u.property,?_⟩
    rwa [←subgroupOf_normalizer_eq hER] at huN
  exact huE (hVE ▸ huVG)

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

omit hmax in
/-- The field quotient kills the derived subgroup of the original ambient Sylow. -/
theorem Preparation.linear_sylow_derived_le_sourceS :
    ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ sourceS L H := by
  obtain ⟨_,_,_,_,_,_,hpsl,_⟩ :=
    (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  obtain ⟨K,_,_,hK,⟨a⟩⟩ := hpsl
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let : IsCyclic (K ≃+* K) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (K ≃+* K) := IsCyclic.commGroup
  rw [←map_subtype_commutator]
  rintro x ⟨y,hy,rfl⟩
  have hh := Abelianization.commutator_subset_ker (residualSylowFieldAction hH.1.1.2 a) hy
  rw [d.residual_sylow_field_kernel h hH.1.1.2
    (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he) a] at hh
  exact hh

/-- The central-derived characteristic subgroup of an outer-involution
centralizer lies nontrivially in the original central line. -/
theorem Preparation.linear_outer_centralizer_characteristic
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ sourceS L H) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    let Q := center E ⊓ _root_.commutator E
    Q ≠ ⊥ ∧ Q.map E.subtype ≤ centerIn (sourceS L H) := by
  obtain ⟨e,σ,_,_,_,ha⟩ := d.linear_mark_outer_involution h hH hp F hm hF he hmax
    t t.property ((orderOf_coe t).trans ht2) htS
  exact Matrix.PSL3.LinearAmbientGeometry.field_centralizer_characteristic_line F
    (sourceS L H) _ e t σ (T.isPGroup'.to_le inf_le_left) ha
    (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
    ((commutator_mono inf_le_left inf_le_left).trans
      (d.linear_sylow_derived_le_sourceS h hH hp F hm hF he))

/-- The original common Sylow is the entire ambient Sylow, at every degree. -/
theorem Preparation.linear_sourceS_eq_sylow : sourceS L H = (T : Subgroup G) := by
  by_contra hne
  obtain ⟨_,_,_,_,_,_,_,_,t₀,ht₀,ht₀T,ht₀S,_⟩ :=
    d.linear_exists_outer_involution h hH hp F hm hF he hne
  let X : Set T := {t | orderOf t=2 ∧ t.val ∉ sourceS L H}
  have hX : X.Nonempty := ⟨⟨t₀,ht₀T⟩,(orderOf_coe _).symm.trans ht₀,ht₀S⟩
  obtain ⟨t,ht,hbound⟩ := Set.exists_max_image X
    (fun t : T => Nat.card (centralizer ({t} : Set T))) X.toFinite hX
  let D := normalizer (sourceS L H : Set G)
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let C := centralizer ({t.val} : Set G)
  have hTD : (T : Subgroup G) ≤ D := sylow_normalizes_sourceS h.sylow_normalizes hH.1.1.2
  have hmaxlocal (V : Subgroup G) (hV : IsPGroup 2 V) (hEV : E ≤ V)
      (hVC : V ≤ C) (hVD : V ≤ D) : V=E := by
    have hh := T.centralizer_prime_overgroup_eq_of_local_card_bound D hTD t ?_ V hV ?_ hVC hVD
    · simpa only [Subgroup.map_subtype_centralizer_singleton (T : Subgroup G) t] using hh
    · intro g y hgy
      apply hbound y
      constructor
      · have hh : orderOf y.val=2 := by
          rw [←hgy]
          exact ((MulAut.conj g.val).orderOf_eq t.val).trans ((orderOf_coe t).trans ht.1)
        exact (orderOf_coe y).symm.trans hh
      · intro hy
        apply ht.2
        exact (mem_normalizer_iff.mp g.property t.val).mpr (by
          change (MulAut.conj g.val) t.val ∈ sourceS L H
          rw [hgy]
          exact hy)
    · simpa only [Subgroup.map_subtype_centralizer_singleton (T : Subgroup G) t] using hEV
  obtain ⟨hQne,hQZ⟩ := d.linear_outer_centralizer_characteristic h hH hp F hm hF he hmax t ht.1 ht.2
  let Q := center E ⊓ _root_.commutator E
  have hcentral (z : G) (hz : z ∈ Q.map E.subtype) (hz1 : z ≠ 1) :
      centralizer ({z} : Set G) ≤ D := by
    have hzZ := hQZ hz
    have hz2 : orderOf z=2 := orderOf_eq_prime
      ((d.linear_involution_geometry h hH hp F hm hF he hmax).2.2.2.1 z
        (by rwa [←centerIn_eq_map_center])) hz1
    have hh := d.linear_centralizer_le_inter h hH hp F hm hF he hmax z hz2 hzZ
    rwa [←d.linear_common_normalizer_eq h hH hp F hm hF he hmax] at hh
  have hEp : IsPGroup 2 E := T.isPGroup'.to_le inf_le_left
  obtain ⟨R,hR⟩ := (hEp.comap_subtype (K := C)).exists_le_sylow
  have hER : E ≤ (R : Subgroup C).map C.subtype := by
    rw [←map_subgroupOf_eq_of_le (show E ≤ C from inf_le_right)]
    exact map_mono hR
  have hRE : (R : Subgroup C).map C.subtype=E :=
    prime_overgroup_eq_of_characteristic_centralizers E D C Q hQne hcentral hmaxlocal
      _ (R.isPGroup'.map C.subtype) hER (map_subtype_le _)
  obtain ⟨z,hz,hz2,hzT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hconj := d.linear_involutions_isConj h hH hp F hm hF he hmax t.val z
    ((orderOf_coe t).trans ht.1) hz2
  have hc : Nat.card C = Nat.card (centralizer ({z} : Set G)) :=
    card_centralizer_eq_of_isConj _ _ hconj
  have hRT : Nat.card R=Nat.card T := by
    calc
      Nat.card R = Nat.card (T.subtype hzT) := by
        rw [R.card_eq_multiplicity,(T.subtype hzT).card_eq_multiplicity,hc]
      _ = Nat.card T := Nat.card_congr (subgroupOfEquivOfLe hzT).toEquiv
  have hET : E=(T : Subgroup G) := eq_of_le_of_card_ge inf_le_left (by
    rw [←hRE,card_map_of_injective C.subtype_injective,hRT])
  have htZ : t.val ∈ centralizer (centerIn (sourceS L H) : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp
      (show x ∈ C from (show E ≤ C from inf_le_right)
        (hET.symm ▸ sourceS_le_sylow h.sylow_normalizes hH.1.1.2 hx.1))
  apply ht.2
  have hh : t.val ∈ (T : Subgroup G) ⊓ centralizer (centerIn (sourceS L H) : Set G) :=
    ⟨t.property,htZ⟩
  rwa [d.linear_sylow_center_centralizer h hH hp F hm hF he hmax] at hh

/-- Both original pairs generate G, for every original n>1 and both orientations. -/
theorem Preparation.linear_ambient_generation :
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      L ⊔ residual H = ⊤ :=
  d.linear_ambient_generation_of_sourceS_eq_sylow h hH hp F hm hF he hmax
    (d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax)

/-- The individual involution-centralizer core is the original ambient Sylow. -/
theorem Preparation.linear_centralizer_core_eq_sourceS
    (z : G) (hz : orderOf z=2) (hzS : z ∈ centerIn (sourceS L H)) :
    (centralizer ({z} : Set G)).pCoreIn 2 = sourceS L H :=
  d.linear_centralizer_core_eq_sourceS_of_sourceS_eq_sylow h hH hp F hm hF he hmax
    (d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax) z hz hzS

/-- The actual normalizer of T is the whole full-normalizer overlap. -/
theorem Preparation.linear_sylow_normalizer_eq_inter :
    normalizer (T : Set G) = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  change normalizer ((T : Subgroup G) : Set G) = _
  rw [←d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax]
  exact d.linear_common_normalizer_eq h hH hp F hm hF he hmax

/-- Distinct ambient conjugates of the central line are disjoint at every original degree. -/
theorem Preparation.linear_center_TI (g : G) :
    (centerIn (sourceS L H)).map (MulAut.conj g).toMonoidHom = centerIn (sourceS L H) ∨
      Disjoint (centerIn (sourceS L H)) ((centerIn (sourceS L H)).map (MulAut.conj g).toMonoidHom) := by
  let Z := centerIn (sourceS L H)
  by_cases hd : Disjoint Z (Z.map (MulAut.conj g).toMonoidHom)
  · exact Or.inr hd
  left
  have hne : Z ⊓ Z.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun hh => hd (disjoint_iff.mpr hh)
  obtain ⟨x,hx1⟩ := ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y,hy,hgy⟩ := x.property.2
  have hxne : (x:G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
  have hyne : y ≠ 1 := by intro hh; simp [hh] at hgy; exact hxne hgy.symm
  have hexp := (d.linear_involution_geometry h hH hp F hm hF he hmax).2.2.2.1
  have hx2 : orderOf (x:G) = 2 := orderOf_eq_prime
    (hexp x (by rw [←centerIn_eq_map_center]; exact x.property.1)) hxne
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (hexp y (by rw [←centerIn_eq_map_center]; exact hy)) hyne
  have hcx := d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax x hx2 x.property.1
  have hcy := d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax y hy2 hy
  have hcmap : (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({(x:G)} : Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    exact congrArg (fun t : G => centralizer ({t} : Set G)) hgy
  have hs : (sourceS L H).map (MulAut.conj g).toMonoidHom = sourceS L H := by
    calc
      _ = ((centralizer ({y} : Set G)).pCoreIn 2).map (MulAut.conj g).toMonoidHom :=
        congrArg (fun P : Subgroup G => P.map (MulAut.conj g).toMonoidHom) hcy.symm
      _ = (centralizer ({(x:G)} : Set G)).pCoreIn 2 := by
        rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,hcmap]
      _ = sourceS L H := hcx
  rw [centerIn_map_equiv,hs]


/-- The constructed marked extension has a faithful completion in original G.
There is no additional ambient-generation or extension premise. -/
theorem Preparation.linear_ambient_completion :
    let a := d.linearNormalizerMarking h hH hp F hm hF he hmax
    ∃ c : ChapterF.SourceCompletion.LinearThreeEven.Completion a.extension G,
      c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      c.left.range ⊓ c.right.range = c.middle.range :=
  d.linear_prepared_completion_input h hH hp F hm hF he hmax
    (d.linear_ambient_generation h hH hp F hm hF he hmax).1

/-- Completion recognition with the actual source cube witness still explicit.
Full-normalizer realization and original ambient generation are discharged. -/
theorem Preparation.linear_ambient_recognition_of_cube
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    m=n ∧ 1<m ∧ ClassicalGroup.IsPSL G 3 (2^n) ∧ Nonempty (G ≃* PSL(3,F)) := by
  let a := d.linearNormalizerMarking h hH hp F hm hF he hmax
  exact d.linear_full_normalizer_recognition h hH hp F hm hF he a.extension a.fullComparison
    (d.linear_ambient_generation h hH hp F hm hF he hmax).1
    s t hs ht hsout htout hs2 ht2 hcube

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
