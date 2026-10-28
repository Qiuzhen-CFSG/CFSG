module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CoreAutomizerSource
public import Theory.GroupTheory.NormalCentralLine
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.DihedralAbelianIndexTwo

/-!
# The original involutions in the nonabelian core branch

Suppose the marked crossed involution misses K. The normal intersection
of the component Sylow and crossed core then misses the Sylow center, so
it is trivial. The factors centralize one another, and the actual source
quotient embeds both faithfully. An abelian subgroup of index two in its
Sylow image makes two nonabelian commuting images impossible. Thus tˣ lies
in K, and the original central lines force tˣ=zK and z=t*zK.

All maps and central marks retain their source meaning. Nonabelianness
of the core and component Sylow are explicit preceding 2.5.21 inputs;
this module does not claim to exclude the abelian core branch.
Source: Aschbacher--Smith 2.5.21, printed p.566.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original central mark crosses into K as soon as both source factors
are nonabelian and the actual Sylow image has an abelian subgroup of index two. -/
theorem MathieuSourceSetup.crossing_mark_mem_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (t : G) (ht : orderOf t = 2)
    (hline : centerIn ((S : Subgroup H).map H.subtype) ⊓ twoCore H = zpowers t)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hnC : ¬ IsMulCommutative (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G))
    (A : Subgroup ((S : Subgroup H).map f)) [IsMulCommutative A] (hi : A.index = 2) :
    x⁻¹ * t * x ∈ K := by
  let Y := (S : Subgroup H).map H.subtype
  let C := twoCore H
  let D := Y ⊓ K
  let X := C.conjBy x⁻¹
  have hYH : Y ≤ H := map_subtype_le _
  have hCY : C ≤ Y := by
    change twoCore H ≤ Y
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_left
  have hYx : Y.conjBy x⁻¹ = Y :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
  have hXY : X ≤ Y := hYx ▸ map_mono hCY
  have hYnC : Y ≤ normalizer (C : Set G) := hYH.trans (le_normalizer_twoCore H)
  have hYnD : Y ≤ normalizer (D : Set G) :=
    (le_inf Y.le_normalizer (hYH.trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))).trans
      inf_normalizer_le_normalizer_inf
  have hYnX : Y ≤ normalizer (X : Set G) := by
    calc
      Y = Y.conjBy x⁻¹ := hYx.symm
      _ ≤ (normalizer (C : Set G)).map (MulAut.conj x⁻¹).toMonoidHom := map_mono hYnC
      _ ≤ normalizer (X : Set G) := le_normalizer_map _
  have hlineX : centerIn Y ⊓ X = zpowers (x⁻¹ * t * x) := by
    have he := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hline
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      centerIn_map_equiv, MonoidHom.map_zpowers] at he
    change centerIn (Y.conjBy x⁻¹) ⊓ X = _ at he
    simpa only [hYx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using he
  have htx : orderOf (x⁻¹ * t * x) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj x⁻¹).orderOf_eq t).trans ht
  have hk : f.ker = C.subgroupOf H := by
    change f.ker = (twoCore H).subgroupOf H
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact hker
  have hdis := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2).1
  have hDK : Disjoint K C := by
    apply disjoint_def.mpr
    intro a haK haC
    have hac : a ∈ centralizer (K : Set G) := by
      change a ∈ twoCore H at haC
      rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at haC
      exact haC.2
    have haz : (⟨a, haK⟩ : K) ∈ center K := by
      exact mem_center_iff.mpr (fun b => Subtype.ext (hac b b.property))
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen, mem_bot] at haz
    exact congrArg Subtype.val haz
  let q : Y →* (S : Subgroup H).map f :=
    (f.comp (inclusion hYH)).codRestrict _ (by
      intro y
      refine ⟨⟨y, hYH y.property⟩, ?_, rfl⟩
      obtain ⟨u, hu, he⟩ := y.property
      exact (show u = (⟨y, hYH y.property⟩ : H) from Subtype.ext he) ▸ hu)
  have hqinj (B : Subgroup G) (hBY : B ≤ Y) (hd : Disjoint B C) :
      Function.Injective (q.comp (inclusion hBY)) := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hb
    have hf : f (⟨b, hYH (hBY b.property)⟩ : H) = 1 := congrArg Subtype.val hb
    have hbC : (b : G) ∈ C := by
      have hh : (⟨b, hYH (hBY b.property)⟩ : H) ∈ f.ker := hf
      rw [hk] at hh
      exact hh
    exact Subtype.ext (disjoint_def.mp hd b.property hbC)
  have hnX : ¬ IsMulCommutative X := by
    intro hh
    let e : C ≃* X := (MulAut.conj x⁻¹).subgroupMap C
    apply hnC
    refine ⟨⟨fun a b => e.injective ?_⟩⟩
    simpa only [map_mul] using hh.is_comm.comm (e a) (e b)
  exact (central_line_mem_of_faithful_nonabelian_images Y D X
    (S.isPGroup'.map H.subtype) inf_le_left hXY hYnD hYnX
    (x⁻¹ * t * x) htx hlineX q
    (hqinj D inf_le_left (hDK.mono inf_le_right le_rfl))
    (hqinj X hXY hdis.symm) hnD hnX A hi).2
/-- Exact original involution identities, retaining the source marks and crossing element. -/
theorem MathieuSourceSetup.nonabelian_crossing_identities
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (t zK : G) (ht : orderOf t = 2) (hk : orderOf zK = 2)
    (hline : centerIn ((S : Subgroup H).map H.subtype) ⊓ twoCore H = zpowers t)
    (hlineK : centerIn ((S : Subgroup H).map H.subtype) ⊓ K = zpowers zK)
    (hfour : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hnC : ¬ IsMulCommutative (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G))
    (A : Subgroup ((S : Subgroup H).map f)) [IsMulCommutative A] (hi : A.index = 2) :
    x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK := by
  have htmark : t ∈ centerIn ((S : Subgroup H).map H.subtype) ⊓ twoCore H :=
    hline.symm ▸ mem_zpowers t
  have htxK := MathieuSourceSetup.crossing_mark_mem_component c hG hempty hgen
    f hker t ht hline x hxT hxS hxN hx2 hnC hnD A hi
  have hcross := (MathieuSourceSetup.source_crossing_on_center c hgen t ht htmark.2 htmark.1 hfour).2
    x hxT hxN hxS
  have htz : z ∈ centerIn ((S : Subgroup H).map H.subtype) := by
    have hzT : z ∈ centerIn (c.T : Subgroup G) := by
      simpa only [centerIn_eq_map_center] using c.mem_center
    exact ⟨c.center_le c.mem_center, fun a ha => hzT.2 a (c.sylow_lt.le ha)⟩
  have htxZ : x⁻¹ * t * x ∈ centerIn ((S : Subgroup H).map H.subtype) :=
    hcross.symm ▸ (centerIn _).mul_mem htmark.1 htz
  have htxline : x⁻¹ * t * x ∈ zpowers zK := hlineK ▸ ⟨htxZ, htxK⟩
  have htxorder : orderOf (x⁻¹ * t * x) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj x⁻¹).orderOf_eq t).trans ht
  have he : x⁻¹ * t * x = zK := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨x⁻¹ * t * x, htxline⟩ : zpowers zK))
      (y := ⟨zK, mem_zpowers zK⟩) (by simpa using htxorder) (by simpa using hk))
  have ht2 : t * t = 1 := by simpa only [pow_two, ht] using pow_orderOf_eq_one t
  have hez : z = t * zK := by
    calc
      z = (t * t) * z := by rw [ht2, one_mul]
      _ = t * zK := by rw [mul_assoc, ← hcross, he]
  refine ⟨he, hez, ?_⟩
  intro heq
  have ht1 : t = 1 := mul_right_cancel (hez.symm.trans (heq.trans (one_mul zK).symm))
  rw [ht1, orderOf_one] at ht
  omega

/-- The original source constructs the marks and the crossing element internally.
Only the preceding nonabelian branch and actual image index remain explicit. -/
theorem MathieuSourceSetup.source_nonabelian_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (hnC : ¬ IsMulCommutative (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G))
    (hA : ∃ A : Subgroup ((S : Subgroup H).map f), IsMulCommutative A ∧ A.index = 2) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  let Y := (S : Subgroup H).map H.subtype
  have hn : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y = K := by
    apply le_antisymm ?_ (le_componentOrbit K Y)
    apply iSup_le
    intro y
    exact (mem_normalizer_iff_map_conj_eq.mp (hn y.property)).le
  obtain ⟨t, zK, ht, hk, htC, hline, hlineK, _, _, hfour, _, hHt, _, hP, _, hfusion⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  change centerIn Y ⊓ componentOrbit K Y = zpowers zK at hlineK
  rw [horbit] at hlineK
  obtain ⟨x, hxT, hxS, hxN, hx2⟩ := exists_outside_normalizer_square_mem Y
    (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  obtain ⟨A, hcomm, hi⟩ := hA
  let := hcomm
  obtain ⟨htx, hz, hne⟩ := MathieuSourceSetup.nonabelian_crossing_identities c hG hempty hgen
    f hker t zK ht hk hline hlineK hfour x hxT hxS hxN hx2 hnC hnD A hi
  have hkK : zK ∈ K := (show zK ∈ centerIn Y ⊓ K from hlineK.symm ▸ mem_zpowers zK).2
  exact ⟨t, zK, x, ht, hk, htC, hkK, hxT, hxS, hxN, hx2, htx, hz, hne, hfusion, hHt, hP⟩

/-- PGL₂ supplies the actual quotient map and its cyclic-index-two Sylow internally. -/
theorem MathieuSourceSetup.pgl_source_nonabelian_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnC : ¬ IsMulCommutative (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G))
    {F : Type*} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 F) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨_, _, ⟨eP⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hodd
    (S.mapSurjective hf)
  exact MathieuSourceSetup.source_nonabelian_crossing c hG hempty hgen hb f hk hnC hnD
    (exists_abelian_index_two_of_dihedral eP)

/-- M₁₀ supplies its actual semidihedral-sixteen Sylow and original core kernel. -/
theorem MathieuSourceSetup.m10_source_nonabelian_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hnC : ¬ IsMulCommutative (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G))
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  exact MathieuSourceSetup.source_nonabelian_crossing c hG hempty hgen hb f hk hnC hnD
    (exists_abelian_index_two_of_semidihedral_sixteen
      (AlternatingSix.M10.sylowTwoEquivSemidihedral (S.mapSurjective hf)))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
