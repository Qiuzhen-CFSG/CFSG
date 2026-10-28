module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.SelectedEightSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.PrimePGLOuterSource
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.CosetFusionSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EarlyCoreSource
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.QuotientTrivialIntersection
public import Theory.GroupTheory.DihedralInnerFourConjugacyPow
/-!
# Excluding an order-two source core in the prime PGL₂ branch

At core order two, the selected largest pair gives an elementary eight F
whose crossing conjugate escapes its original Sylow orbit. If that conjugate
lay in K O₂(H), their quotient four-groups would lie in one index-two subgroup
of a dihedral Sylow of variable order. Dihedral fusion lifts through the
literal core and contradicts escape. Thus the component four has an outer
conjugate involution u. Source component fusion gives u in zᴳ, contradicting
the proved odd-dihedral centralizer calculation for outer involutions.

The core, quotient map, selected pair, crossing and involution remain the
original source objects. Source: Aschbacher--Smith 2.5.21, printed p.565.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
  {p : ℕ} [Fact p.Prime]

private theorem four_of_elementary_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 4) : IsKleinFour A := by
  refine ⟨hcard, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (IsElementaryAbelian.exponent_dvd_p 2 A) with h | h
  · let : Subsingleton A := Monoid.exp_eq_one_iff.mp h
    have hc : Nat.card A = 1 := by simp
    omega
  · exact h

/-- The original prime PGL₂ branch excludes an order-two actual core; the
selected-eight and outer-involution premises are constructed internally. -/
theorem MathieuSourceSetup.prime_pgl_twoCore_card_ne_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hp : 7 ≤ p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p)) :
    Nat.card (twoCore H) ≠ 2 := by
  intro hcard
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), by decide, by simp⟩
  let Y : Subgroup G := (S : Subgroup H).map H.subtype
  let C : Subgroup G := twoCore H
  obtain ⟨U,L,E,_,_,hEY,hE,hFY,hFe,hFc,_,hZF,_,_,_,x,_,_,hxN,_,hescape⟩ :=
    MathieuSourceSetup.selected_eight_of_core_card_two c hG hempty hgen hb hstar hcard
  let F : Subgroup G := E ⊔ C
  let Fx : Subgroup G := F.conjBy x⁻¹
  let : IsElementaryAbelian 2 F := hFe
  have hYH : Y ≤ H := map_subtype_le _
  have hCZY : C ≤ centerIn Y := by
    obtain ⟨t,_,ht,_,htC,hCt,_,_,_,_,_,_,_,_,_,_⟩ :=
      MathieuSourceSetup.source_central_marks c hG hempty hgen hb
    have he : C = zpowers t :=
      (eq_of_le_of_card_ge (zpowers_le.mpr htC) (by
        rw [Nat.card_zpowers, ht, hcard])).symm
    rw [he]
    exact hCt ▸ inf_le_left
  have hFxY : Fx ≤ Y := by
    have hy : Y.conjBy x⁻¹ = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
    exact (map_mono hFY).trans hy.le
  have hCFx : C ≤ Fx := by
    have hy : (centerIn Y).conjBy x⁻¹ = centerIn Y := by
      apply mem_normalizer_iff_map_conj_eq.mp
      exact (normalizer (centerIn Y : Set G)).inv_mem
        (normalizes_centerIn (S := Y) (A := normalizer (Y : Set G)) le_rfl hxN)
    exact hCZY.trans (hy ▸ map_mono hZF)
  let : IsElementaryAbelian 2 Fx := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hFxc : Nat.card Fx = 8 := by
    change Nat.card (F.conjBy x⁻¹) = 8
    rw [conjBy, card_map_of_injective (MulAut.conj x⁻¹).injective, hFc]
  obtain ⟨f,hf,hker⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  have hkerC : f.ker = C.subgroupOf H := by
    rw [hker]
    exact congrArg (fun W : Subgroup G => W.subgroupOf H)
      (MathieuSourceSetup.core_eq_sylow_centralizer c hgen).symm
  let D : Subgroup H := Y.subgroupOf H
  have hDS : D = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hYH]
  let P := S.mapSurjective hf
  have hDP : D.map f = (P : Subgroup (GorensteinWalter.PGL2 (ZMod p))) := by
    rw [hDS]
    rfl
  let A : Subgroup H := F.subgroupOf H
  let B : Subgroup H := Fx.subgroupOf H
  have hFH : F ≤ H := hFY.trans hYH
  have hFxH : Fx ≤ H := hFxY.trans hYH
  have hAD : A ≤ D := fun _ ha => hFY ha
  have hBD : B ≤ D := fun _ ha => hFxY ha
  have hkerA : f.ker ≤ A := by
    rw [hkerC]
    intro a ha
    exact (show C ≤ F from le_sup_right) ha
  have hkerB : f.ker ≤ B := by
    rw [hkerC]
    exact fun _ ha => hCFx ha
  have hcA : Nat.card A = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv).trans hFc
  have hcB : Nat.card B = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFxH).toEquiv).trans hFxc
  have hcKer : Nat.card f.ker = 2 := by
    rw [hkerC, Nat.card_congr (subgroupOfEquivOfLe (hCZY.trans inf_le_left |>.trans hYH)).toEquiv]
    exact hcard
  have image_card (V : Subgroup H) (hKV : f.ker ≤ V) (hV : Nat.card V = 8) :
      Nat.card (V.map f) = 4 := by
    have h := IsElementaryAbelian.card_inf_ker_mul_card_map V f
    rw [inf_eq_right.mpr hKV, hcKer, hV] at h
    omega
  have hcAf : Nat.card (A.map f) = 4 := image_card A hkerA hcA
  have hcBf : Nat.card (B.map f) = 4 := image_card B hkerB hcB
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hFH
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hFxH
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hAf : IsKleinFour (A.map f) := four_of_elementary_card hcAf
  have hBf : IsKleinFour (B.map f) := four_of_elementary_card hcBf
  have hAP : A.map f ≤ (P : Subgroup (GorensteinWalter.PGL2 (ZMod p))) := by
    rw [←hDP]
    exact map_mono hAD
  have hBP : B.map f ≤ (P : Subgroup (GorensteinWalter.PGL2 (ZMod p))) := by
    rw [←hDP]
    exact map_mono hBD
  have hnot : ¬ Fx ≤ K ⊔ C := by
    intro hinner
    let J : Subgroup H := (K ⊔ C).subgroupOf H
    let I := J.map f
    have hker' : f.ker = pCore 2 H := by
      rw [hkerC]
      change (twoCore H).subgroupOf H = pCore 2 H
      rw [twoCore, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    have hcanonical := (MathieuSourceSetup.prime_pgl_component_image
      c hG hempty hgen hp eK f hf hker').2
    have hI : I = (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod p)).range := by
      change ((K ⊔ C).subgroupOf H).map f = _
      rw [subgroupOf_sup c.component_le (hCZY.trans inf_le_left |>.trans hYH),
        Subgroup.map_sup, ← hkerC, map_ker_self, sup_bot_eq]
      exact hcanonical
    have hIi : I.index = 2 := by
      rw [hI]
      exact GorensteinWalter.pgl2_psl2Range_index_eq_two (ZMod p) hodd
    let : I.Normal := normal_of_index_eq_two hIi
    obtain ⟨m, _, ⟨ep⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model
      (ZMod p) hodd P
    have hm : 2 ≤ m := GorensteinWalter.pgl2_dihedral_sylow_parameter_ge_two
      (ZMod p) hodd P ep
    have hPI : ¬ (P : Subgroup (GorensteinWalter.PGL2 (ZMod p))) ≤ I := by
      intro hle
      apply P.not_dvd_index
      simpa only [hIi] using (index_dvd_of_le hle)
    have hsubi : (I.subgroupOf P).index = 2 := I.subgroupOf_index_eq_two P hIi hPI
    have hAfI : A.map f ≤ I := map_mono (fun _ ha =>
      (show E ⊔ C ≤ K ⊔ C from sup_le_sup (hEY.trans inf_le_right) le_rfl) ha)
    have hBfI : B.map f ≤ I := map_mono (fun _ hb => hinner hb)
    obtain ⟨s, hs⟩ := Theory.GroupTheory.dihedral_inner_four_ambient_conjugacy_pow hm
      (P : Subgroup (GorensteinWalter.PGL2 (ZMod p)))
      I (A.map f) (B.map f) ep hsubi hAP hBP hAfI hBfI hAf hBf
    have hsD : (s : GorensteinWalter.PGL2 (ZMod p)) ∈ D.map f := hDP.symm ▸ s.property
    obtain ⟨sH, hsHD, hsImage⟩ := hsD
    have hkerConj : f.ker ≤ A.conjBy sH := by
      have he : f.ker.map (MulAut.conj sH).toMonoidHom = f.ker :=
        Subgroup.Normal.map_conj_eq _ _
      exact he.ge.trans (map_mono hkerA)
    have hmapped : (A.conjBy sH).map f = B.map f := by
      rw [conjBy, Subgroup.image_conjugate, hsImage]
      exact hs
    have hAB : A.conjBy sH = B :=
      Subgroup.map_injective_of_ker_le f hkerConj hkerB hmapped
    have hambient := congrArg (fun V : Subgroup H => V.map H.subtype) hAB
    rw [conjBy, Subgroup.image_conjugate, map_subgroupOf_eq_of_le hFH,
      map_subgroupOf_eq_of_le hFxH] at hambient
    have hsY : (sH : G) ∈ Y := hsHD
    apply hescape (sH⁻¹ : G) (Y.inv_mem hsY)
    change Fx = F.conjBy ((sH : G)⁻¹)⁻¹
    rw [inv_inv, conjBy]
    exact hambient.symm
  have hzK := MathieuSourceSetup.pgl_central_mark_mem_component_of_core_card_two
    c hG hempty hgen hb hcard (ZMod p) hodd eK eQ
  obtain ⟨t,ht,htC,_,_,_,hfusion,_⟩ := MathieuSourceSetup.pgl_order_two_core_fusion
    c hG hempty hgen hb hcard (ZMod p) hodd eK eQ
  have hZinner : centerIn Y ≤ K ⊔ C := by
    obtain ⟨v,_,_,_,hvC,_,_,hspan,_⟩ :=
      MathieuSourceSetup.source_central_marks c hG hempty hgen hb
    rw [hspan]
    exact sup_le (zpowers_le.mpr (mem_sup_right hvC)) (zpowers_le.mpr (mem_sup_left hzK))
  have hCxInner : C.conjBy x⁻¹ ≤ K ⊔ C := by
    have hy : (centerIn Y).conjBy x⁻¹ = centerIn Y := by
      apply mem_normalizer_iff_map_conj_eq.mp
      exact (normalizer (centerIn Y : Set G)).inv_mem
        (normalizes_centerIn (S := Y) (A := normalizer (Y : Set G)) le_rfl hxN)
    exact (map_mono hCZY).trans (hy.le.trans hZinner)
  have hExnot : ¬ E.conjBy x⁻¹ ≤ K ⊔ C := by
    intro he
    apply hnot
    change (E ⊔ C).map (MulAut.conj x⁻¹).toMonoidHom ≤ K ⊔ C
    rw [Subgroup.map_sup]
    exact sup_le he hCxInner
  obtain ⟨u,huEx,huout⟩ := SetLike.not_le_iff_exists.mp hExnot
  obtain ⟨e,heE,heu⟩ := huEx
  have he1 : e ≠ 1 := by
    intro he
    apply huout
    rw [←heu,he,map_one]
    exact (K ⊔ C).one_mem
  let : IsKleinFour E := hE
  have he2 : orderOf e = 2 := by
    have hn : (⟨e,heE⟩ : E) ≠ 1 := fun hh => he1 (congrArg Subtype.val hh)
    have hh : orderOf (⟨e, heE⟩ : E) = 2 := orderOf_eq_prime
      (by simpa only [pow_two] using IsKleinFour.mul_self (⟨e, heE⟩ : E)) hn
    rwa [←orderOf_coe] at hh
  have hu2 : orderOf u = 2 := by rw [←heu]; exact (MulAut.conj x⁻¹).orderOf_eq e |>.trans he2
  have huz : IsConj z u :=
    (hfusion e (hEY heE).2 he2).trans (isConj_iff.mpr ⟨x⁻¹,heu⟩)
  have huY : u ∈ Y := hFxY (map_mono (show E ≤ F from le_sup_left) ⟨e,heE,heu⟩)
  exact MathieuSourceSetup.prime_pgl_outer_involution_false c hG hempty hgen hb hstar
    hp eK eQ t u ht htC (hCZY htC) huY hu2 huout huz

/-- The original prime PGL₂ branch constructs the nonabelian-core crossing,
with the order-two-core exclusion discharged by the selected-eight argument. -/
theorem MathieuSourceSetup.prime_pgl_source_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  exact MathieuSourceSetup.prime_pgl_large_core_crossing c hG hempty hgen hb hp hfm eK eQ
    (MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb
      (MathieuSourceSetup.prime_pgl_twoCore_card_ne_two c hG hempty hgen hb hstar hp eK eQ))

/-- The binary linear component has the prescribed PGL₂(7) automizer,
so its actual two-core also cannot have order two. -/
theorem MathieuSourceSetup.linear_binary_twoCore_card_ne_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* Matrix.PSL3Two.PSL) : Nat.card (twoCore H) ≠ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨eQ⟩ := MathieuSourceSetup.normal_linear_binary_core_quotient c hG hempty hgen eK
  exact MathieuSourceSetup.prime_pgl_twoCore_card_ne_two c hG hempty hgen hb hstar
    (p := 7) (by decide)
    (eK.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)
    (eQ.trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.symm)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
