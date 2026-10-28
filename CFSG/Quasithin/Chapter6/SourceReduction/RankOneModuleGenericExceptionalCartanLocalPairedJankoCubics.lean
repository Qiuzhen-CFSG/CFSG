module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPairedJanko
public import Theory.GroupTheory.Hall.PermutableNormalizerMover

/-!
# Independent cubics and the normalizing exchanger in the paired J₁ row

The original right Hall subgroup injects into Y/O₂(Y). Its image E has
order nine and lies in the product of the two genuine containing J₁
factors. Since each factor has just one factor of three in its order,
E meets each in a cubic subgroup and is their internal direct product.
The centralizer in E of either factor is exactly the opposite cubic;
thus these are independent actions, with the actual multiplication map.

Hall conjugacy in the solvable Cartan--Sylow join produces an element
of the original Sylow image outside the component stabilizer that
normalizes the same cyclic Cartan image D. Every subgroup of D is
characteristic, so its kernels on the two exchanged factors coincide.
No involutory lift or Frobenius-square marking is supplied as a premise.

The original seed reduction and its Chapter 12 consumer retain all earlier
exclusions and both Hall conditions. The seven-part exclusion and the
normalizer lift to the whole original residual remain open; this module
does not claim the paired J₁ exclusion or SourceLocalCartanEscape.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637, especially the
paired J₁ paragraph on p.636 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem janko_pair_cubic (R U E : Subgroup G)
    (hR : Nat.card R = 175560) (hU : Nat.card U = 175560)
    (hcomm : ⁅R,U⁆ = ⊥) (hdis : Disjoint R U)
    (hE : Nat.card E = 9) (hEP : E ≤ R ⊔ U) :
    Nat.card (E ⊓ R : Subgroup G) = 3 := by
  have hUR : U ≤ centralizer (R : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hn : R ⊔ U ≤ normalizer (R : Set G) :=
    sup_le R.le_normalizer (hUR.trans (Subgroup.centralizer_le_normalizer _))
  have hP : Nat.card (R ⊔ U : Subgroup G) = 175560 * 175560 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint R U
      (hUR.trans (Subgroup.centralizer_le_normalizer _)) hdis,hR,hU]
  have hd := Nat.dvd_gcd
    (card_dvd_of_le (show E ⊓ R ≤ E from inf_le_left))
    (card_dvd_of_le (show E ⊓ R ≤ R from inf_le_right))
  rw [hE,hR] at hd
  change Nat.card (E ⊓ R : Subgroup G) ∣ 3 at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hh | hh
  · have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes R E (hEP.trans hn)
    rw [inf_comm,hR,hE,hh,one_mul] at hc
    have hd := card_dvd_of_le (show R ⊔ E ≤ R ⊔ U from sup_le le_sup_left hEP)
    rw [hP,←hc] at hd
    norm_num at hd
  · exact hh

private theorem janko_plane_split (R U E : Subgroup G)
    (a : R ≃* Janko1.Model) (b : U ≃* Janko1.Model)
    (hc : ⁅R,U⁆ = ⊥) (hd : Disjoint R U)
    (hE : Nat.card E = 9) (hEP : E ≤ R ⊔ U) :
    Nat.card (E ⊓ R : Subgroup G) = 3 ∧
    Nat.card (E ⊓ U : Subgroup G) = 3 ∧
    E = (E ⊓ R) ⊔ (E ⊓ U) ∧
    Disjoint (E ⊓ R) (E ⊓ U) := by
  have hR : Nat.card R = 175560 := (Nat.card_congr a.toEquiv).trans Janko1.card_model
  have hU : Nat.card U = 175560 := (Nat.card_congr b.toEquiv).trans Janko1.card_model
  have h1 := janko_pair_cubic R U E hR hU hc hd hE hEP
  have h2 := janko_pair_cubic U R E hU hR (by rwa [commutator_comm]) hd.symm hE
    (by rwa [sup_comm])
  have hdis : Disjoint (E ⊓ R) (E ⊓ U) := hd.mono inf_le_right inf_le_right
  have hnorm : E ⊓ U ≤ normalizer (E ⊓ R : Set G) :=
    ((inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))).trans
      (centralizer_le (show E ⊓ R ≤ R from inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ((E ⊓ R) ⊔ (E ⊓ U) : Subgroup G) = 9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,h1,h2]
  exact ⟨h1,h2,(eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    (by rw [hcard,hE])).symm,hdis⟩

omit [Finite G] in
private theorem simple_center_eq_bot (R : Subgroup G) (a : R ≃* Janko1.Model) :
    center R = ⊥ := by
  let : IsSimpleGroup R := a.isSimpleGroup
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  exact (inferInstance : (center R).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative R (center_eq_top_iff.mp he))

omit [Finite G] in
private theorem split_plane_centralizer (R U E : Subgroup G)
    (a : R ≃* Janko1.Model) (hc : ⁅R,U⁆ = ⊥)
    (hsplit : E = (E ⊓ R) ⊔ (E ⊓ U)) :
    E ⊓ centralizer (R : Set G) = E ⊓ U := by
  have hUR := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hnorm : E ⊓ U ≤ normalizer (E ⊓ R : Set G) :=
    ((inf_le_right.trans hUR).trans (centralizer_le (show E ⊓ R ≤ R from inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · intro x hx
    have hxe : x ∈ ((E ⊓ R : Subgroup G) : Set G) * ((E ⊓ U : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hnorm,←hsplit]
      exact hx.1
    obtain ⟨r,hr,u,hu,rfl⟩ := hxe
    have hrc : r ∈ centralizer (R : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer (R : Set G)).mul_mem hx.2
          ((centralizer (R : Set G)).inv_mem (hUR hu.2))
    have hz : (⟨r,hr.2⟩ : R) ∈ center R := mem_center_iff.mpr fun y =>
      Subtype.ext (hrc y y.property)
    rw [simple_center_eq_bot R a] at hz
    have he : r = 1 := congrArg Subtype.val (mem_bot.mp hz)
    change r * u ∈ E ⊓ U
    rw [he,one_mul]
    exact hu
  · exact le_inf inf_le_left (inf_le_right.trans hUR)


/-- The two actual Hall cubics and the kernels of their actions on the
original J₁ quotient factors. -/
@[expose] def PairedJankoHallPlane (T : Sylow 2 G) (B Y : Subgroup G) (C : Subgroup Y) : Prop :=
  ∃ t : Y, (t : G) ∈ (T : Subgroup G) ∧
    let q := QuotientGroup.mk' (pCore 2 Y)
    let R := C.map q
    let U := R.conjBy (q t)
    let E := (B.subgroupOf Y).map q
    Nonempty (R ≃* Janko1.Model) ∧ Nonempty (U ≃* Janko1.Model) ∧
    U.conjBy (q t) = R ∧
    Nat.card E = 9 ∧ Nat.card (E ⊓ R : Subgroup _) = 3 ∧
    Nat.card (E ⊓ U : Subgroup _) = 3 ∧ E = (E ⊓ R) ⊔ (E ⊓ U) ∧
    Disjoint (E ⊓ R) (E ⊓ U) ∧
    E ⊓ centralizer (R : Set _) = E ⊓ U ∧
    E ⊓ centralizer (U : Set _) = E ⊓ R ∧
    ∃ e : (E ⊓ R : Subgroup _) × (E ⊓ U : Subgroup _) ≃* E,
      ∀ x y, (e (x,y) : Y ⧸ pCore 2 Y) = (x : Y ⧸ pCore 2 Y) * y

/-- In the original nonnormal J₁ branch, the prescribed Hall plane is
faithful on the pair and splits into its two independent factor cubics. -/
theorem nonnormal_janko_hall_plane
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : ¬ C.Normal)
    (hKC : K ≤ C.map Y.subtype) (a : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    PairedJankoHallPlane T B Y C := by
  have hmoved := nonnormal_container_seed_moved h.qtke hKH hH.1.1.2 hKL hY C hC hKC hCn
  have hlin := moved_seed_linear_four_of_escape h.qtke hKL hKT horbit hmoved hY hescape
  obtain ⟨hB,hBc⟩ := moved_seed_right_hall_plane h hH hgen c hKH hK hqs hKT horbit hmoved hlin
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hi := (nonnormal_container_models h.qtke hKH hH.1.1.2 hKL horbit
    hY hescape C hC hKC hCn).1
  obtain ⟨t,ht,hcomp,⟨aR⟩,⟨aU⟩,hdis,hcomm,hout,hswap,e,he⟩ :=
    nonnormal_janko_quotient_pair hTY C hC hi a
  let q := QuotientGroup.mk' (pCore 2 Y)
  let R := C.map q
  let U := R.conjBy (q t)
  let E := (B.subgroupOf Y).map q
  let O := componentOrbit C ((T : Subgroup G).subgroupOf Y)
  have hO : O.map q = R ⊔ U := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨r,u⟩,hxru⟩ := e.surjective ⟨x,hx⟩
      have heq : x = (r : Y ⧸ pCore 2 Y) * u :=
        (congrArg Subtype.val hxru).symm.trans (he r u)
      rw [heq]
      exact mul_mem_sup r.property u.property
    · apply sup_le
      · intro r hr
        have hval := he ⟨r,hr⟩ 1
        simpa only [OneMemClass.coe_one,mul_one,hval] using (e (⟨r,hr⟩,1)).property
      · intro u hu
        have hval := he 1 ⟨u,hu⟩
        simpa only [OneMemClass.coe_one,one_mul,hval] using (e (1,⟨u,hu⟩)).property
  have hBO : B ≤ O.map Y.subtype := by
    apply (Global.right_cartan_le_residual c).trans
    dsimp only [O]
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hTY,←horbit]
    exact iSup_mono fun _ => map_mono hKC
  have hBOY : B.subgroupOf Y ≤ O := by
    apply (map_le_map_iff_of_injective Y.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hBY]
    exact hBO
  have hEP : E ≤ R ⊔ U := (map_mono (f := q) hBOY).trans_eq hO
  have hE : Nat.card E = 9 := by
    let := hB
    have hd : Disjoint (pCore 2 Y) (B.subgroupOf Y) :=
      IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
        (IsElementaryAbelian.isPGroup 3 B).comap_subtype
    have hq : Function.Injective (q.comp (B.subgroupOf Y).subtype) := by
      apply (q.comp (B.subgroupOf Y).subtype).ker_eq_bot_iff.mp
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      apply eq_bot_iff.mpr
      intro x hx
      exact Subtype.ext (disjoint_def.mp hd hx x.property)
    rw [show E = (q.comp (B.subgroupOf Y).subtype).range by
      rw [MonoidHom.range_comp,range_subtype]]
    rw [←Nat.card_congr (MonoidHom.ofInjective hq).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv]
    exact hBc
  obtain ⟨h1,h2,hsplit,hd⟩ := janko_plane_split R U E aR aU hcomm hdis hE hEP
  have hc : E ⊓ R ≤ centralizer (E ⊓ U : Set _) :=
    (inf_le_right.trans (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (centralizer_le (show E ⊓ U ≤ U from inf_le_right))
  obtain ⟨f,hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (E ⊓ R) (E ⊓ U) hd hc
  exact ⟨t,ht,⟨aR⟩,⟨aU⟩,hswap,hE,h1,h2,hsplit,hd,
    split_plane_centralizer R U E aR hcomm hsplit,
    split_plane_centralizer U R E aU (by rwa [commutator_comm]) (by rwa [sup_comm]),
    f.trans (MulEquiv.subgroupCongr hsplit.symm),hf⟩

/-- The same cyclic Cartan image has equal kernels on the two exchanged
J₁ factors; the exchanger comes from the original Sylow. -/
@[expose] def PairedJankoCartanExchange (T : Sylow 2 G)
    (A Y : Subgroup G) (C : Subgroup Y) : Prop :=
    ∃ t : Y, (t : G) ∈ (T : Subgroup G) ∧
      let q := QuotientGroup.mk' (pCore 2 Y)
      q t ∉ normalizer (C.map q : Set (Y ⧸ pCore 2 Y)) ∧
      q t ∈ normalizer ((A.subgroupOf Y).map q : Set (Y ⧸ pCore 2 Y)) ∧
      (A.subgroupOf Y).map q ⊓ centralizer (C.map q : Set (Y ⧸ pCore 2 Y)) =
        (A.subgroupOf Y).map q ⊓ centralizer ((C.map q).conjBy (q t) : Set (Y ⧸ pCore 2 Y))

/-- The original Cartan image has a normalizing exchanger in the original
Sylow image. No involutory lift or Frobenius-square marking is assumed. -/
theorem nonnormal_janko_cartan_exchanger
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : ¬ C.Normal)
    (hKC : K ≤ C.map Y.subtype) (a : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    PairedJankoCartanExchange T A Y C := by
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let D := (A.subgroupOf Y).map q
  let N := normalizer (C.map q : Set (Y ⧸ pCore 2 Y))
  have haction := nonnormal_janko_action h hH hgen c hKH hK hqs hKT hKL horbit
    hY hescape C hC hCn hKC a
  have hDN : D ≤ N := le_sup_left.trans haction.1
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hi : N.index = 2 := by
    rw [cComponent_normalizer_index_quotient hC]
    exact (nonnormal_container_models h.qtke hKH hH.1.1.2 hKL horbit
      hY hescape C hC hKC hCn).1
  let : N.Normal := N.normal_of_index_eq_two hi
  have hout : ¬ (P : Subgroup _) ≤ N := by
    intro hp
    have hd := index_dvd_of_le hp
    rw [hi] at hd
    exact P.not_dvd_index hd
  obtain ⟨s,hs,hsN⟩ := SetLike.not_le_iff_exists.mp hout
  have hoddD : Odd (Nat.card D) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have hoAY : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact hoAY.of_dvd_nat (card_map_dvd _ q)
  let : Group.IsSolvable (D ⊔ (P : Subgroup _) : Subgroup _) :=
    h.cartan_sylow_action_isSolvable c hTY q
  obtain ⟨u,hu,huN,huD⟩ := OddHall.permutable_normalizer_mover P D N hoddD hDN
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q) s hs hsN
  obtain ⟨t,ht,rfl⟩ := hu
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let i : A.subgroupOf Y →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hii : Function.Injective i := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hh))
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective i hii
  let : IsCyclic D := isCyclic_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  exact ⟨t,ht,huN,huD,cyclic_conjugate_centralizers_eq D (C.map q) (q t) huD⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
open Chapter1.Section02.LocalModels
/-- The original seed reduction retains all earlier exclusions and constructs
the independent Hall cubics and a Cartan-normalizing exchanger in the nonnormal branch. -/
theorem localCartan_escape_seed_pairedJankoCubics_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
          PairedJankoAction T A B Y C ∧ PairedJankoPlacement T Y C ∧
          LocalSieve.PairedJankoHallPlane T B Y C ∧ LocalSieve.PairedJankoCartanExchange T A Y C)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hcase⟩ :=
    localCartan_escape_seed_pairedJanko_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,?_⟩
  by_cases hCn : C.Normal
  · exact Or.inl hCn
  obtain ⟨hi,hKlt,hlin,hB,hBc,⟨e⟩,ha,hp⟩ := hcase.resolve_left hCn
  exact Or.inr ⟨hi,hKlt,hlin,hB,hBc,⟨e⟩,ha,hp,
    LocalSieve.nonnormal_janko_hall_plane h hH hgen c hKH hK hqs hKT hKL hR hY hescape C hC hCn hKC e,
    LocalSieve.nonnormal_janko_cartan_exchanger h hH hgen c hKH hK hqs hKT hKL hR hY hescape C hC hCn hKC e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
