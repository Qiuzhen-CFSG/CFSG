module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.SpecificGroups.PGL2.OuterInvolutionCentralizer
public import GorensteinWalter.PGL2PerfectSubnormal
public import Theory.GroupTheory.SemisimpleCentralizerImage
public import Theory.GroupTheory.SpecificGroups.OddDihedralAction
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The escaping outer involution in the prime PGL₂ source branch

The literal quotient of H by O₂(H) is faithful on its centerless normal
component. Its image is the canonical PSL₂ subgroup of prime PGL₂, and the
actual relative centralizer of an outer involution is odd dihedral.

For the marked central-core involution t, source 2.5.18 makes K normal in
C_G(t). If the escaping involution u is conjugate to z, its centralizer has
characteristic two. Applying 1.1.3(2) to t and then 1.1.3(1) to C_K(u)
contradicts the trivial two-core of the nontrivial odd-dihedral group.
The selected-eight producer supplies u in the final core-order-two branch;
this theorem retains that original element and assumes no core order.

Source: Aschbacher--Smith 2.5.21, printed p.565, outer-involution paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels Overcomponents
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
  {p : ℕ} [Fact p.Prime]

private theorem source_conjugate_centralizer_mem_He
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (u : G) (huz : IsConj z u) : centralizer ({u} : Set G) ∈ Chapter1.He G := by
  have hM : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (hG.evenCharacteristic c.T M c.maximal c.sylow_le)
  have hs := c.localSetup hG structural115Input localC129Input_knownSimple
  have hzM : z ∈ M := c.sylow_le (c.sylow_lt.le hs.mem_sylow)
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using c.involution)
  have hzHe : centralizer ({z} : Set G) ∈ Chapter1.He G := by
    have hh := pCoreIn_selfCentralizing_centralizer hM hp (zpowers_le.mpr hzM)
    change M ⊓ centralizer (zpowers z : Set G) ∈ Chapter1.He G at hh
    simpa only [zpowers_eq_closure, centralizer_closure,
      inf_eq_right.mpr hs.centralizer_le] using hh
  obtain ⟨g, hg⟩ := isConj_iff.mp huz
  have he : MulAut.conj g z = u := hg
  have hc := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z)).mp
      (Chapter1.mem_He_iff.mp hzHe)
  rw [he] at hc
  exact Chapter1.mem_He_iff.mpr hc

/-- The source component maps faithfully onto the canonical PSL₂ subgroup of
its original prime PGL₂ quotient. -/
theorem MathieuSourceSetup.prime_pgl_component_image
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hp : 7 ≤ p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (f : H →* GorensteinWalter.PGL2 (ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 H) :
    Disjoint (K.subgroupOf H) f.ker ∧
      (K.subgroupOf H).map f =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range := by
  let F := ZMod p
  let D := K.subgroupOf H
  let eD : D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (subgroupOfEquivOfLe c.component_le).trans eK
  let : IsQuasisimple D := c.component.2
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  let : IsSimpleGroup D := eD.isSimpleGroup
  have hC : centralizer (D : Set H) = f.ker := by
    rw [hk, ← MulAut.conjNormal_ker_eq_centralizer]
    exact MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  have hd : Disjoint D f.ker := by
    apply disjoint_def.mpr
    intro d hdD hdC
    have hz : (⟨d, hdD⟩ : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro a
      rw [← hC] at hdC
      exact Subtype.ext (hdC a a.property)
    let e : D ≃* K := subgroupOfEquivOfLe c.component_le
    have he := (centerCongr e ⟨⟨d, hdD⟩, hz⟩).property
    change e ⟨d, hdD⟩ ∈ center K at he
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen, mem_bot] at he
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)
  have hfi : Function.Injective (f.subgroupMap D) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro d hdg
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hd d.property (congrArg Subtype.val hdg)
  have hne : D.map f ≠ ⊥ := by
    intro he
    obtain ⟨d, hd1⟩ := exists_ne (1 : D)
    apply hd1
    apply hfi
    apply Subtype.ext
    have hh := mem_map_of_mem f d.property
    rw [he, mem_bot] at hh
    exact hh.trans (map_one f).symm
  let : Group.IsPerfect (D.map f) := Group.IsPerfect.map f
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    refine ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), by decide, ?_⟩
    simp [F]
  obtain ⟨hbig, himage⟩ := GorensteinWalter.pgl2_perfect_subnormal_eq_commutator
    F hodd (D.map f) hne inferInstance (c.component.1.map hf)
  have hcanonical : D.map f =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    himage.trans (GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd hbig)
  exact ⟨hd, hcanonical⟩

private theorem source_prime_pgl_outer_centralizer_dihedral
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hp : 7 ≤ p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p))
    (u : H) (hu2 : orderOf (u : G) = 2)
    (hout : (u : G) ∉ K ⊔ twoCore H) :
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ Nonempty
      ((K ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) ≃* DihedralGroup n) := by
  let F := (ZMod p)
  let f : H →* GorensteinWalter.PGL2 F :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    rw [show f = eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ eQ.injective, QuotientGroup.ker_mk']
  let D := K.subgroupOf H
  let eD : D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (subgroupOfEquivOfLe c.component_le).trans eK
  let : IsQuasisimple D := c.component.2
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  let : IsSimpleGroup D := eD.isSimpleGroup
  obtain ⟨hd, hcanonical⟩ := MathieuSourceSetup.prime_pgl_component_image
    c hG hempty hgen hp eK f hf hk
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), by decide, by simp [F]⟩
  have hbig : 3 < Nat.card F := by simpa [F] using (show 3 < p by omega)
  have huout : f u ∉ D.map f := by
    intro hu
    have hpre : u ∈ D ⊔ f.ker := by
      rw [← comap_map_eq]
      exact hu
    have hmem := mem_map_of_mem H.subtype hpre
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le, hk] at hmem
    exact hout hmem
  have huout' : f u ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rwa [← hcanonical]
  have hfu : IsInvolution (f u) := by
    refine ⟨fun he => huout (he ▸ (D.map f).one_mem), ?_⟩
    have hu : u ^ 2 = 1 := Subtype.ext (hu2 ▸ pow_orderOf_eq_one (u : G))
    rw [← map_pow, hu, map_one]
  obtain ⟨n, hn, hlarge, ⟨e⟩⟩ := Theory.PGL2.outer_involution_centralizer_dihedral
    F hodd hbig (f u) hfu huout'
  let N : Subgroup H := D ⊓ centralizer ({u} : Set H)
  have hmap : N.map f = (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := F)).range ⊓ centralizer ({f u} : Set (GorensteinWalter.PGL2 F)) := by
    rw [← hcanonical]
    exact SemisimpleCentralizer.map_inf_centralizer
      (Group.IsPerfect.not_isMulCommutative D) D
      (MulEquiv.piUnique (fun _ : PUnit.{1} => D)).symm f u
  have hni : Function.Injective (f.subgroupMap N) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hd a.property.1 (congrArg Subtype.val ha)
  let eN : N ≃* N.map f := MulEquiv.ofBijective (f.subgroupMap N)
    ⟨hni, f.subgroupMap_surjective N⟩
  let eA : (K ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) ≃* N := {
    toFun := fun a => ⟨⟨a, c.component_le a.property.1⟩, a.property.1,
      mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp a.property.2))⟩
    invFun := fun a => ⟨a.val.val, a.property.1,
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property.2))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact ⟨n, hn, hlarge, ⟨eA.trans (eN.trans ((MulEquiv.subgroupCongr hmap).trans e))⟩⟩

/-- The original prime PGL₂ branch has no z-conjugate outside K O₂(H) in the
source Sylow, once the marked central-core involution is fixed. -/
theorem MathieuSourceSetup.prime_pgl_outer_involution_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hp : 7 ≤ p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p))
    (t u : G) (ht : orderOf t = 2) (htQ : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (huY : u ∈ (S : Subgroup H).map H.subtype) (hu2 : orderOf u = 2)
    (hout : u ∉ K ⊔ twoCore H) (huz : IsConj z u) : False := by
  let J := centralizer ({t} : Set G)
  let C := J ⊓ centralizer ({u} : Set G)
  let N := K ⊓ centralizer ({u} : Set G)
  have hHJ : H ≤ J :=
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htQ htZ).1
  have hKJ : K ≤ J := c.component_le.trans hHJ
  have hJN : J ≤ normalizer (K : Set G) :=
    source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htQ htZ
  have huH : u ∈ H := map_subtype_le _ huY
  obtain ⟨n, hn, hlarge, ⟨eN⟩⟩ := source_prime_pgl_outer_centralizer_dihedral
    c hG hempty hgen hp eK eQ ⟨u, huH⟩ hu2 hout
  have hCu : centralizer ({u} : Set G) ∈ Chapter1.He G :=
    source_conjugate_centralizer_mem_He c hG u huz
  have htCu : t ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hHJ huH)).symm
  have htP : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using ht)
  have hC : C ∈ Chapter1.He G := by
    have hh := pCoreIn_selfCentralizing_centralizer hCu htP (zpowers_le.mpr htCu)
    change centralizer ({u} : Set G) ⊓ centralizer (zpowers t : Set G) ∈ Chapter1.He G at hh
    simpa only [zpowers_eq_closure, centralizer_closure, inf_comm] using hh
  have hNC : N ≤ C := inf_le_inf hKJ le_rfl
  have hnormal : (N.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (inf_le_left.trans hJN)
      (inf_le_right.trans (centralizer ({u} : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)
  have hNne : N ≠ ⊥ := by
    intro hN
    have hc := Nat.card_congr eN.toEquiv
    change Nat.card N = Nat.card (DihedralGroup n) at hc
    rw [(Subgroup.eq_bot_iff_card N).mp hN, DihedralGroup.nat_card] at hc
    omega
  have hNHe : N ∈ Chapter1.He G := Chapter1.lemma_1_1_3_1 hC hNne hNC hnormal.isSubnormal
  have hc := Chapter1.mem_He_iff.mp hNHe
  rw [odd_dihedral_twoCore_eq_bot hn (by omega) eN] at hc
  have he : centralizer (↑(⊥ : Subgroup N) : Set N) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup N) ≤ center N from bot_le)
  rw [he] at hc
  have htriv : Subsingleton N := ⟨fun a b =>
    (mem_bot.mp (hc (mem_top a))).trans (mem_bot.mp (hc (mem_top b))).symm⟩
  have hncard : Nat.card N = 1 := by let := htriv; simp
  have hcard := Nat.card_congr eN.toEquiv
  change Nat.card N = Nat.card (DihedralGroup n) at hcard
  rw [hncard, DihedralGroup.nat_card] at hcard
  omega

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
