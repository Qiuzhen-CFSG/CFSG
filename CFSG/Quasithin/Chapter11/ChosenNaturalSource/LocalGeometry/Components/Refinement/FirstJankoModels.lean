module

public import Theory.SpecificGroups.Janko1.Model
public import Theory.SpecificGroups.Janko1.Model.NormalizerCentralizerGeneration
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.Certification.AbelianSylow
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.SpecificGroups.AlternatingFiveInnerNormalizer
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.AutomorphismTowerSimple
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne


/-!
# J₁ generation with the original Sylow normalizer

A perfect subgroup of the concrete J₁ model has trivial two-core: its
abelian Sylow subgroup meets the perfect group's center trivially. For a
Sylow-normalized A₅ subgroup, all Sylow automorphisms are inner. Since the
Sylow has order eight and A₅ has order sixty, their action has a nontrivial
centralizing involution. The join of A₅ with the Sylow is its centralizer,
by the certified centralizer order 120. The concrete centralizer-normalizer
generation theorem therefore gives the whole J₁ model.

For a group KP with K normal and P a two-group, an actual identification
K/O₂(K) ≃ J₁ extends to a surjection KP → J₁: every automorphism of J₁ is
inner and its center is trivial. The normal-supplement kernel theorem
makes the kernel a two-group. Core lifting preserves the original A₅
section, and Sylow-normalizer surjectivity lifts the generation statement.
The final theorem restricts to the original KP inside the ambient group;
no ambient normality of K is asserted.

The first-normalizer source application is in FirstJanko. It uses this
containment to discharge the J₁ row of the component sieve.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004, proof of
11.1.2, printed p.762. The imported matrix model and automorphism
certificates retain their ATLAS attribution and checked constructions.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Janko

private theorem perfect_core (B : Subgroup Janko1.Model) [Group.IsPerfect B] :
    pCore 2 B = ⊥ := by
  let P : Sylow 2 B := default
  let R := (P : Subgroup B).map B.subtype
  let : IsMulCommutative R := Janko1.two_subgroup_isMulCommutative R
    (P.isPGroup'.map B.subtype)
  have hP : IsMulCommutative P := by
    exact ⟨⟨fun x y => Subtype.ext (Subtype.ext (congrArg
      (fun z : R => (z : Janko1.Model))
      (mul_comm (⟨x,mem_map_of_mem B.subtype x.property⟩ : R)
        ⟨y,mem_map_of_mem B.subtype y.property⟩)))⟩⟩
  apply bot_unique
  intro x hx
  have hh := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨Janko1.perfect_subgroup_pCore_two_le_center B hx,
      Group.IsPerfect.mem_commutator⟩,pCore_isPGroup.le_sylow_of_normal P hx⟩
  rwa [commutator_self_eq_bot_iff.mpr hP] at hh

private theorem centralizer_generation (P : Sylow 2 Janko1.Model)
    (a : Janko1.Model) (ha : orderOf a = 2) (haP : a ∈ P) :
    Nat.card (centralizer ({a} : Set Janko1.Model)) = 120 ∧
      centralizer ({a} : Set Janko1.Model) ⊔ normalizer (P : Set Janko1.Model) = ⊤ := by
  obtain ⟨g,hg⟩ := Janko1.involution_fusion_of_card Janko1.card_model a ha
  let e := MulAut.conj g
  have hc : (centralizer ({a} : Set Janko1.Model)).map e.toMonoidHom =
      centralizer ({Janko1.a} : Set Janko1.Model) := by
    ext x
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hh := congrArg e hx
      simpa only [map_mul,e.apply_symm_apply,show e a = Janko1.a from hg] using hh
    · intro hx
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply,show e a = Janko1.a from hg] using hx
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : Janko1.a ∈ Q := hg ▸ mem_map_of_mem e.toMonoidHom haP
  constructor
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,hc,
      Nat.card_congr Janko1.InvolutionCentralizer.productEquiv.toEquiv]
    change Nat.card (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) = 120
    rw [Nat.card_prod,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [Subgroup.map_sup,hc,map_top_of_surjective _ e.surjective]
    have hn : (normalizer (P : Set Janko1.Model)).map e.toMonoidHom =
        normalizer (((P : Subgroup Janko1.Model).map e.toMonoidHom) : Set Janko1.Model) :=
      map_equiv_normalizer_eq (P : Subgroup Janko1.Model) e
    rw [hn]
    change centralizer ({Janko1.a} : Set Janko1.Model) ⊔
      normalizer (Q : Set Janko1.Model) = ⊤
    exact Janko1.centralizer_sup_normalizer_eq_top Q hQ

/-- A Sylow-normalized A₅ subgroup generates J₁ with that Sylow normalizer. -/
theorem five_sup_normalizer (P : Sylow 2 Janko1.Model) (B : Subgroup Janko1.Model)
    (hn : (P : Subgroup Janko1.Model) ≤ normalizer (B : Set Janko1.Model))
    (eB : B ≃* alternatingGroup (Fin 5)) :
    B ⊔ normalizer (P : Set Janko1.Model) = ⊤ := by
  have hcard : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  let α := B.normalizerMonoidHom.comp (inclusion hn)
  have hrange : α.range ≤ MulAut.innerSubgroup B := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨b,hb⟩ := alternatingFive_normalizerAction_inner
      Janko1.two_subgroup_isMulCommutative B eB (inclusion hn x)
    exact ⟨b,hb.symm⟩
  have hne : (P : Subgroup Janko1.Model) ⊓ centralizer (B : Set Janko1.Model) ≠ ⊥ := by
    intro hz
    have hinj : Function.Injective α := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      apply mem_bot.mp
      rw [←hz]
      refine ⟨x.property,?_⟩
      change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
      rwa [normalizerMonoidHom_ker] at hx
    have hd : Nat.card P ∣ Nat.card B := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact (card_dvd_of_le hrange).trans (card_range_dvd MulAut.conj)
    rw [Janko1.SylowTwo.card,hcard] at hd
    norm_num at hd
  obtain ⟨a,ha,hane⟩ := ((P : Subgroup Janko1.Model) ⊓
    centralizer (B : Set Janko1.Model)).bot_or_exists_ne_one.resolve_left hne
  let : IsElementaryAbelian 2 P := Janko1.SylowTwo.elementary P
  have ha2 : orderOf a = 2 := by
    refine orderOf_eq_prime_iff.mpr ⟨?_,hane⟩
    have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 P) (⟨a,ha.1⟩ : P)
    exact congrArg Subtype.val hpow
  obtain ⟨hC,hgen⟩ := centralizer_generation P a ha2 ha.1
  have hBC : B ≤ centralizer ({a} : Set Janko1.Model) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ha.2 b hb)
  have hPC : (P : Subgroup Janko1.Model) ≤ centralizer ({a} : Set Janko1.Model) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun t : P => (t : Janko1.Model)) (mul_comm (⟨x,hx⟩ : P) ⟨a,ha.1⟩))
  have hBC' : B ⊔ (P : Subgroup Janko1.Model) ≤ centralizer ({a} : Set Janko1.Model) :=
    sup_le hBC hPC
  have hlarge : 120 ≤ Nat.card (B ⊔ (P : Subgroup Janko1.Model) : Subgroup Janko1.Model) := by
    have h60 := card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup Janko1.Model) from le_sup_left)
    have h8 := card_dvd_of_le (show (P : Subgroup Janko1.Model) ≤ B ⊔ (P : Subgroup Janko1.Model) from le_sup_right)
    rw [hcard] at h60
    rw [Janko1.SylowTwo.card] at h8
    have hd := Nat.lcm_dvd h60 h8
    norm_num at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have he : B ⊔ (P : Subgroup Janko1.Model) = centralizer ({a} : Set Janko1.Model) :=
    eq_of_le_of_card_ge hBC' (hC.symm ▸ hlarge)
  apply top_unique
  rw [←hgen,←he]
  exact sup_le (sup_le le_sup_left ((P : Subgroup Janko1.Model).le_normalizer.trans le_sup_right)) le_sup_right

/-- The local A₅ quotient suffices: perfectness and the elementary Sylows
kill the original subgroup's two-core. -/
theorem five_section_sup_normalizer (P : Sylow 2 Janko1.Model)
    (B : Subgroup Janko1.Model) [Group.IsPerfect B]
    (hn : (P : Subgroup Janko1.Model) ≤ normalizer (B : Set Janko1.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B ⊔ normalizer (P : Set Janko1.Model) = ⊤ := by
  let e : B ≃* (B ⧸ pCore 2 B) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (perfect_core B).symm)
  exact five_sup_normalizer P B hn (e.trans eB)

private def modelAutEquiv : Janko1.Model ≃* MulAut Janko1.Model :=
  MulEquiv.ofBijective MulAut.conj ⟨MulAut.conj_injective_of_center_eq_bot (by
    rcases (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp h)).elim),
    Janko1.OuterCertificate.aut_inner⟩

/-- The inner conjugation action of a normal J₁ section extends its literal
quotient map to the whole normal two-supplement, with two-group kernel. -/
theorem normal_supplement_projection {G : Type*} [Group G]
    (K P : Subgroup G) [K.Normal] (hP : IsPGroup 2 P) (hgen : K ⊔ P = ⊤)
    (eK : (K ⧸ pCore 2 K) ≃* Janko1.Model) :
    ∃ q : G →* Janko1.Model, Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∀ k : K, q k = eK (QuotientGroup.mk' (pCore 2 K) k) := by
  let a : G →* MulAut Janko1.Model := (MulAut.congr eK).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp MulAut.conjNormal)
  let q := modelAutEquiv.symm.toMonoidHom.comp a
  have he (k : K) : q k = eK (QuotientGroup.mk' (pCore 2 K) k) := by
    apply modelAutEquiv.injective
    change modelAutEquiv (modelAutEquiv.symm (a k)) = _
    rw [modelAutEquiv.apply_symm_apply]
    change a k = MulAut.conj (eK (QuotientGroup.mk' (pCore 2 K) k))
    ext x
    obtain ⟨y,rfl⟩ := eK.surjective x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    change eK (quotientAut (pCore 2 K) (MulAut.conjNormal k)
      (eK.symm (eK (QuotientGroup.mk' (pCore 2 K) y)))) = _
    rw [eK.symm_apply_apply,quotientAut_apply_mk]
    change eK (QuotientGroup.mk' (pCore 2 K) (k*y*k⁻¹)) = _
    simp only [map_mul,map_inv,MulAut.conj_apply]
  have hr : q.comp K.subtype = eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) :=
    MonoidHom.ext he
  refine ⟨q,?_,?_,he⟩
  · intro x
    obtain ⟨y,rfl⟩ := eK.surjective x
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    exact ⟨k,he k⟩
  · apply q.kernel_isPGroup_of_normal_supplement K P hP hgen
    rw [hr,MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup

/-- Generation lifts across a two-group kernel, keeping the original
A₅ section and the original full Sylow normalizer. -/
theorem five_section_sup_normalizer_of_surjective {G : Type*} [Group G] [Finite G]
    (q : G →* Janko1.Model) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 G) (B : Subgroup G) [Group.IsPerfect B]
    (hn : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B ⊔ normalizer (P : Set G) = ⊤ := by
  let A := B.map q
  let r := q.subgroupMap B
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := r) (q.subgroupMap_surjective B)
  have hrk : IsPGroup 2 r.ker := by
    have he : r.ker = q.ker.comap B.subtype := by
      ext x
      change r x = 1 ↔ q x = 1
      exact ⟨congrArg Subtype.val,fun h => Subtype.ext h⟩
    rw [he]
    exact hk.comap_of_injective _ B.subtype_injective
  have hr : r.ker = pCore 2 B := by
    have hc := r.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective B) hrk
    rwa [perfect_core A,MonoidHom.comap_bot] at hc
  let e : B ⧸ pCore 2 B ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hr.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r (q.subgroupMap_surjective B))
  let Q := P.mapSurjective hq
  have hQA : (Q : Subgroup Janko1.Model) ≤ normalizer (A : Set Janko1.Model) :=
    (map_mono hn).trans (B.le_normalizer_map q)
  have hg := five_sup_normalizer Q A hQA (e.symm.trans eB)
  have hm : (B ⊔ normalizer (P : Set G)).map q = ⊤ := by
    rw [Subgroup.map_sup,P.normalizer_map_surjective q hq]
    exact hg
  have hker : q.ker ≤ B ⊔ normalizer (P : Set G) :=
    (hk.le_sylow_of_normal P).trans ((P : Subgroup G).le_normalizer.trans le_sup_right)
  have hh := congrArg (comap q) hm
  rwa [comap_map_eq,sup_eq_left.mpr hker,comap_top] at hh

/-- A normal J₁ section with a full Sylow supplement is generated by its
Sylow-normalized A₅ section and the normalizer of that same Sylow. -/
theorem normal_supplement_generated {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (K B : Subgroup G) [K.Normal] [Group.IsPerfect B]
    (hgen : K ⊔ (P : Subgroup G) = ⊤)
    (eK : (K ⧸ pCore 2 K) ≃* Janko1.Model)
    (hn : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B ⊔ normalizer (P : Set G) = ⊤ := by
  obtain ⟨q,hq,hk,_⟩ := normal_supplement_projection K P P.isPGroup' hgen eK
  exact five_section_sup_normalizer_of_surjective q hq hk P B hn eB


/-- In the original ambient group, the containing J₁ section lies in the
join of the A₅ section with the original Sylow normalizer. -/
theorem containing_le_sup_normalizer {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (K B : Subgroup G) [Group.IsPerfect B]
    (hBK : B ≤ K) (hPK : (P : Subgroup G) ≤ normalizer (K : Set G))
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Janko1.Model)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    K ≤ B ⊔ normalizer (P : Set G) := by
  let J := K ⊔ (P : Subgroup G)
  have hKJ : K ≤ J := le_sup_left
  have hBJ : B ≤ J := hBK.trans hKJ
  let R := P.subtype (show (P : Subgroup G) ≤ J from le_sup_right)
  let C := K.subgroupOf J
  let A := B.subgroupOf J
  let k : C ≃* K := subgroupOfEquivOfLe hKJ
  let b : A ≃* B := subgroupOfEquivOfLe hBJ
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hPK)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  have hgen : C ⊔ (R : Subgroup J) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hKJ (show (P : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hn : (R : Subgroup J) ≤ normalizer (A : Set J) := by
    intro t ht x
    exact hPB ht x
  have hh := normal_supplement_generated R C A hgen
    ((QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK) hn
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eB)
  have hmap := congrArg (map J.subtype) hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,←MonoidHom.range_eq_map,range_subtype] at hmap
  apply hKJ.trans
  rw [←hmap]
  apply sup_le le_sup_left
  have hnormal := (R : Subgroup J).le_normalizer_map J.subtype
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ J from le_sup_right)] at hnormal
  exact hnormal.trans le_sup_right

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Janko
