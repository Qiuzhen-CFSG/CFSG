module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalConjugateCartan
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualActorPair
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow

/-!
# The original linear-three tensor actor is excluded

The original pair has two-group action kernels and local images at the
same full Sylow. A selected SL₃(4) actor therefore supplies the literal
map required by the cubic Cartan calculation; its order makes the local
A₅ image proper. The original opposite Cartan factor centralizes the old
A₅ section, and its normalizer orbit yields the contradiction.

The source consumer retains only the actual Cartan containment and orbit
identity, in addition to the earlier nonzero core and tensor-line inputs.
It handles both the single and repeated natural-module rows of9.3.7.
No model map, local marking or restricted-kernel premise remains.

Source: Aschbacher--Smith9.3.8, printed p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidualActorPair
open ChapterA.Section03 Chapter4
variable {X Y Z : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Group Z] [Finite Z]

omit [Finite X] [Finite Y] [Finite Z] in
theorem marked_restriction_map (q : X →* Y) (J C : Subgroup X) (hCJ : C ≤ J)
    (a : J.map q ≃* Z) :
    (C.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)) =
      ((C.map q).subgroupOf (J.map q)).map a.toMonoidHom := by
  rw [←map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact mem_map.mpr ⟨c,hc,rfl⟩
  · rintro ⟨c,hc,hcx⟩
    exact ⟨⟨c,hCJ hc⟩,hc,Subtype.ext hcx⟩

omit [Finite X] [Finite Y] [Finite Z] in
theorem marked_restriction_kernel (q : X →* Y) (J C : Subgroup X) (hCJ : C ≤ J)
    (a : J.map q ≃* Z) (hk : IsPGroup 2 (q.subgroupMap C).ker) :
    IsPGroup 2 ((a.toMonoidHom.comp (q.subgroupMap J)).subgroupMap (C.subgroupOf J)).ker := by
  let c : C.subgroupOf J ≃* C := subgroupOfEquivOfLe hCJ
  have he : ((a.toMonoidHom.comp (q.subgroupMap J)).subgroupMap (C.subgroupOf J)).ker =
      (q.subgroupMap C).ker.comap c.toMonoidHom := by
    ext x
    constructor
    · intro hx
      have hh : a (q.subgroupMap J x) = 1 := congrArg Subtype.val hx
      exact Subtype.ext (congrArg (fun y : J.map q => (y : Y)) (a.map_eq_one_iff.mp hh))
    · intro hx
      apply Subtype.ext
      change a (q.subgroupMap J x) = 1
      rw [a.map_eq_one_iff]
      exact Subtype.ext (congrArg (fun y : C.map q => (y : Y))
        (show q.subgroupMap C (c x) = 1 from hx))
  rw [he]
  exact hk.comap_of_injective c.toMonoidHom c.injective

omit [Finite Z] in
theorem marked_restriction_local (q : X →* Y) (J C : Subgroup X) (hCJ : C ≤ J)
    (a : J.map q ≃* Z) (R : Sylow 2 J)
    (hC : (C.map q).subgroupOf (J.map q) ∈
      localCComponents (R.mapSurjective (q.subgroupMap_surjective J))) :
    (C.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)) ∈
      localCComponents ((R.mapSurjective (q.subgroupMap_surjective J)).mapSurjective
        (f := a.toMonoidHom) a.surjective) := by
  rw [marked_restriction_map q J C hCJ a]
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hC a.toMonoidHom

omit [Finite X] [Finite Y] [Finite Z] in
/-- The same marking preserves the distinction of the two original images. -/
theorem marked_restriction_distinct (q : X →* Y) (J C B : Subgroup X)
    (hCJ : C ≤ J) (hBJ : B ≤ J) (a : J.map q ≃* Z)
    (hne : C.map q ≠ B.map q) :
    (C.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)) ≠
      (B.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)) := by
  rw [marked_restriction_map q J C hCJ a,marked_restriction_map q J B hBJ a]
  intro he
  apply hne
  have hh := congrArg (map (J.map q).subtype) (map_injective a.injective he)
  simpa only [map_subgroupOf_eq_of_le (map_mono hCJ),
    map_subgroupOf_eq_of_le (map_mono hBJ)] using hh

private theorem seven_not_dvd_local_five (C : Subgroup X)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) : ¬ 7 ∣ Nat.card C := by
  have hc : Nat.card (C ⧸ pCore 2 C) = 60 := by
    rw [Nat.card_congr eC.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 C),hc]
  intro hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with h | h
  · norm_num at h
  · obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hn] at h
    have hh := (by decide : Nat.Prime 7).dvd_of_dvd_pow h
    norm_num at hh

omit [Finite Y] [Finite Z] in
theorem marked_restriction_proper (q : X →* Y) (J C : Subgroup X) (hCJ : C ≤ J)
    (a : J.map q ≃* Z) (h7 : 7 ∣ Nat.card Z)
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    (C.subgroupOf J).map (a.toMonoidHom.comp (q.subgroupMap J)) ≠ ⊤ := by
  intro ht
  have hd := card_dvd_of_surjective
    ((a.toMonoidHom.comp (q.subgroupMap J)).subgroupMap (C.subgroupOf J))
    ((a.toMonoidHom.comp (q.subgroupMap J)).subgroupMap_surjective (C.subgroupOf J))
  rw [ht,card_top,Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv] at hd
  exact seven_not_dvd_local_five C eC (h7.trans hd)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal quotient and actor equivalence supply all map, local and
restricted-kernel inputs to the linear Cartan calculation. -/
theorem linear_factor_centralizes
    (hF : Nat.card F = 4) (q : X →* Y) (J C B E : Subgroup X)
    (hCJ : C ≤ J) (hBJ : B ≤ J) (hEJ : E ≤ J)
    (a : J.map q ≃* SL(3,F)) (R : Sylow 2 J)
    (hC : (C.map q).subgroupOf (J.map q) ∈
      localCComponents (R.mapSurjective (q.subgroupMap_surjective J)))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hkC : IsPGroup 2 (q.subgroupMap C).ker)
    (hkB : IsPGroup 2 (q.subgroupMap B).ker)
    (hEC : E ≤ sectionCentralizer C) (hEB : E ≤ normalizer (B : Set X))
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer B := by
  have h7 : 7 ∣ Nat.card SL(3,F) := by
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
    norm_num
  exact source_tensor_linear_original_chosen_factor hF J C B E hCJ hBJ hEJ
    (a.toMonoidHom.comp (q.subgroupMap J))
    ((R.mapSurjective (q.subgroupMap_surjective J)).mapSurjective
      (f := a.toMonoidHom) a.surjective)
    (marked_restriction_local q J C hCJ a R hC)
    (marked_restriction_proper q J C hCJ a h7 eC) eC
    (marked_restriction_kernel q J C hCJ a hkC) hEC hEB
    (marked_restriction_kernel q J B hBJ a hkB) h3

end CFSG.Quasithin.Chapter10.SourceOldResidualActorPair

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Stellmacher
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03 ChapterE Chapter4
open SourceOldResidualActorPair
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

omit [Finite G] in
private theorem sectionCentralizer_restrict {I C E : Subgroup G}
    (hCI : C ≤ I) (hEI : E ≤ I) (hEC : E ≤ sectionCentralizer C) :
    E.subgroupOf I ≤ sectionCentralizer (C.subgroupOf I) := by
  apply (le_sectionCentralizer_iff _ _).mpr
  obtain ⟨hn,hc⟩ := (le_sectionCentralizer_iff E C).mp hEC
  constructor
  · rw [←subgroupOf_normalizer_eq hCI]
    exact comap_mono hn
  · apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEI,map_subgroupOf_eq_of_le hCI,
      map_pCoreIn_of_injective 2 _ _ I.subtype_injective,map_subgroupOf_eq_of_le hCI]
    exact hc

private theorem cubic_le_twoResidual {X : Type*} [Group X] [Finite X]
    (C : Subgroup X) (hC : IsPGroup 3 C) : C ≤ pResidual 2 X := by
  let q := QuotientGroup.mk' (pResidual 2 X)
  have hp := hC.map q
  have hq := (isPGroup_quotient_pResidual (G := X) 2).to_subgroup (C.map q)
  have hd := hp.disjoint_of_coprime hq (by decide : Nat.Coprime 3 2)
  have he : C.map q = ⊥ := disjoint_self.mp hd
  simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp he

/-- Either selected SL₃(4) action row contradicts the original Cartan orbit.
The quotient map, both local markings and both restricted two-kernels are
constructed from the original tensor overgroup. -/
theorem old_residual_linear_image_false
    (hF : Nat.card F = 4)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (W : Subgroup M₀) [W.Normal] (hUW : m.tensorLine.subgroupOf M₀ ≤ W)
    (A B : Subgroup G) [IsElementaryAbelian 3 A]
    (hAM : A ≤ M₀) (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (horbit : componentOrbit (A ⊓ L.map (MulAut.conj t).toMonoidHom)
      ((T : Subgroup G) ⊓ normalizer (A : Set G)) = A)
    (a : ((pResidual 2 M₀).map (actionMk W)) ≃* SL(3,F)) : False := by
  let K := (pResidual 2 H).map H.subtype
  let E := A ⊓ L.map (MulAut.conj t).toMonoidHom
  let J := pResidual 2 M₀
  let C := L.subgroupOf M₀
  let K₁ := K.subgroupOf M₀
  let E₁ := E.subgroupOf M₀
  have hLM : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hKM : K ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_right
  have hEM : E ≤ M₀ := inf_le_left.trans hAM
  obtain ⟨_,hCJ,hKJ,hkC,hkK,_,_,_,R,_,_,hClocal⟩ :=
    m.old_residual_pair_action_data hH hlarge M₀ hcore hgen hKU W hUW
  let c : C ≃* L := subgroupOfEquivOfLe hLM
  let ec : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  have hE3 : IsPGroup 3 E₁ :=
    ((IsElementaryAbelian.isPGroup 3 A).to_le inf_le_left).comap_subtype
  have hEJ : E₁ ≤ J := cubic_le_twoResidual E₁ hE3
  have hEC : E ≤ sectionCentralizer L :=
    inf_le_right.trans (m.conjugate_factor_le_sectionCentralizer ht htn)
  have hEK : E ≤ normalizer (K : Set G) := inf_le_left.trans hAK
  have hEK₁ : E₁ ≤ normalizer (K₁ : Set M₀) := by
    rw [←subgroupOf_normalizer_eq hKM]
    exact comap_mono hEK
  have hcentral := linear_factor_centralizes hF (actionMk W) J C K₁ E₁
    hCJ hKJ hEJ a R hClocal ec hkC hkK
    (sectionCentralizer_restrict hLM hEM hEC) hEK₁
    (fun x hx => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 3) (x : G) hx.1))
  have hEC' : E ≤ sectionCentralizer K := by
    apply (le_sectionCentralizer_iff E K).mpr
    refine ⟨hEK,?_⟩
    have hm := map_mono (f := M₀.subtype) ((le_sectionCentralizer_iff E₁ K₁).mp hcentral).2
    rwa [map_commutator,map_subgroupOf_eq_of_le hEM,
      map_pCoreIn_of_injective 2 _ _ M₀.subtype_injective,map_subgroupOf_eq_of_le hKM] at hm
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  have hNK : (T : Subgroup G) ⊓ normalizer (A : Set G) ≤ normalizer (K : Set G) :=
    inf_le_left.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  have hBne : B ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hB3
    omega
  obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hBne
  have hb3 : orderOf b = 3 := by
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hB3 ▸ orderOf_dvd_natCard b)).resolve_left (fun h => hb (orderOf_eq_one_iff.mp h))
  exact source_tensor_torus_cubic_contradiction K A E _ eK hNK hEC' horbit
    b (hBA b.property) (hBK b.property) ((Subgroup.orderOf_coe b).trans hb3)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
