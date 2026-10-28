module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SourceRatio

/-!
# Actual actor kernels and nonfaithful alternatives on the full natural orbit

The literal N_G(L) action on V_M kills precisely O₂(L) on the component.
Its component image is the originally marked full SL₃ group, with the
quotient representative equations preserved. Full three-rank in that image
forces the ambient action kernel to have order prime to three. Hence the
faithful image still has three-rank at most two and its component has rank two.

The centralizer arguments then exclude a moved cyclic group of order three
and every commuting perfect subgroup whose order is divisible by three.
The final component-orbit application retains the exact produced subgroup
and its centralizer containment, as required in D.3.9(2). They do not prove
D.3.9's extraction of those alternatives from a nonfaithful offender, nor
that its non-Suzuki component has order divisible by three. Those source
premises and the remaining multiplicity exclusion belong to
qt-d-1222-natural-preliminary-source; qt-d-1222-natural-local-geometry retains
final chapter assembly. Cubic containment itself is proved here when the
cubic centralizes the component in either of the two literal action images.

Source: Aschbacher--Smith, D.3.9, printed pp.199--201; A.3.20, p.55;
and 11.0.3--4, p.760, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original component has full three-rank in M/O₂(M). -/
theorem sl3_twoCore_component_rank
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    2 ≤ primeRank 3 ((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) := by
  let e := (cComponentTwoCoreQuotientEquiv (component_in_normalizer D S)).symm.trans
    ((relativeComponentQuotientEquiv (L := L)).trans m.groupEquiv)
  rw [primeRank_equiv 3 e]
  apply Matrix.PSL3.SplitPrimeRank.special_rank
  rw [S.field.card_eq]
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mpr heven

/-- A cubic centralizing the original component modulo O₂(M) lies in L. -/
theorem sl3_orderThree_mem_of_centralizes_twoCore_component
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3)
    (hc : QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))) ⟨x,hxM⟩ ∈
      centralizer (((L.subgroupOf (normalizer (L : Set G))).map
        (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) :
        Set ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))))) : x ∈ L := by
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let : K.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hr : primeRank 3 (M ⧸ pCore 2 M) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      ((normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hi : q ⟨x,hxM⟩ ∈ K.map q :=
    CubicCentralizer.cubic_mem_of_centralizes (K.map q)
      (sl3_twoCore_component_rank D S m heven) hr
      (by rw [← map_pow]; exact congrArg q (Subtype.ext (hx ▸ pow_orderOf_eq_one x))) hc
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem q hk K
    ⟨x,hxM⟩ (orderOf_injective M.subtype M.subtype_injective ⟨x,hxM⟩ |>.symm.trans hx) hi

open Representation.BinaryOffender

/-- On the original component, the full-orbit action kills exactly O₂(L). -/
theorem sl3_fullAction_component_kernel
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    ((actionHom (fullModuleConjugation D S)).comp
      (inclusion L.le_normalizer)).ker = pCore 2 L := by
  let := fullModule_elementary D S
  obtain ⟨s,_,σ,hσ,ha,_,_⟩ := fullModule_sl3_component_ratio D S m
  ext l
  change actionHom (fullModuleConjugation D S) (inclusion L.le_normalizer l) = 1 ↔
    l ∈ pCore 2 L
  rw [actionHom_eq_one_iff]
  constructor
  · intro hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply hσ
    apply LinearMap.ext
    intro v
    change σ ((QuotientGroup.mk' (pCore 2 L)) l) v = σ 1 v
    rw [ha,hl,map_one,Module.End.one_apply]
  · intro hl v
    have he : (QuotientGroup.mk' (pCore 2 L)) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [← ha,he,map_one,Module.End.one_apply]

private theorem sl3_component_rank
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) : 2 ≤ primeRank 3 L := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide : Odd 3) (pCore 2 L)
    pCore_isPGroup, primeRank_equiv 3 m.groupEquiv]
  apply Matrix.PSL3.SplitPrimeRank.special_rank
  rw [S.field.card_eq]
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mpr heven

/-- The kernel of the actual full-orbit action is prime to three. This is
proved from the full component centre and ambient three-rank, not assumed. -/
theorem sl3_fullAction_kernel_coprime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    Nat.Coprime 3 (Nat.card (actionHom (fullModuleConjugation D S)).ker) := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let a : K ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let f := actionHom (fullModuleConjugation D S)
  have hk : (f.comp K.subtype).ker = (pCore 2 L).comap a.toMonoidHom := by
    ext k
    change f (k : M) = 1 ↔ a k ∈ pCore 2 L
    change a k ∈ (f.comp (inclusion L.le_normalizer)).ker ↔ _
    rw [sl3_fullAction_component_kernel D S m]
  have hcp : Nat.Coprime 3 (Nat.card (f.comp K.subtype).ker) := by
    rw [hk, comap_equiv_eq_map_symm', card_map_of_injective a.symm.injective]
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  apply CubicNatural.kernel_coprime_of_rank_two f K hcp
  · rw [primeRank_equiv 3 a]
    exact sl3_component_rank D S m heven
  · exact (normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide)

/-- Both rank bounds in the faithful source action, with its actual component
image. These are the ranks needed to exclude D.3.9(2b). -/
theorem sl3_fullAction_rank_pair
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    2 ≤ primeRank 3 ((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) ∧
      primeRank 3 (actionImage ρ) ≤ 2 := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let a : K ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let f := actionHom (fullModuleConjugation D S)
  have hk := sl3_fullAction_kernel_coprime D S m heven
  refine ⟨?_,(primeRank_le_of_surjective_of_coprime 3 f
    (fullModuleConjugation D S).asGroupHom.rangeRestrict_surjective hk).trans
      ((normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide))⟩
  have hk' : Nat.Coprime 3 (Nat.card (f.subgroupMap K).ker) := by
    rw [ker_subgroupMap]
    exact hk.of_dvd_right (card_comap_dvd_of_injective f.ker K.subtype K.subtype_injective)
  rw [← primeRank_eq_of_surjective_of_coprime 3 (f.subgroupMap K)
    (f.subgroupMap_surjective K) hk',primeRank_equiv 3 a]
  exact sl3_component_rank D S m heven

/-- The cubic part of the nonfaithful alternative of D.3.9 is impossible
in the literal faithful full-module action. The produced X and its actor A
are retained, including their original commutator equality. -/
theorem sl3_fullAction_no_moved_cyclicThree
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ X A : Subgroup (actionImage ρ), Nat.card X = 3 →
      X ≤ centralizer (K : Set (actionImage ρ)) →
      A ≤ centralizer (K : Set (actionImage ρ)) → X = ⁅X,A⁆ → False := by
  let := fullModule_elementary D S
  obtain ⟨hK,hr⟩ := sl3_fullAction_rank_pair D S m heven
  dsimp only
  intro X A hcard hX hA hm
  exact CubicCentralizer.no_moved_cyclicThree _ X A hK hr hcard hX hA hm

/-- Cubic containment on D,S if the cubic's actual full-orbit action
centralizes the component image. No multiplicity bound is required. -/
theorem sl3_orderThree_mem_of_fullAction_centralizes_component
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3)
    (hc : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      actionHom ρ ⟨x,hxM⟩ ∈ centralizer
        (((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) :
          Set (actionImage ρ))) : x ∈ L := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let f := actionHom (fullModuleConjugation D S)
  let : K.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨hK,hr⟩ := sl3_fullAction_rank_pair D S m heven
  have hi : f ⟨x,hxM⟩ ∈ K.map f :=
    CubicCentralizer.cubic_mem_of_centralizes _ hK hr
      (by
        rw [← map_pow]
        have he : (⟨x,hxM⟩ : M) ^ 3 = 1 := Subtype.ext (hx ▸ pow_orderOf_eq_one x)
        rw [he,map_one]) hc
  exact Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem f
    (sl3_fullAction_kernel_coprime D S m heven) K ⟨x,hxM⟩
    (orderOf_injective M.subtype M.subtype_injective ⟨x,hxM⟩ |>.symm.trans hx) hi

/-- The literal component image on V_M is the original L/O₂(L), with its
full SL₃ centre. In particular the action kernel has not collapsed that centre. -/
theorem sl3_fullAction_component_marking
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    let f := actionHom (fullModuleConjugation D S)
    ∃ e : ((L.subgroupOf (normalizer (L : Set G))).map f) ≃* SL(3,S.field.Carrier),
      ∀ l : L, e ⟨f (inclusion L.le_normalizer l),
        mem_map_of_mem f (show inclusion L.le_normalizer l ∈
          L.subgroupOf (normalizer (L : Set G)) from l.property)⟩ =
          m.groupEquiv ((QuotientGroup.mk' (pCore 2 L)) l) := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let a : K ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let f := actionHom (fullModuleConjugation D S)
  let j := f.subgroupMap K
  have hj : j.ker = pCore 2 K := by
    have he : j.ker = (pCore 2 L).comap a.toMonoidHom := by
      ext k
      change j k = 1 ↔ a k ∈ pCore 2 L
      have hm : j k = 1 ↔ f (k : M) = 1 := Subtype.ext_iff
      rw [hm]
      change a k ∈ (f.comp (inclusion L.le_normalizer)).ker ↔ _
      rw [sl3_fullAction_component_kernel D S m]
    rw [he,comap_equiv_eq_map_symm',pCore_map_iso]
  let b : (K ⧸ pCore 2 K) ≃* K.map f :=
    QuotientGroup.liftEquiv (pCore 2 K) (f.subgroupMap_surjective K) hj.symm
  let e : K.map f ≃* SL(3,S.field.Carrier) := b.symm.trans
    ((relativeComponentQuotientEquiv (L := L)).trans m.groupEquiv)
  refine ⟨e,?_⟩
  intro l
  let k : K := a.symm l
  have hk : b ((QuotientGroup.mk' (pCore 2 K)) k) = j k := rfl
  change m.groupEquiv (relativeComponentQuotientEquiv
    (b.symm (j k))) = m.groupEquiv ((QuotientGroup.mk' (pCore 2 L)) l)
  rw [← hk,b.symm_apply_apply]
  rfl

/-- The actual component image has centre of order at most three, including
at even degree where the centre is nontrivial. -/
theorem sl3_fullAction_component_center_card
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := fullModule_elementary D S
    Nat.card (center ((L.subgroupOf (normalizer (L : Set G))).map
      (actionHom (fullModuleConjugation D S)))) ≤ 3 := by
  let := fullModule_elementary D S
  obtain ⟨e,_⟩ := sl3_fullAction_component_marking D S m
  rw [Nat.card_congr (centerCongr e).toEquiv]
  exact Nat.le_of_dvd (by decide) (Matrix.SL3.card_center_dvd_three S.field.Carrier)

/-- The nonfaithful D.3.9 actor cannot produce a commuting perfect subgroup
whose order is divisible by three in the actual full-orbit action image. -/
theorem sl3_fullAction_perfect_centralizer_coprime
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ (J : Subgroup (actionImage ρ)) [Group.IsPerfect J],
      J ≤ centralizer (K : Set (actionImage ρ)) → Nat.Coprime 3 (Nat.card J) := by
  let := fullModule_elementary D S
  obtain ⟨hK,hr⟩ := sl3_fullAction_rank_pair D S m heven
  dsimp only
  intro J hJ hc
  exact CubicCentralizer.perfect_centralizer_coprime _ J hK hr
    (sl3_fullAction_component_center_card D S m) hc

/-- Literal D.3.9(2a) application: retain the produced component, its orbit,
and the centralizer containment. A component whose order is divisible by
three cannot occur. Identifying non-Suzuki components as such remains an
input to the D.3.9 extraction, not a replacement for that extraction. -/
theorem sl3_fullAction_no_component_orbit_three
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ (J A : Subgroup (actionImage ρ)), IsComponent (actionImage ρ) J →
      componentOrbit J A ≤ centralizer (K : Set (actionImage ρ)) →
      3 ∣ Nat.card J → False := by
  let := fullModule_elementary D S
  dsimp only
  intro J A hJ hc hd
  obtain ⟨hK,hr⟩ := sl3_fullAction_rank_pair D S m heven
  exact CubicCentralizer.no_component_three _ J hJ hK hr
    (sl3_fullAction_component_center_card D S m) ((le_componentOrbit J A).trans hc) hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
