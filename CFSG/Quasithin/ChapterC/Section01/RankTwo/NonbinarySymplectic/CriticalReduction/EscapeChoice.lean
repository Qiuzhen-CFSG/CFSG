module
public import Theory.GroupAction.SymplecticSmallTwoSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CriticalGeneration

/-!
# Escaping fixed seeds at arbitrary nonbinary degree

If a bad fixed seed joined with Z_alpha were locally normal, its section
of order at most q² would be centralized by the two-perfect symplectic
component. The primitive-prime bound proves that assertion at every degree.
The genuine critical conjugate-generation theorem and MS93 (2.1)(vii)
then choose an escaping conjugate of the same literal join.

The application uses the characteristic replacement's actual simple
component image, quotient map and full finite-field parameter. It does not
assume that the replacement retains the original odd-index witness.
Source: MS93 (3.4), printed p.868, and Section 7, p.933.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
section Local
variable {M J : Type*} [Group M] [Finite M] [Group J] {R : Subgroup M}

theorem bad_seed_join_not_normalized_of_symplectic (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker)
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n)
    (hS : Nat.card S = Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : (Z R a).relIndex (Y ⊔ Z R a) ≤ Nat.card F ^ 2)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a) :
    ¬ stabilizer R a ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro hnorm
  have ht : color R t = true := by
    have hc := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have haQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _)
  have hdQ : Z R d ≤ Q R d :=
    (geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans (omegaCenter_le _)
  have hDQ : Y ⊔ Z R a ≤ Q R t := sup_le
    ((hY.trans (U_le_Z d)).trans (hdQ.trans (Q_le_adjacent_h R ht hdt)))
    (haQ.trans (Q_le_adjacent_h R ht hat))
  have hQG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hDG := hDQ.trans hQG
  let := finite_stabilizer R a
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let : Finite (Y ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hDQ) (inclusion_injective _)
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer (R := R) a)) (inclusion_injective _)
  let : ((Z R a).subgroupOf (Y ⊔ Z R a)).Normal :=
    normal_subgroupOf_of_le_normalizer (hDG.trans (Z_normalized R a))
  have hperf : IsPPerfect 2 (Ltilde R a) := by
    let e := (pResidual 2 (stabilizer R a)).equivMapOfInjective
      (stabilizer R a).subtype (stabilizer R a).subtype_injective
    exact (isPPerfect_pResidual (G := stabilizer R a) 2).of_surjective
      e.toMonoidHom e.surjective
  have hc := commutator_component_le_of_symplectic_small_section hn hF hS
    (Ltilde R a) (Y ⊔ Z R a) (Z R a) hperf q hq hker (hp.to_le hDQ) hcard
    ((Ltilde_le_stabilizer (R := R) a).trans hnorm)
    ((Ltilde_le_stabilizer (R := R) a).trans (Z_normalized R a))
  exact hbad ((commutator_mono le_sup_left le_rfl).trans hc)

theorem exists_critical_escape_of_bad_symplectic_seed (R : Subgroup M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    (q : M →* J) (hq : Function.Surjective q) (hk : q.ker = pCore 2 M)
    [Finite J] [((pResidual 2 M).map q).Normal]
    [IsSimpleGroup ((pResidual 2 M).map q)] [IsQuasisimple ((pResidual 2 M).map q)]
    (hcent : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n)
    (hS : Nat.card ((pResidual 2 M).map q) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F))
    (geometry : Geometry R) (hb : 0 < geometry.b R) (hC : EdgeCentralizerCondition R)
    {a d t e : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hcrit : CriticalPair R a e (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : Nat.card Y ≤ Nat.card F ^ 2)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a)
    (hYn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ∃ g ∈ stabilizer R a,
      ¬ Z R e ≤ normalizer ((Y ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hQG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hZaQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _)
  have hZdQ : Z R d ≤ Q R d :=
    (geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans (omegaCenter_le _)
  have hYQ : Y ≤ Q R t := (hY.trans (U_le_Z d)).trans (hZdQ.trans (Q_le_adjacent_h R ht hdt))
  have hXQ : Y ⊔ Z R a ≤ Q R t := sup_le hYQ (hZaQ.trans (Q_le_adjacent_h R ht hat))
  have hXG := hXQ.trans hQG
  have hNQ : Q R t ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
    (le_inf hYn (hQG.trans (Z_normalized R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup Y (Z R a))
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨g, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
    · have hh := Q_act R g (beta R)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh,show Q R (hVertex R 1) = R.map (embedM R) from Q_beta R]
      exact (hp.map _).map _
    · cases ha
  obtain ⟨r,hr,hrker⟩ := local_residual_projection R hp hQR q hk ha
  let := finite_stabilizer R d
  let := finite_stabilizer R a
  let : Finite Y := Finite.of_injective
    (inclusion ((hY.trans (U_le_Z d)).trans (Z_le_stabilizer R d))) (inclusion_injective _)
  let : Finite (Z R a) := Finite.of_injective
    (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)
  have hidx : (Z R a).relIndex (Y ⊔ Z R a) ≤ Nat.card F ^ 2 := by
    have hn := (hZaQ.trans (Q_le_adjacent_h R ht hat)).trans hYn
    rw [relIndex_sup_of_normalizes Y (Z R a) hn]
    exact (Nat.le_of_dvd (Nat.card_pos (α := Y)) ((Z R a).relIndex_dvd_card Y)).trans hcard
  have hnotN : ¬ ((Y ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
    intro hnorm
    exact bad_seed_join_not_normalized_of_symplectic geometry hb ha hd hat hdt hQt r hr hrker hn hF hS Y hY hidx hbad
      ((normal_subgroupOf_iff_le_normalizer hXG).mp hnorm)
  have hbe : 0 < criticalDistance R a (geometry.exists_critical a ha) := by
    rwa [geometry.distance_constant a ha]
  have he := critical_endpoint_color R a ha _ hcrit
  have hrev := critical_reverse R geometry hC a ha hbe e he hcrit
  have hgenerate := edge_conjugate_generation_of_centric_component R hp hQR hgen
    q hq hk hcent ha hat (Z R e) (critical_Z_le_stabilizer R geometry a ha hbe hcrit) hrev.2
  obtain ⟨g,hg,hg₁,_⟩ := source_2_1_vii R a e t ha hat (Y ⊔ Z R a) (Y ⊔ Z R a)
    hXQ hXQ (normal_subgroupOf_of_le_normalizer hNQ)
    (normal_subgroupOf_of_le_normalizer hNQ) hnotN hnotN hgenerate
  exact ⟨g,hg,hg₁⟩

end Local
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A bad seed on the actual replacement has an escaping conjugate.
The section bound is the literal full-Sylow bound q², at the original degree. -/
theorem Input.replacement_exists_critical_escape
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {a u t e : Vertex d.radical} (ha : color d.radical a = false)
    (hu : color d.radical u = false)
    (hat : Adjacent d.radical a t) (hut : Adjacent d.radical u t)
    (hcrit : CriticalPair d.radical a e (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam d.radical)) (hYU : Y ≤ U d.radical u)
    (hcard : Nat.card Y ≤ Nat.card F ^ 2)
    (hbad : ¬ ⁅Y,Ltilde d.radical a⁆ ≤ Z d.radical a)
    (hYn : Q d.radical t ≤ normalizer (Y : Set (FreeAmalgam d.radical))) :
    ∃ g ∈ stabilizer d.radical a,
      ¬ Z d.radical e ≤ normalizer
        ((Y ⊔ Z d.radical a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  have hstr := h.replacement_component_image_structure d
  let : ((pResidual 2 d.overgroup).map q).Normal := by
    rw [h.replacement_residual d]
    exact hstr.2.1
  let : IsSimpleGroup ((pResidual 2 d.overgroup).map q) := by
    rw [h.replacement_residual d]
    exact hstr.2.2.1
  let : IsQuasisimple ((pResidual 2 d.overgroup).map q) := by
    rw [h.replacement_residual d]
    exact hstr.2.2.2.1
  have hcent : centralizer ((pResidual 2 d.overgroup).map q : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [h.replacement_residual d]
    exact hstr.2.2.2.2
  have hgen : pResidual 2 d.overgroup ⊔ d.radical = ⊤ := by
    rw [h.replacement_residual d]
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := h.replacement_product d x
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hcardS : Nat.card ((pResidual 2 d.overgroup).map q) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F) := by
    rw [h.replacement_residual d]
    exact h.replacement_component_image_card_sp d
  exact exists_critical_escape_of_bad_symplectic_seed d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) hgen q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent
    (by have := h.nonbinary; omega) h.field_card hcardS geometry hb
    (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
    ha hu hat hut hcrit Y hYU hcard hbad hYn

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
